#include "setup.h"

#include <slog.h>
#include <stdatomic.h>
#include <stdint.h>

#include "cwalk.h"

#include "SML/logic/synchronization.h"
#include "SML/sprite/persona.h"

#include "generic/pairs.h"
#include "render.h"
#include "render/rgb_momentum.h"
#include "render/sprite.h"
#include "render/timer_nano.h"

constexpr size_t ANIMA_COUNT = 1;

pthread_t ANIMA_THREADS[ANIMA_COUNT];

struct core_logic {
  struct {
    size_t count;
    anima_s *data;
  } animas;
  maze_s maze;
  Persona persona;
  Situation situation;
};
typedef struct core_logic core_logic_s;

void core_logic_ctor(core_logic_s *self, size_t anima_count, const char *source_path) {

  *self = (core_logic_s){
      .animas = {
          .count = anima_count,
          .data = malloc(anima_count * sizeof(*self->animas.data)),
      },
      .maze = {},
  };

  {
    char path_buffer[FILENAME_MAX];
    cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
    maze_ctor_from_path(&self->maze, path_buffer);
  }

  situation_ctor(&self->situation, ANIMA_COUNT);
  situation_reset(&self->situation);

  Persona_ctor(&self->persona, &self->situation);
}

void core_logic_dtor(core_logic_s *self) {
  assert(self != nullptr);
  // TODO
}

struct core_render {
  Renderer renderer;
  Sprites sprites;
};
typedef struct core_render core_render_s;

void core_render_ctor(core_render_s *self, const core_logic_s *core_logic, const char *source_path) {

  *self = (core_render_s){
      .sprites = {
          .anima_count = core_logic->animas.count,
          .animas = malloc(core_logic->animas.count * sizeof(Sprite)),
      },
  };

  char path_buffer[FILENAME_MAX];

  cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);
  slog_display(SLOG_INFO, 0, "Renderer with sheet from: %s\n", path_buffer);

  Renderer_ctor(&self->renderer, core_logic->maze.dimensions, path_buffer);

  { // Sprite block

    // Persona
    Sprite_init(&self->sprites.persona, 16, atomic_load(&core_logic->situation.persona.location), RENDER_TOP);

    // Animas
    for (uint8_t idx = 0; idx < ANIMA_COUNT; ++idx) {
      Sprite_init(&self->sprites.animas[idx], 16, atomic_load(&core_logic->animas.data[idx].smt.situation.animas.data[idx].location), RENDER_TOP);
    }
  }
}

void game_state(core_logic_s *logic, core_render_s *render) {
  SDL_Event event;
  SDL_zero(event);

  bool game_loop = true;

  uint64_t frame_nanoseconds = 0;
  TimerNano frame_cap_timer = TimerNano_default();

  RGBMomentum colour = {};

  situation_reset(&logic->situation);

  for (size_t idx = 0; idx < logic->animas.count; ++idx) {
    sync_situation_to_situation(&logic->situation, &logic->animas.data[idx].smt.situation);
  }

  while (game_loop) {
    TimerNano_start(&frame_cap_timer);

    // Draw the maze only once...
    Renderer_draw_maze(&render->renderer, &logic->maze);

    while (SDL_PollEvent(&event)) {
      if (event.type == SDL_EVENT_QUIT) {
        game_loop = false;
      }

      Persona_handle_event(&logic->persona, &logic->maze, &logic->situation, &event);
    }

    { // logic block
      Sync_update_animas(&logic->situation, logic->animas.data);
      Sync_update_situation(&logic->situation, logic->animas.data);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        pthread_cond_broadcast(&logic->animas.data[id].contact.cond_resume);
      }
    }

    { /// Pre-render block

      rgb_momentum_advance(&colour);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        Anima_on_frame(&logic->animas.data[id], &render->sprites.animas[id], &logic->maze, TILE_PIXELS, RENDER_TOP);
      }
      Persona_on_frame(&logic->persona, &render->sprites.persona, &logic->maze, &logic->situation, TILE_PIXELS, RENDER_TOP);
    }

    { /// Render_block
      SDL_RenderClear(render->renderer.renderer);

      SDL_SetRenderDrawColor(render->renderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        Renderer_anima(&render->renderer, &logic->animas.data[id], &render->sprites.animas[id], RENDER_DRAW);
      }
      Renderer_persona(&render->renderer, &logic->persona, &render->sprites.persona, &logic->situation, RENDER_DRAW);

      Renderer_render_frame_buffer(&render->renderer);
    }

    { /// Post-render block
      Renderer_clear(&render->renderer);
    }

    { // wait block
      frame_nanoseconds = TimerNano_get_ticks(&frame_cap_timer);
      if (frame_nanoseconds < NS_PER_FRAME) {
        SDL_DelayNS(NS_PER_FRAME - frame_nanoseconds);
      }
    }
  }
}

int main() { // int main(int argc, char *argv[]) {

  int exit_code = 0;

  { // slog setup
    uint16_t slog_level_flags = SLOG_DEBUG;
    slog_init("logfile", slog_level_flags, 1);
  }

  char *source_path;
  { // Set source path, static lifetime
    int source_path_length;
    set_source_path(&source_path, &source_path_length);
  }

  core_logic_s core_logic = {};
  core_logic_ctor(&core_logic, ANIMA_COUNT, source_path);

  { // Core logic
    for (uint8_t idx = 0; idx < ANIMA_COUNT; ++idx) {

      spirit_setup_s *setup = malloc(sizeof(*setup));
      // static lifetime, as thread lives until exit
      *setup = (spirit_setup_s){
          .anima = &core_logic.animas.data[idx],
          .anima_count = ANIMA_COUNT,
          .maze = &core_logic.maze,
          .source_path = source_path,
      };

      anima_ctor(&core_logic.animas.data[idx], ANIMA_COUNT, idx, &core_logic.maze);

      pthread_create(&ANIMA_THREADS[setup->anima->id], nullptr, setup_spirit, (void *)setup);
    }

    for (size_t idx = 0; idx < core_logic.animas.count; ++idx) {
      sync_situation_to_situation(&core_logic.situation, &core_logic.animas.data[idx].smt.situation);
    }
  }

  core_render_s core_render = {};
  core_render_ctor(&core_render, &core_logic, source_path);

  /* Sync_update_animas(&core_logic.situation, core_logic.animas.data); */
  /* Sync_update_situation(&core_logic.situation, core_logic.animas.data); */

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
    goto exit_block;
  }

  { // core block
    bool core_loop = true;

    /* while (core_loop) { */
    game_state(&core_logic, &core_render);
    /* } */
  }

exit_block: {
  Renderer_dtor(&core_render.renderer);
  SDL_Quit();

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    pthread_cancel(ANIMA_THREADS[idx]);
    pthread_join(ANIMA_THREADS[idx], nullptr);
  }

  maze_dtor((maze_s *)&core_logic.maze);
  free(source_path);
  slog_destroy();

  return exit_code;
}
}
