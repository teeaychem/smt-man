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

constexpr size_t ANIMA_COUNT = 2;

pthread_t ANIMA_THREADS[ANIMA_COUNT];

struct core_logic {
  Anima animas[ANIMA_COUNT];
  Maze maze;
  Persona persona;
  Situation situation;
};
typedef struct core_logic core_logic_s;

struct core_render {
  Renderer renderer;
  Sprites sprites;
};
typedef struct core_render core_render_s;

void core_render_setup(core_render_s *self, const core_logic_s *core_logic, const char *source_path) {
  char path_buffer[FILENAME_MAX];

  cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);
  slog_display(SLOG_INFO, 0, "Renderer with sheet from: %s\n", path_buffer);

  Renderer_create(&self->renderer, core_logic->maze.size, path_buffer);

  { // Sprite block

    // Persona
    Sprite_init(&self->sprites.persona, 16, atomic_load(&core_logic->situation.persona.location), RENDER_TOP);

    // Animas
    for (uint8_t idx = 0; idx < ANIMA_COUNT; ++idx) {
      Sprite_init(&self->sprites.animas[idx], 16, atomic_load(&core_logic->animas[idx].smt.situation.animas.states[idx].location), RENDER_TOP);
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

    { /// Pre-render block
      Sync_update_animas(&logic->situation, logic->animas);
      Sync_update_situation(&logic->situation, logic->animas);
      rgb_momentum_advance(&colour);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        Anima_on_frame(&logic->animas[id], &render->sprites.animas[id], &logic->maze, TILE_PIXELS, RENDER_TOP);
      }
      Persona_on_frame(&logic->persona, &render->sprites.persona, &logic->maze, &logic->situation, TILE_PIXELS, RENDER_TOP);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        if (atomic_load(&logic->animas[id].contact.flag_suspend)) {
          atomic_store(&logic->animas[id].contact.flag_suspend, false);
          pthread_cond_broadcast(&logic->animas[id].contact.cond_resume);
        }
      }
    }

    { /// Render_block
      SDL_RenderClear(render->renderer.renderer);

      SDL_SetRenderDrawColor(render->renderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
        Renderer_anima(&render->renderer, &logic->animas[id], &render->sprites.animas[id], RENDER_DRAW);
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

  core_logic_s core_logic = {
      .maze = setup_maze(source_path),
      .situation.animas = {
          .count = ANIMA_COUNT,
          .states = alloca(ANIMA_COUNT * sizeof(AnimaState)),
      },
  };

  { // Core logic
    for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
      core_logic.animas[idx].smt.situation.animas.count = ANIMA_COUNT;
      core_logic.animas[idx].smt.situation.animas.states = alloca(ANIMA_COUNT * sizeof(AnimaState));
    }

    Pair_uint8 persona_location = {.x = 17, .y = 15};
    setup_situation(&core_logic.situation, persona_location);

    Persona_default(&core_logic.persona, &core_logic.situation);

    setup_animas(core_logic.animas, ANIMA_THREADS, &core_logic.maze, ANIMA_COUNT, source_path);
  }

  core_render_s core_render = {
      .sprites = {.anima_count = ANIMA_COUNT,
                  .animas = alloca(ANIMA_COUNT * sizeof(Sprite))},
  };
  core_render_setup(&core_render, &core_logic, source_path);

  Sync_update_animas(&core_logic.situation, core_logic.animas);
  Sync_update_situation(&core_logic.situation, core_logic.animas);

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
    goto exit_block;
  }

  { // core block
    bool core_loop = true;

    game_state(&core_logic, &core_render);
  }

exit_block: {
  Renderer_drop(&core_render.renderer);
  SDL_Quit();

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    pthread_cancel(ANIMA_THREADS[idx]);
    pthread_join(ANIMA_THREADS[idx], nullptr);
  }

  Maze_drop((Maze *)&core_logic.maze);
  free(source_path);
  slog_destroy();

  return exit_code;
}
}
