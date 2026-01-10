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

int main() { // int main(int argc, char *argv[]) {

  {
    uint16_t slog_level_flags = SLOG_FLAGS_ALL;
    slog_init("logfile", slog_level_flags, 1);
  }

  int exit_code = 0;

  char *source_path;
  { // Set source path, kept until exit
    int source_path_length;
    set_source_path(&source_path, &source_path_length);
  }

  Anima animas[ANIMA_COUNT];

  Z3_symbol lang_anima_enum_names[ANIMA_COUNT][ANIMA_COUNT] = {};
  Z3_func_decl lang_anima_enum_consts[ANIMA_COUNT][ANIMA_COUNT] = {};
  Z3_func_decl lang_anima_enum_testers[ANIMA_COUNT][ANIMA_COUNT] = {};

  Z3_symbol lang_persona_enum_names[ANIMA_COUNT] = {};
  Z3_func_decl lang_persona_enum_consts[ANIMA_COUNT] = {};
  Z3_func_decl lang_persona_enum_testers[ANIMA_COUNT] = {};

  AbstractAnima mind_animas[ANIMA_COUNT][ANIMA_COUNT];
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    animas[idx].situation.anima_count = ANIMA_COUNT;
    animas[idx].situation.animas = mind_animas[idx];

    animas[idx].lang = (Lang){
        .anima.enum_names = lang_anima_enum_names[idx],
        .anima.enum_consts = lang_anima_enum_consts[idx],
        .anima.enum_testers = lang_anima_enum_testers[idx],
        .persona.enum_name = lang_persona_enum_names[idx],
        .persona.enum_const = lang_persona_enum_consts[idx],
        .persona.enum_tester = lang_persona_enum_testers[idx],

    };
  }

  AbstractAnima situation_animas[ANIMA_COUNT] = {};
  Situation situation = {
      .anima_count = ANIMA_COUNT,
      .animas = situation_animas,
  };

  Sprite anima_sprites[ANIMA_COUNT];
  Sprites sprites = {
      .anima_count = ANIMA_COUNT,
      .animas = anima_sprites,
  };
  Persona persona;

  RGBMomentum colour = {};

  const Maze maze = setup_maze(source_path);
  { // Setup block
    Pair_uint8 persona_location = {.x = 13, .y = 17};
    setup_situation(&situation, persona_location);

    Persona_default(&persona, &situation);
    Sprite_init(&sprites.persona, 16, persona_location, RENDER_TOP);

    setup_animas(animas, ANIMA_THREADS, &sprites, &maze, ANIMA_COUNT);
  }
  Renderer renderer = {};
  {
    char path_buffer[FILENAME_MAX];

    cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);
    slog_display(SLOG_INFO, 0, "Renderer with sheet from: %s\n", path_buffer);

    Renderer_create(&renderer, maze.size, path_buffer);
  }

  Sync_update_animas(&situation, animas);
  Sync_update_situation(&situation, animas);

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
    goto exit_block;
  }

  // Draw the maze only once...
  Renderer_draw_maze(&renderer, &maze);

  { // core block
    bool core_loop = true;

    uint64_t frame_nanoseconds = 0;
    TimerNano frame_cap_timer = TimerNano_default();

    SDL_Event event;
    SDL_zero(event);

    while (core_loop) {
      TimerNano_start(&frame_cap_timer);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          core_loop = false;
        }
        Anima_handle_event(&animas[0], &event);
        Persona_handle_event(&persona, &maze, &situation, &event);
      }

      { /// Pre-render block
        Sync_update_animas(&situation, animas);
        Sync_update_situation(&situation, animas);
        rgb_momentum_advance(&colour);

        for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
          Anima_on_frame(&animas[id], &sprites.animas[id], &maze, TILE_PIXELS, RENDER_TOP);
        }
        Persona_on_frame(&persona, &sprites.persona, &maze, &situation, TILE_PIXELS, RENDER_TOP);

        for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
          if (atomic_load(&animas[id].contact.flag_suspend)) {
            atomic_store(&animas[id].contact.flag_suspend, false);
            pthread_cond_broadcast(&animas[id].contact.cond_resume);
          }
        }
      }

      { /// Render_block
        SDL_RenderClear(renderer.renderer);

        SDL_SetRenderDrawColor(renderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

        for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
          Renderer_anima(&renderer, &animas[id], &sprites.animas[id], RENDER_DRAW);
        }
        Renderer_persona(&renderer, &persona, &sprites.persona, &situation, RENDER_DRAW);

        Renderer_render_frame_buffer(&renderer);
      }

      { /// Post-render block
        Renderer_persona(&renderer, &persona, &sprites.persona, &situation, RENDER_ERASE);
        for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
          Renderer_anima(&renderer, &animas[id], &sprites.animas[id], RENDER_ERASE);
        }
      }

      { // wait block
        frame_nanoseconds = TimerNano_get_ticks(&frame_cap_timer);
        if (frame_nanoseconds < NS_PER_FRAME) {
          SDL_DelayNS(NS_PER_FRAME - frame_nanoseconds);
        }
      }
    }
  }

exit_block: {
  Renderer_drop(&renderer);
  SDL_Quit();

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    pthread_cancel(ANIMA_THREADS[idx]);
    pthread_join(ANIMA_THREADS[idx], nullptr);
  }

  Maze_drop((Maze *)&maze);
  free(source_path);
  slog_destroy();

  return exit_code;
}
}
