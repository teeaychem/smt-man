#include "setup.h"

#include <glib.h>
#include <stdatomic.h>
#include <stdint.h>

#include "constants.h"
#include "generic/pairs.h"
#include "logic/synchronization.h"
#include "lyf/persona.h"
#include "render.h"
#include "render/rgb_momentum.h"
#include "render/timer_nano.h"
#include "temp.h"

pthread_t ANIMA_THREADS[ANIMA_COUNT];

int main() { // int main(int argc, char *argv[]) {
  int exit_code = 0;

  Situation situation = {};

  Anima animas[ANIMA_COUNT];
  Persona persona;

  Renderer renderer = {};
  RGBMomentum colour = {};
  Maze maze = {};

  { // Setup block
    setup_resources(&renderer, &maze);

    {
      situation.persona.direction_actual = DIRECTION_E;
      situation.persona.location = (Pair_uint8){.x = 13, .y = 17};
      situation.persona.movement_pattern = 0x552a552a;
    }

    Persona_default(&persona, &situation, 16);
    setup_animas(animas);
  }

  { // Scratch block
    g_message("scratch begin...");
    Sync_situations(&situation, animas);
    z3_tmp(&maze, &situation);
    g_message("scratch end...");
  }

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
    goto exit_block;
  }
  g_log(nullptr, G_LOG_LEVEL_DEBUG, "SDL initialization ok");

  // Draw the maze only once...
  Renderer_read_maze(&renderer, &maze);
  Renderer_write_maze(&renderer, &maze);

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
        Sync_situations(&situation, animas);
        rgb_momentum_advance(&colour);

        for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
          Anima_on_frame(&animas[id], &maze);
        }
        Persona_on_frame(&persona, &maze, &situation);

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
          Renderer_anima(&renderer, animas, id, RENDER_DRAW);
        }
        Renderer_persona(&renderer, &persona, &situation, RENDER_DRAW);

        Renderer_render_frame_buffer(&renderer);
      }

      { /// Post-render block
        Renderer_persona(&renderer, &persona, &situation, RENDER_ERASE);
        for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {
          Renderer_anima(&renderer, animas, id, RENDER_ERASE);
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

  Maze_destroy(&maze);

  g_message("good-bye");

  return exit_code;
}
}
