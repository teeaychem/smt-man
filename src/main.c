#include "cwalk.h"
#include "setup.h"

#include <glib.h>
#include <stdatomic.h>
#include <stdint.h>

#include "constants.h"
#include "generic/pairs.h"
#include "logic/synchronization.h"
#include "render.h"
#include "render/rgb_momentum.h"
#include "render/timer_nano.h"
#include "sprites/persona.h"

pthread_t ANIMA_THREADS[ANIMA_COUNT];

int main() { // int main(int argc, char *argv[]) {
  int exit_code = 0;

  char *source_path;
  { // Set source path, kept until exit
    int source_path_length;
    set_source_path(&source_path, &source_path_length);
  }

  Situation situation = {};

  Anima animas[ANIMA_COUNT];
  Persona persona;

  RGBMomentum colour = {};

  const Maze maze = setup_maze(source_path);
  { // Setup block
    setup_situation(&situation, (Pair_uint8){.x = 13, .y = 17});

    Persona_default(&persona, &situation, 16);

    setup_animas(animas, &maze);
  }
  Renderer renderer = {};
  {
    char path_buffer[FILENAME_MAX];
    cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);
    g_log(nullptr, G_LOG_LEVEL_INFO, "Renderer with sheet from: %s", path_buffer);

    Renderer_create(&renderer, maze.size, path_buffer);
  }

  Sync_update_animas(&situation, animas);
  Sync_update_situation(&situation, animas);

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
    goto exit_block;
  }
  g_log(nullptr, G_LOG_LEVEL_DEBUG, "SDL initialization ok");

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

  Maze_drop((Maze *)&maze);
  free(source_path);

  g_message("good-bye");

  return exit_code;
}
}
