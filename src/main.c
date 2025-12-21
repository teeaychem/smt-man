#include "setup.h"

#include <glib.h>
#include <stdatomic.h>
#include <stdint.h>

#include "constants.h"
#include "generic/pairs.h"
#include "logic/synchronization.h"
#include "temp.h"
#include "render.h"
#include "render/timer_nano.h"
#include "render/palette.h"
#include "render/rgb_momentum.h"
#include "render/sheet.h"

pthread_t ANIMA_THREADS[ANIMA_COUNT];

constexpr uint32_t FPS = 12;

int main() { // int main(int argc, char *argv[]) {
  int exit_code = 0;

  Situation situation = {};

  Anima animas[ANIMA_COUNT];
  Pallete anima_palletes[ANIMA_COUNT];
  Pair_uint32 anima_sprite_location[ANIMA_COUNT] = {};

  Renderer renderer = {};
  RGBMomentum colour = {};
  Maze maze = {};

  setup_resources(&renderer, &maze, animas, anima_palletes);
  setup_sprites(&renderer, animas, anima_sprite_location);

  { // Scratch block
    g_message("scratch begin...");
    Sync_situation_animas(&situation, animas);
    z3_tmp(&maze, &situation);
    g_message("scratch end...");
  }

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
    goto exit_block;
  }

  bool quit = false;

  SDL_Event event;

  constexpr uint64_t NS_PER_FRAME = 1000000000 / FPS;

  uint64_t frame_nanoseconds = 0;
  TimerNano frame_cap_timer = TimerNano_default();

  SDL_zero(event);

  // Draw the maze only once...
  Renderer_read_maze(&renderer, &maze);

  { // core block
    while (!quit) {
      TimerNano_start(&frame_cap_timer);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handle_event(&animas[0], &event);
      }

      { // pre_render_block
        Sync_situation_animas(&situation, animas);
        rgb_momentum_advance(&colour);
      }

      { // render_block
        SDL_RenderClear(renderer.renderer);

        SDL_SetRenderDrawColor(renderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

        for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {

          Renderer_erase_from_sheet(&renderer,
                                    anima_sprite_location[id],
                                    sheet_data.anima.size,
                                    Sheet_anima_offset(&animas[id]),
                                    anima_palletes[id]);

          Anima_on_frame(&animas[id], &maze, &anima_sprite_location[id]);

          Renderer_draw_from_sheet(&renderer,
                                   anima_sprite_location[id],
                                   sheet_data.anima.size,
                                   Sheet_anima_offset(&animas[id]),
                                   anima_palletes[id]);

          if (atomic_load(&animas[id].contact.flag_suspend)) {
            atomic_store(&animas[id].contact.flag_suspend, false);
            pthread_cond_broadcast(&animas[id].contact.cond_resume);
          }
        }

        Renderer_update(&renderer);
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
  Renderer_destroy(&renderer);
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
