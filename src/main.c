#include "render/palette.h"
#include "render/sheet.h"
#include "setup.h"

#include <glib.h>
#include <stdatomic.h>
#include <stdint.h>

#include "cwalk.h"

#include "constants.h"
#include "generic/pairs.h"
#include "misc.h"
#include "render.h"
#include "render/NSTimer.h"
#include "toys.h"

pthread_t ANIMA_THREADS[ANIMA_COUNT];
pthread_mutex_t MTX_SOLVER = PTHREAD_MUTEX_INITIALIZER;

void update_anima_sprite(Situation *world, uint8_t anima_id) {

  switch (atomic_load(&world->anima[anima_id].status)) {

  case ANIMA_STATUS_SEARCH: {
    /* if (sprite->tick % 15 == 0) { */
    /* sprite_info->surface_offset.x = (sprite_info->surface_offset.x + sprite_info->size.x) % sprite_info->surface.size.x; */
    /* } */
  } break;
  }
}

void World_sync_animas(Situation *world, Anima animas[ANIMA_COUNT]) {
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    atomic_store(&world->anima[idx].location, atomic_load(&animas[idx].mind.view.anima[idx].location));
    atomic_store(&world->anima[idx].status, atomic_load(&animas[idx].mind.view.anima[idx].status));
  }
}

int main() { // int main(int argc, char *argv[]) {

  Situation world = {};

  Anima animas[ANIMA_COUNT];
  Pallete anima_palletes[ANIMA_COUNT];
  Pair_uint32 anima_sprite_location[ANIMA_COUNT] = {};

  Renderer renderer = {};
  rgb_s colour = {};
  Maze maze = {};

  { // Resource setup
    char *source_path;
    setup_source_path(&source_path);
    setup_maze(&maze, source_path);

    { // Renderer
      char path_buffer[FILENAME_MAX];
      cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);

      Renderer_create(&renderer, TILE_PIXELS, maze.size, path_buffer);
    }

    setup_anima(animas, 0, Pair_uint8_create(1, 4));
    anima_palletes[0] = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xffff00ff,
    };

    setup_anima(animas, 1, Pair_uint8_create(16, 26));
    anima_palletes[1] = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xffffbb00,
    };

    setup_anima(animas, 2, Pair_uint8_create(21, 12));
    anima_palletes[2] = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xfa8072ff,
    };

    setup_anima(animas, 3, Pair_uint8_create(4, 29));
    anima_palletes[3] = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xff808080,
    };

    free(source_path);
  }

  { // Sprite setup
    for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
      auto location = atomic_load(&animas[idx].mind.view.anima[idx].location);
      anima_sprite_location[idx] = (Pair_uint32){.x = (location.x * renderer.scale),
                                                 (location.y * renderer.scale)};
    }
  }

  { // Scratch
    g_message("scratch begin...");
    World_sync_animas(&world, animas);
    z3_tmp(&maze, &world);

    g_message("scratch end...");
  }

  int exit_code = 0;

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exit_code = 1;
  } else {

    bool quit = false;

    SDL_Event event;
    Uint64 frameNS;
    NSTimer frameCapTimer = NSTimer_default();

    SDL_zero(event);

    // Draw the maze only once...
    Renderer_read_maze(&renderer, &maze);

    while (!quit) {
      NSTimer_start(&frameCapTimer);

      // Handle events

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handle_event(&animas[0], &event);
      }

      // Pre-render

      World_sync_animas(&world, animas);
      rgbVM_advance(&colour);

      // Render

      SDL_RenderClear(renderer.renderer);

      SDL_SetRenderDrawColor(renderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

      for (uint8_t id = 0; id < ANIMA_COUNT; ++id) {

        Renderer_erase_from_sheet(&renderer,
                                  anima_sprite_location[id],
                                  sheet_data.anima.size,
                                  Sheet_anima_offset(&animas[id]),
                                  anima_palletes[id]);

        Anima_on_frame(&animas[id], &maze, &anima_sprite_location[id]);

        // TODO: Update sprite

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

      frameNS = NSTimer_get_ticks(&frameCapTimer);
      if (frameNS < NS_PER_FRAME) {
        SDL_DelayNS(NS_PER_FRAME - frameNS);
      }
    }
  }

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
