#include "setup.h"

#include <glib.h>
#include <stdatomic.h>

#include "render/NSTimer.h"
#include "toys.h"

pthread_t ANIMA_THREADS[ANIMA_COUNT];
pthread_mutex_t MTX_SOLVER = PTHREAD_MUTEX_INITIALIZER;

void update_anima_sprite(SmtWorld *world, uint8_t anima_id, SpriteInfo *sprite_info) {

  switch (atomic_load(&world->anima[anima_id].status)) {

  case ANIMA_STATUS_SEARCH: {
    if (sprite_info->tick % 15 == 0) {
      sprite_info->surface_offset.x = (sprite_info->surface_offset.x + sprite_info->size.x) % sprite_info->surface.size.x;
    }
  } break;
  }
}

void World_sync_animas(SmtWorld *world, Anima animas[ANIMA_COUNT]) {
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    atomic_store(&world->anima[idx].location, atomic_load(&animas[idx].pov.anima[idx].location));
    atomic_store(&world->anima[idx].status, atomic_load(&animas[idx].pov.anima[idx].status));
  }
}

int main() { // int main(int argc, char *argv[]) {

  SmtWorld world = {};
  Anima animas[ANIMA_COUNT];

  Renderer renderer = Renderer_create(PIXEL_DIMENSIONS);

  rgbVM colour;
  Maze maze;

  { // Resource setup
    char *source_path = setup_source_path();
    maze = setup_maze(source_path);

    setup_anima(source_path, animas, &renderer.anima_sprites[0], 0, Pair_uint8_create(1, 1));
    setup_anima(source_path, animas, &renderer.anima_sprites[1], 1, Pair_uint8_create(16, 26));
    free(source_path);
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

        Renderer_erase_sprite(&renderer, animas[id].sprite_location, &renderer.anima_sprites[id]);

        Anima_move(&animas[id], &maze);
        Anima_instinct(&animas[id]);

        update_anima_sprite(&world, id, &renderer.anima_sprites[id]);

        Renderer_draw_sprite(&renderer, animas[id].sprite_location, &renderer.anima_sprites[id]);

        renderer.anima_sprites[id].tick += 1;
        if (atomic_load(&animas[id].sync.flag_suspend)) {
          atomic_store(&animas[id].sync.flag_suspend, false);
          pthread_cond_broadcast(&animas[id].sync.cond_resume);
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
