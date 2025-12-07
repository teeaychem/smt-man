#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "cwalk.h"
#include <sys/syslog.h>
#include <sys/types.h>
#include <whereami.h>

#include "anima.h"
#include "glib.h"
#include "logic.h"
#include "maze.h"
#include "misc.h"

#include "constants.h"
#include "render/NSTimer.h"
#include "render/render.h"

#include "surface.h"
#include "toys.h"

#include "utils/pairs.h"

pthread_mutex_t MTX_SOLVER = PTHREAD_MUTEX_INITIALIZER;

pthread_t ANIMA_THREADS[ANIMA_COUNT];

void *spirit(void *void_anima) {

  Anima *anima = void_anima;
  Mind mind = Mind_default();

  pthread_mutex_lock(&MTX_SOLVER);
  Anima_touch(anima, &mind);
  pthread_mutex_unlock(&MTX_SOLVER);

  atomic_store(&anima->sync.flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->sync.mtx_suspend);
    if (!atomic_load(&anima->sync.flag_suspend)) {
      Anima_deduct(anima, &mind);

      sleep(1);
      atomic_store(&anima->sync.flag_suspend, true);
    }
    pthread_cond_wait(&anima->sync.cond_resume, &anima->sync.mtx_suspend);
    pthread_mutex_unlock(&anima->sync.mtx_suspend);
  }
  return 0;
}

void source_path_setup(char **source_path) {
  // Set the source path for resources, etc.
  int source_path_size = wai_getExecutablePath(nullptr, 0, nullptr) + 1;
  *source_path = malloc((size_t)source_path_size * sizeof(*source_path));
  int source_path_len;
  wai_getExecutablePath(*source_path, source_path_size - 1, &source_path_len);
  assert(source_path_len < source_path_size);
  *source_path[source_path_len] = '\0';
}

void update_anima_sprite(SmtWorld *world, uint8_t anima_id, SpriteInfo *sprite_info) {

  switch (atomic_load(&world->anima[anima_id].status)) {

  case ANIMA_STATUS_SEARCH: {
    if (sprite_info->tick % 15 == 0) {
      sprite_info->surface_offset.x = (sprite_info->surface_offset.x + sprite_info->size.x) % sprite_info->surface.size.x;
    }
  } break;
  }
}

void World_sync(SmtWorld *world, Anima animas[ANIMA_COUNT]) {
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    atomic_store(&world->anima[idx].location, atomic_load(&animas[idx].pov.anima[idx].location));
    atomic_store(&world->anima[idx].status, atomic_load(&animas[idx].pov.anima[idx].status));
  }
}

void render_maze(Renderer *renderer, Maze *maze) {
  // For each tile...
  for (uint32_t pos_x = 0; pos_x < TILE_COUNTS.x; ++pos_x) {
    for (uint32_t pos_y = 0; pos_y < TILE_COUNTS.y; ++pos_y) {

      bool is_path = Maze_abstract_is_path(maze, pos_x, pos_y);

      for (uint32_t pxl_y = 0; pxl_y < TILE_SCALE; ++pxl_y) {
        uint32_t y_offset = ((pos_y * TILE_SCALE) + pxl_y) * renderer->dimensions.x;
        for (uint32_t pxl_x = 0; pxl_x < TILE_SCALE; ++pxl_x) {
          uint32_t x_offset = pxl_x + (pos_x * TILE_SCALE);

          renderer->frame_buffer[y_offset + x_offset] = is_path ? 0x00000000 : 0xffffffff;
        }
      }
    }
  }
}

int main(int argc, char **argv) {
  SmtWorld world = {};
  Anima animas[ANIMA_COUNT];

  Renderer renderer;
  SpriteInfo anima_sprites[ANIMA_COUNT];

  char *source_path = nullptr;
  char path_buffer[FILENAME_MAX];

  source_path_setup(&source_path);

  // Things are prepared...

  cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
  Maze maze = Maze_create(path_buffer);

  cwk_path_join(source_path, "resources/gottlob.png", path_buffer, FILENAME_MAX);
  anima_sprites[0] = (SpriteInfo){
      .size = PAIR_SPRITE_EDGE,
      .surface = Surface_from_path(path_buffer),
      .surface_offset = PairI32_create(0, 0),
  };
  animas[0] = Anima_create(0, PairI32_create(1, 1), DOWN, DOWN, PAIR_SPRITE_EDGE);
  pthread_create(&ANIMA_THREADS[0], nullptr, spirit, (void *)&animas[0]);

  cwk_path_join(source_path, "resources/bertrand.png", path_buffer, FILENAME_MAX);
  anima_sprites[1] = (SpriteInfo){
      .size = PAIR_SPRITE_EDGE,
      .surface = Surface_from_path(path_buffer),
      .surface_offset = PairI32_create(0, 0),
  };
  animas[1] = Anima_create(1, PairI32_create(10, 26), DOWN, DOWN, PAIR_SPRITE_EDGE);
  pthread_create(&ANIMA_THREADS[1], nullptr, spirit, (void *)&animas[1]);

  /* begin scratch */
  World_sync(&world, animas);
  g_message("scratch begin...");
  z3_tmp(&maze, &world);

  g_message("scratch end...");

  /* end scratch */

  // Things happen...

  int exitCode = 0;

  rgbVM colour;

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exitCode = 1;
  } else {

    renderer = Renderer_create(PIXEL_DIMENSIONS);

    bool quit = false;

    SDL_Event event;
    Uint64 frameNS;
    NSTimer frameCapTimer = NSTimer_default();

    SDL_zero(event);

    // Draw the maze only once...
    render_maze(&renderer, &maze);

    while (!quit) {
      NSTimer_start(&frameCapTimer);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handle_event(&animas[0], &event);
      }

      World_sync(&world, animas);

      SDL_RenderClear(renderer.renderer);

      for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
        Renderer_erase_sprite(&renderer,
                              animas[idx].sprite_location,
                              &anima_sprites[idx]);
      }

      rgbVM_advance(&colour);
      SDL_SetRenderDrawColor(renderer.renderer,
                             colour.state[0].value,
                             colour.state[1].value,
                             colour.state[2].value,
                             0x000000ff);

      for (uint8_t idx = 0; idx < ANIMA_COUNT; ++idx) {
        // Anima_instinct(&ANIMAS[idx]);
        update_anima_sprite(&world, idx, &anima_sprites[idx]);
        Anima_move(&animas[idx], &maze);

        Renderer_draw_sprite(&renderer,
                             animas[idx].sprite_location,
                             &anima_sprites[idx]);
      }

      Renderer_update(&renderer);

      for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
        anima_sprites[idx].tick += 1;

        if (atomic_load(&animas[idx].sync.flag_suspend)) {
          atomic_store(&animas[idx].sync.flag_suspend, false);
          pthread_cond_broadcast(&animas[idx].sync.cond_resume);
        }
      }

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
    Surface_destroy(&anima_sprites[idx].surface);
  }
  Maze_destroy(&maze);

  g_message("good-bye");

  return exitCode;
}
