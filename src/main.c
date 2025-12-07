#define PAIR_IMPLEMENTATION
#include "pairs.h"
#undef PAIR_IMPLEMENTATION

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
#include "render/sprite.h"

#include "surface.h"
#include "toys.h"

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

void World_sync_animas(SmtWorld *world, Anima animas[ANIMA_COUNT]) {
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    atomic_store(&world->anima[idx].location, atomic_load(&animas[idx].pov.anima[idx].location));
    atomic_store(&world->anima[idx].status, atomic_load(&animas[idx].pov.anima[idx].status));
  }
}

// Setup

Maze setup_maze(char *source_path, char *path_buffer) {
  cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
  return Maze_create(path_buffer);
}

void setup_anima(char *source_path, char *path_buffer, Anima animas[ANIMA_COUNT], SpriteInfo anima_sprites[ANIMA_COUNT], uint8_t id, Pair_uint8 location) {
  animas[id] = Anima_create(id, location, DOWN, DOWN, PAIR_SPRITE_EDGE);

  char path_b[40];

  sprintf(path_b, "resources/%s.png", animas[id].name);

  cwk_path_join(source_path, path_b, path_buffer, FILENAME_MAX);

  anima_sprites[id] = (SpriteInfo){
      .size = PAIR_SPRITE_EDGE,
      .surface = Surface_from_path(path_buffer),
      .surface_offset = Pair_uint32_create(0, 0),
  };
  pthread_create(&ANIMA_THREADS[id], nullptr, spirit, (void *)&animas[id]);
}

int main() { // int main(int argc, char *argv[]) {

  Pair_uint32_create(2, 2);

  SmtWorld world = {};
  Anima animas[ANIMA_COUNT];

  Renderer renderer;
  SpriteInfo anima_sprites[ANIMA_COUNT];

  char *source_path = nullptr;
  char path_buffer[FILENAME_MAX];

  source_path_setup(&source_path);

  // Things are prepared...
  Maze maze = setup_maze(source_path, path_buffer);

  setup_anima(source_path, path_buffer, animas, anima_sprites, 0, Pair_uint8_create(1, 1));
  setup_anima(source_path, path_buffer, animas, anima_sprites, 1, Pair_uint8_create(16, 26));

  g_message("scratch begin...");

  World_sync_animas(&world, animas);
  z3_tmp(&maze, &world);

  g_message("scratch end...");

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
    Renderer_read_maze(&renderer, &maze);

    while (!quit) {
      NSTimer_start(&frameCapTimer);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handle_event(&animas[0], &event);
      }

      World_sync_animas(&world, animas);

      SDL_RenderClear(renderer.renderer);

      for (uint8_t idx = 0; idx < ANIMA_COUNT; ++idx) {
        Renderer_erase_sprite(&renderer, animas[idx].sprite_location, &anima_sprites[idx]);
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

        Renderer_draw_sprite(&renderer, animas[idx].sprite_location, &anima_sprites[idx]);
      }

      Renderer_update(&renderer);

      for (uint8_t idx = 0; idx < ANIMA_COUNT; ++idx) {
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
