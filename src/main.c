#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <unistd.h>

#include "cwalk.h"
#include <stumpless.h>
#include <sys/syslog.h>
#include <sys/types.h>
#include <whereami.h>

#include "anima.h"
#include "logic.h"
#include "maze.h"

#include "render/NSTimer.h"
#include "render/constants.h"
#include "render/render.h"

#include "surface.h"
#include "toys.h"

#include "utils/pairs.h"

Renderer gRenderer;

pthread_mutex_t mtx_cvc5 = PTHREAD_MUTEX_INITIALIZER;

Anima ANIMAS[ANIMA_COUNT];
SpriteInfo ANIMA_SPRITES[ANIMA_COUNT];
pthread_t ANIMA_THREADS[ANIMA_COUNT];

struct smt_world_t WORLD = {};

void *spirit(void *_anima) {

  Anima *anima = _anima;
  Mind mind = Mind_default();

  pthread_mutex_lock(&mtx_cvc5);
  Anima_touch(anima, &mind);
  pthread_mutex_unlock(&mtx_cvc5);

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
};

SDL_Window *gWindow = NULL;

size_t SOURCE_PATH_SIZE;
char *SOURCE_PATH = NULL;

void setup() {
  // Set the source path for resources, etc.
  SOURCE_PATH_SIZE = wai_getExecutablePath(NULL, 0, NULL) + 1;
  SOURCE_PATH = malloc(SOURCE_PATH_SIZE * sizeof(*SOURCE_PATH));
  int source_path_len;
  wai_getExecutablePath(SOURCE_PATH, SOURCE_PATH_SIZE - 1, &source_path_len);
  SOURCE_PATH[source_path_len] = '\0';
}

void update_anima_sprite(uint8_t anima_id, SpriteInfo *sprite_info) {

  switch (atomic_load(&WORLD.anima[anima_id].status)) {

  case ANIMA_STATUS_SEARCH: {
    if (sprite_info->tick % 15 == 0) {
      sprite_info->surface_offset.x = (sprite_info->surface_offset.x + sprite_info->size.x) % sprite_info->surface.size.x;
    }
  } break;
  }
}

int main(int argc, char **argv) {
  struct stumpless_target *target;
  target = stumpless_open_stdout_target("smt-man-log");

  char PATH_BUFFER[FILENAME_MAX];

  setup();

  /* begin scratch */

  /* end scratch */

  // Things are prepared...

  cwk_path_join(SOURCE_PATH, "resources/maze/source.txt", PATH_BUFFER, FILENAME_MAX);
  Maze maze = Maze_create(PATH_BUFFER);

  cwk_path_join(SOURCE_PATH, "resources/gottlob.png", PATH_BUFFER, FILENAME_MAX);
  ANIMA_SPRITES[0] = (SpriteInfo){
      .size = PAIR_SPRITE_EDGE,
      .surface = Surface_from_path(PATH_BUFFER),
      .surface_offset = PairI32_create(0, 0),
  };
  ANIMAS[0] = Anima_default(0, PairI32_create(16, 16), PAIR_SPRITE_EDGE);
  pthread_create(&ANIMA_THREADS[0], NULL, spirit, (void *)&ANIMAS[0]);

  cwk_path_join(SOURCE_PATH, "resources/bertrand.png", PATH_BUFFER, FILENAME_MAX);
  ANIMA_SPRITES[1] = (SpriteInfo){
      .size = PAIR_SPRITE_EDGE,
      .surface = Surface_from_path(PATH_BUFFER),
      .surface_offset = PairI32_create(0, 0),
  };
  ANIMAS[1] = Anima_default(1, PairI32_create(32, 16), PAIR_SPRITE_EDGE);
  pthread_create(&ANIMA_THREADS[1], NULL, spirit, (void *)&ANIMAS[1]);

  // Things happen...

  int exitCode = 0;

  rgbVM colour;

  if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    exitCode = 1;
  } else {

    gRenderer = Renderer_create();

    bool quit = false;

    SDL_Event event;
    Uint64 frameNS;
    NSTimer frameCapTimer = NSTimer_default();

    SDL_zero(event);

    // Draw the maze only once...
    for (size_t pxl = 0; pxl < PairI32_area(&kPIXELS); ++pxl) {
      if (maze.pixels[pxl] != '#') {
        gRenderer.frameBuffer[pxl] = 0xffffffff;
      }
    }

    for (int32_t y = 0; y < maze.size.y; ++y) {
      for (int32_t x = 0; x < maze.size.x; ++x) {
        if (Maze_at_point(&maze, PairI32_create(x, y)) != '#') {
          Renderer_fill_tile(&gRenderer, PairI32_create(x * SPRITE_EDGE_SIZE, y * SPRITE_EDGE_SIZE), 0xffffffff);
        }
      }
    }

    while (!quit) {
      NSTimer_start(&frameCapTimer);

      for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
        WORLD.anima[idx].location = ANIMAS[idx].pov.anima[idx].location;

        Renderer_erase_sprite(&gRenderer,
                              atomic_load(&ANIMAS[idx].pov.anima[idx].location),
                              &ANIMA_SPRITES[idx]);
      }

      SDL_RenderClear(gRenderer.renderer);

      rgbVM_advance(&colour);
      SDL_SetRenderDrawColor(gRenderer.renderer,
                             colour.state[0].value,
                             colour.state[1].value,
                             colour.state[2].value,
                             0x000000ff);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handle_event(&ANIMAS[0], &event);
      }

      for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
        Anima_instinct(&ANIMAS[idx]);
        update_anima_sprite(idx, &ANIMA_SPRITES[idx]);
        Anima_move(&ANIMAS[idx], &maze);

        Renderer_draw_sprite(&gRenderer,
                             atomic_load(&ANIMAS[idx].pov.anima[idx].location),
                             &ANIMA_SPRITES[idx]);
      }

      Renderer_update(&gRenderer);

      SDL_RenderPresent(gRenderer.renderer);

      for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
        ANIMA_SPRITES[idx].tick += 1;

        if (atomic_load(&ANIMAS[idx].sync.flag_suspend)) {
          atomic_store(&ANIMAS[idx].sync.flag_suspend, false);
          pthread_cond_broadcast(&ANIMAS[idx].sync.cond_resume);
        }
      }

      frameNS = NSTimer_get_ticks(&frameCapTimer);
      if (frameNS < kNS_PER_FRAME) {
        SDL_DelayNS(kNS_PER_FRAME - frameNS);
      }
    }
  }

  Renderer_destroy(&gRenderer);
  SDL_Quit();

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    pthread_cancel(ANIMA_THREADS[idx]);
    pthread_join(ANIMA_THREADS[idx], NULL);
    Surface_destroy(&ANIMA_SPRITES[idx].surface);
  }

  printf("good-bye\n");

  return exitCode;
}
