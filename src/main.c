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
#include "maze.h"

#include "render/NSTimer.h"
#include "render/constants.h"
#include "render/render.h"

#include "surface.h"
#include "toys.h"

#include "utils/pairs.h"

Renderer gRenderer;

pthread_mutex_t mtx_cvc5 = PTHREAD_MUTEX_INITIALIZER;

constexpr size_t kANIMAS = 2;

Anima ANIMAS[kANIMAS];
pthread_t ANIMA_THREADS[kANIMAS];

void *spirit(void *_anima) {

  Anima *anima = _anima;
  Mind mind = Mind_default();

  pthread_mutex_lock(&mtx_cvc5);
  Anima_touch(anima, &mind);
  pthread_mutex_unlock(&mtx_cvc5);

  atomic_store(&anima->flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->mtx_suspend);
    if (!atomic_load(&anima->flag_suspend)) {
      Anima_deduct(anima, &mind);

      sleep(1);
      atomic_store(&anima->flag_suspend, true);
    }
    pthread_cond_wait(&anima->cond_resume, &anima->mtx_suspend);
    pthread_mutex_unlock(&anima->mtx_suspend);
  }
  return 0;
};

SDL_Window *gWindow = NULL;
char *SOURCE_PATH = NULL;

void setup() {
  // Set the source path for resources, etc.
  size_t wai_length = wai_getExecutablePath(NULL, 0, NULL);
  SOURCE_PATH = (char *)malloc((wai_length + 1));
  int dirname_length;
  wai_getExecutablePath(SOURCE_PATH, wai_length, &dirname_length);
  SOURCE_PATH[dirname_length] = '\0';
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
  Surface surface_gottlob = Surface_from_path(PATH_BUFFER);

  ANIMAS[0] = Anima_default("gottlob", PairI32_create(16, 16), surface_gottlob);
  pthread_create(&ANIMA_THREADS[0], NULL, spirit, (void *)&ANIMAS[0]);

  cwk_path_join(SOURCE_PATH, "resources/bertrand.png", PATH_BUFFER, FILENAME_MAX);
  Surface surface_bertrand = Surface_from_path(PATH_BUFFER);

  ANIMAS[1] = Anima_default("bertrand", PairI32_create(32, 16), surface_bertrand);
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
          Renderer_fill_tile(&gRenderer, PairI32_create(x * kSPRITE, y * kSPRITE), 0xffffffff);
        }
      }
    }

    while (!quit) {
      NSTimer_start(&frameCapTimer);

      for (size_t idx = 0; idx < kANIMAS; ++idx) {
        if (atomic_load(&ANIMAS[idx].flag_suspend)) {
          atomic_store(&ANIMAS[idx].flag_suspend, false);
          pthread_cond_broadcast(&ANIMAS[idx].cond_resume);
        }

        Renderer_erase_surface(&gRenderer, &ANIMAS[idx].surface, &ANIMAS[idx].pos);
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

      for (size_t idx = 0; idx < kANIMAS; ++idx) {
        Anima_instinct(&ANIMAS[idx]);
        Anima_move(&ANIMAS[idx], &maze);
        Renderer_draw_surface(&gRenderer, &ANIMAS[idx].surface, &ANIMAS[idx].pos);
      }

      Renderer_update(&gRenderer);

      SDL_RenderPresent(gRenderer.renderer);

      frameNS = NSTimer_get_ticks(&frameCapTimer);
      if (frameNS < kNS_PER_FRAME) {
        SDL_DelayNS(kNS_PER_FRAME - frameNS);
      }
    }
  }

  Renderer_destroy(&gRenderer);
  SDL_Quit();

  for (size_t idx = 0; idx < kANIMAS; ++idx) {
    pthread_cancel(ANIMA_THREADS[idx]);
    pthread_join(ANIMA_THREADS[idx], NULL);
  }

  printf("good-bye\n");

  return exitCode;
}
