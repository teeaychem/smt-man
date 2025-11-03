#include <pthread.h>
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
#include "sprite.h"
#include "toys.h"

#include "utils/pairs.h"

Renderer gRenderer;

pthread_cond_t cond_resume = PTHREAD_COND_INITIALIZER;

pthread_mutex_t mtx_suspend = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mtx_cvc5 = PTHREAD_MUTEX_INITIALIZER;

bool flag_suspend = true;

pthread_t thread_gottlob;
pthread_t thread_bertrand;

void *spirit(void *_anima) {

  Anima *anima = _anima;
  Mind mind = Mind_default();

  pthread_mutex_lock(&mtx_cvc5);
  Anima_touch(anima, &mind);
  pthread_mutex_unlock(&mtx_cvc5);

  pthread_mutex_lock(&mtx_suspend);
  flag_suspend = true;
  pthread_mutex_unlock(&mtx_suspend);

  while (true) {
    pthread_mutex_lock(&mtx_suspend);
    if (!flag_suspend) {
      Anima_deduct(anima, &mind);
      flag_suspend = true;
      sleep(1);
    }
    pthread_cond_wait(&cond_resume, &mtx_suspend);
    pthread_mutex_unlock(&mtx_suspend);
  }
  return 0;
};

SDL_Window *gWindow = NULL;
char *SOURCE_PATH = NULL;

bool sdl_init(PairI32 dPixels) {
  bool success = false;

  if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    gWindow = SDL_CreateWindow("Hello", dPixels.x * kSCALE, dPixels.y * kSCALE, 0);
    gRenderer = Renderer_create(gWindow, dPixels);

    success = true;
  }

  return success;
}

void sdl_close() {
  SDL_DestroyWindow(gWindow);
  gWindow = NULL;

  SDL_Quit();
}

void setup() {
  // Set the source path for resources, etc.
  size_t wai_length = wai_getExecutablePath(NULL, 0, NULL);
  SOURCE_PATH = (char *)malloc((wai_length + 1));
  int dirname_length;
  wai_getExecutablePath(SOURCE_PATH, wai_length, &dirname_length);
  SOURCE_PATH[dirname_length] = '\0';
}

int main(int argc, char **agrv) {
  struct stumpless_target *target;
  target = stumpless_open_stdout_target("smt-man-log");

  setup();

  /* begin scratch */

  pthread_mutex_lock(&mtx_suspend);
  flag_suspend = true;
  pthread_mutex_unlock(&mtx_suspend);

  /* end scratch */

  // Things are prepared...

  char PATH_BUFFER[FILENAME_MAX];

  cwk_path_join(SOURCE_PATH, "resources/maze/source.txt", PATH_BUFFER, FILENAME_MAX);
  Maze maze = Maze_create(PATH_BUFFER);

  cwk_path_join(SOURCE_PATH, "resources/gottlob.png", PATH_BUFFER, FILENAME_MAX);
  Sprite sprite_gottlob = Sprite_create(PATH_BUFFER);

  Anima gottlob = Anima_default("gottlob", PairI32_create(6, 1), sprite_gottlob);
  pthread_create(&thread_gottlob, NULL, spirit, (void *)&gottlob);

  cwk_path_join(SOURCE_PATH, "resources/bertrand.png", PATH_BUFFER, FILENAME_MAX);
  Sprite sprite_bertrand = Sprite_create(PATH_BUFFER);

  Anima bertrand = Anima_default("bertrand", PairI32_create(10, 1), sprite_bertrand);
  pthread_create(&thread_bertrand, NULL, spirit, (void *)&bertrand);

  pthread_mutex_lock(&mtx_suspend);
  flag_suspend = false;
  pthread_mutex_unlock(&mtx_suspend);
  pthread_cond_broadcast(&cond_resume);

  /* Anima bertrand = Anima_default("bertrand", PairI32_create(10, 1), sprite_bertrand); */
  /* Anima_touch(&bertrand); */

  // Things happen...

  int exitCode = 0;

  rgbVM colour;

  /* sleep(2); */
  /* exit(1); */

  if (!sdl_init(kPIXELS)) {
    exitCode = 1;
  } else {

    bool quit = false;

    NSTimer frameCapTimer = NSTimer_default();

    SDL_Event event;
    SDL_zero(event);

    // Draw the maze only once...
    for (int32_t y = 0; y < maze.size.y; ++y) {
      for (int32_t x = 0; x < maze.size.x; ++x) {
        if (Maze_tile_at(&maze, PairI32_create(x, y)) != '#') {
          Renderer_fill_tile(&gRenderer, PairI32_create(x * kTILE, y * kTILE), 0xffffffff);
        }
      }
    }

    while (!quit) {

      NSTimer_start(&frameCapTimer);

      if (flag_suspend) {
        pthread_mutex_lock(&mtx_suspend);
        flag_suspend = false;
        pthread_mutex_unlock(&mtx_suspend);
        pthread_cond_broadcast(&cond_resume);
        /* pthread_cond_signal(&cond_resume); */
      }

      SDL_RenderClear(gRenderer.renderer);

      /* Renderer_fillTile(&gRenderer, gottlob.sprite.pos, 0x000000ff); */

      rgbVM_advance(&colour);
      SDL_SetRenderDrawColor(gRenderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handle_event(&gottlob, &event);
        Anima_handle_event(&bertrand, &event);
      }

      /* Anima_deduct(&bertrand); */

      Anima_move_within(&gottlob, &maze);
      Anima_move_within(&bertrand, &maze);

      Renderer_draw_sprite(&gRenderer, &gottlob.sprite);
      Renderer_draw_sprite(&gRenderer, &bertrand.sprite);

      Renderer_update(&gRenderer);
      /* Renderer_project(&gRenderer); */
      SDL_RenderPresent(gRenderer.renderer);
      SDL_Delay(1);

      Uint64 frameNS = NSTimer_get_ticks(&frameCapTimer);
      if (frameNS < kNS_PER_FRAME) {
        SDL_DelayNS(kNS_PER_FRAME - frameNS);
      }
    }
  }

  sdl_close();
  pthread_cancel(thread_gottlob);
  pthread_cancel(thread_bertrand);

  pthread_join(thread_gottlob, NULL);
  pthread_join(thread_bertrand, NULL);

  printf("good-bye\n");

  return exitCode;
}
