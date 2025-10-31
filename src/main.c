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
#include "sprite.h"
#include "toys.h"

#include "utils/pairs.h"

Renderer gRenderer;

SDL_Window *gWindow = NULL;
char *SOURCE_PATH = NULL;

char PATH_BUFFER[FILENAME_MAX];

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
  setup_logic();

  setup();

  /* begin scratch */

  struct stumpless_target *target;
  target = stumpless_open_stdout_target("SMTMlog");

  /* end scratch */

  cwk_path_join(SOURCE_PATH, "resources/maze/source.txt", PATH_BUFFER, FILENAME_MAX);
  Maze maze = Maze_create(PATH_BUFFER);

  cwk_path_join(SOURCE_PATH, "resources/gottlob.png", PATH_BUFFER, FILENAME_MAX);
  Sprite x = Sprite_create(PATH_BUFFER);

  Anima gottlob = Anima_default("gottlob", x);
  Anima_deduction_known(&gottlob);

  int exitCode = 0;

  rgbVM colour;

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
        // std::cout << std::format("Maze x/y: {}/{} {}/{}", x, y, maze.size.x(), maze.size.y()) << "\n";
        PairI32 z = PairI32_create(x, y);
        if (Maze_tile_at(&maze, &z) != '#') {
          Renderer_fill_tile(&gRenderer, PairI32_create(x * gRenderer.kTileSize, y * gRenderer.kTileSize), 0xffffffff);
        }
      }
    }

    while (!quit) {

      NSTimer_start(&frameCapTimer);

      SDL_RenderClear(gRenderer.renderer);

      /* Renderer_fillTile(&gRenderer, gottlob.sprite.pos, 0x000000ff); */

      rgbVM_advance(&colour);
      SDL_SetRenderDrawColor(gRenderer.renderer, colour.state[0].value, colour.state[1].value, colour.state[2].value, 0x000000ff);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handle_event(&gottlob, &event);
      }
      Anima_deduct(&gottlob);

      Anima_move_within(&gottlob, &maze);

      Renderer_draw_sprite(&gRenderer, &gottlob.sprite);

      Renderer_update(&gRenderer);
      SDL_RenderPresent(gRenderer.renderer);
      SDL_Delay(1);

      Uint64 frameNS = NSTimer_get_ticks(&frameCapTimer);
      if (frameNS < kNS_PER_FRAME) {
        SDL_DelayNS(kNS_PER_FRAME - frameNS);
      }
    }
  }

  sdl_close();

  return exitCode;
}
