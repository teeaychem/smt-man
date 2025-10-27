#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <cstddef>
#include <cstdlib>

#include "cwalk.h"

#include <png.h>
#include <stumpless.h>
#include <sys/syslog.h>
#include <sys/types.h>
#include <whereami.h>

#include "anima.h"

#include "maze.h"
#include "sprite.h"
#include "toys.hpp"

#include "utils/NSTimer.h"
#include "utils/NVec.h"

constexpr uint32_t kTileSize{16};

constexpr int kScreenFps{30};

constexpr Uint64 nsPerFrame = 1000000000 / kScreenFps;

constexpr int kGridScale{2};
Size dMaze{28, 31};
Size dPixels = {dMaze.x() * kTileSize, dMaze.y() * kTileSize};
Size dScreen = {dPixels.x() * kGridScale, dPixels.y() * kGridScale};

SDL_Window *gWindow{nullptr};
char *SOURCE_PATH;
char PATH_BUFFER[FILENAME_MAX];

struct Renderer {

  SDL_Renderer *renderer{nullptr};
  int32_t *frameBuffer;
  SDL_Texture *texture{nullptr};

  Renderer() {}

  Renderer(SDL_Window *window) {
    renderer = SDL_CreateRenderer(gWindow, NULL);
    frameBuffer = new int32_t[dPixels.area()];
    texture = SDL_CreateTexture(renderer, SDL_PIXELFORMAT_RGBA32, SDL_TEXTUREACCESS_STREAMING, dPixels.x(), dPixels.y());
  }

  void update() {
    char *pix;
    int pitch;

    SDL_LockTexture(this->texture, NULL, (void **)&pix, &pitch);
    for (int32_t i = 0, sp = 0, dp = 0; i < dPixels.y(); i++, dp += dPixels.x(), sp += pitch) {
      memcpy(pix + sp, this->frameBuffer + dp, dPixels.x() * 4);
    }
    SDL_UnlockTexture(this->texture);
    SDL_RenderTexture(this->renderer, this->texture, NULL, NULL);
  }

  void drawSprite(Sprite const *sprite) {
    int cell = 0;
    int32_t yOffset = sprite->pos_y * dPixels.x() + sprite->pos_x;

    for (int32_t row = 0; row < sprite->size_h; ++row) {
      for (int32_t col = 0; col < sprite->size_w; ++col, ++cell) {
        this->frameBuffer[yOffset + col] = sprite->pixels[cell];
      }
      yOffset += dPixels.x();
    }
  }

  void fillTile(int32_t pos_x, int32_t pos_y, int32_t colour) {

    int32_t yOffset = pos_y * dPixels.x() + pos_x;

    for (int32_t row = 0; row < kTileSize; ++row) {
      for (int32_t col = 0; col < kTileSize; ++col) {
        this->frameBuffer[yOffset + col] = colour;
      }
      yOffset += dPixels.x();
    }
  }
};

Renderer gRenderer{};

bool sdl_init() {
  bool success{false};

  if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    gWindow = SDL_CreateWindow("Hello", dScreen.x(), dScreen.y(), 0);
    gRenderer = Renderer(gWindow);

    success = true;
  }

  return success;
}

void sdl_close() {
  SDL_DestroyWindow(gWindow);
  gWindow = nullptr;

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

  setup();

  /* begin scratch */

  struct stumpless_target *target;
  target = stumpless_open_stdout_target("SMTMlog");

  /* end scratch */

  cwk_path_join(SOURCE_PATH, "resources/maze/source.txt", PATH_BUFFER, FILENAME_MAX);
  Maze maze = Maze_create(PATH_BUFFER);

  cwk_path_join(SOURCE_PATH, "resources/gottlob.png", PATH_BUFFER, FILENAME_MAX);
  Sprite x = Sprite_create(PATH_BUFFER);

  Anima gottlob = Anima_default(x);

  int exitCode{0};

  colour_thing colour;

  if (!sdl_init()) {
    exitCode = 1;
  } else {

    bool quit{false};

    NSTimer frameCapTimer = NSTimer_default();

    SDL_Event event;
    SDL_zero(event);

    // Draw the maze only once...
    for (uint32_t y{0}; y < maze.size_y; ++y) {
      for (uint32_t x{0}; x < maze.size_x; ++x) {
        // std::cout << std::format("Maze x/y: {}/{} {}/{}", x, y, maze.size.x(), maze.size.y()) << "\n";
        if (Maze_tileAt(&maze, x, y) != '#') {
          gRenderer.fillTile(x * kTileSize, y * kTileSize, 0xffffffff);
        }
      }
    }

    while (!quit) {

      NSTimer_start(&frameCapTimer);

      SDL_RenderClear(gRenderer.renderer);

      gRenderer.fillTile(gottlob.sprite.pos_x, gottlob.sprite.pos_y, 0x000000ff);

      colour.advance();
      SDL_SetRenderDrawColor(gRenderer.renderer, colour[0], colour[1], colour[2], 0x000000ff);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        Anima_handleEvent(&gottlob, &event);
      }

      Anima_moveWithin(&gottlob, &maze);

      gRenderer.drawSprite(&gottlob.sprite);

      gRenderer.update();
      SDL_RenderPresent(gRenderer.renderer);
      SDL_Delay(1);

      Uint64 frameNS{NSTimer_getTicksNS(&frameCapTimer)};
      if (frameNS < nsPerFrame) {
        SDL_DelayNS(nsPerFrame - frameNS);
      }
    }
  }

  sdl_close();

  return exitCode;
}
