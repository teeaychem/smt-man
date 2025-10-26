#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <algorithm>
#include <cinttypes>
#include <cstddef>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <png.h>
#include <sys/types.h>
#include <whereami.h>

#include <cstdint>
#include <cstring>
#include <iostream>

#include "anima.hpp"

#include "maze.hpp"
#include "sprite.hpp"
#include "toys.hpp"
#include "unethical.hpp"
#include "utils.hpp"

SDL_Window *gWindow{nullptr};
std::filesystem::path SOURCE_PATH;

std::ostream &operator<<(std::ostream &os, Position p) {
  return os << "(" << p.x << "," << p.y << ")";
}

struct Renderer {

  SDL_Renderer *renderer{nullptr};
  int32_t *frameBuffer;
  SDL_Texture *texture{nullptr};

  Renderer() {}

  Renderer(SDL_Window *window) {
    renderer = SDL_CreateRenderer(gWindow, NULL);
    frameBuffer = new int32_t[dPixels.area()];
    texture = SDL_CreateTexture(renderer, SDL_PIXELFORMAT_RGBA32, SDL_TEXTUREACCESS_STREAMING, dPixels.W, dPixels.H);
  }

  void update() {
    char *pix;
    int pitch;

    SDL_LockTexture(this->texture, NULL, (void **)&pix, &pitch);
    for (int32_t i = 0, sp = 0, dp = 0; i < dPixels.H; i++, dp += dPixels.W, sp += pitch) {
      memcpy(pix + sp, this->frameBuffer + dp, dPixels.W * 4);
    }
    SDL_UnlockTexture(this->texture);
    SDL_RenderTexture(this->renderer, this->texture, NULL, NULL);
  }

  void drawSprite(Sprite const *sprite) {
    int cell = 0;
    int32_t yOffset = sprite->position.y * dPixels.W + sprite->position.x;

    for (int32_t row = 0; row < sprite->size.H; ++row) {
      for (int32_t col = 0; col < sprite->size.W; ++col, ++cell) {
        this->frameBuffer[yOffset + col] = sprite->pixels[cell];
      }
      yOffset += dPixels.W;
    }
  }

  void fillTile(Position const *position, int32_t colour) {

    int32_t yOffset = position->y * dPixels.W + position->x;

    for (int32_t row = 0; row < kTileSize; ++row) {
      for (int32_t col = 0; col < kTileSize; ++col) {
        this->frameBuffer[yOffset + col] = colour;
      }
      yOffset += dPixels.W;
    }
  }
};

Renderer gRenderer{};

bool sdl_init() {
  bool success{false};

  if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    gWindow = SDL_CreateWindow("Hello", dScreen.W, dScreen.H, 0);
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
  char *path = (char *)malloc((wai_length + 1));
  wai_getExecutablePath(path, wai_length, NULL);
  SOURCE_PATH = std::filesystem::path(path).parent_path();
  free(path);
}

Maze readMaze(std::filesystem::path path) {
  std::ifstream infile(path);
  if (!infile) {
    std::cout << "Failed to open maze from path: " << path << "\n";
    exit(1);
  }

  std::string line;
  if (!std::getline(infile, line)) {
    std::cout << "Failed to read maze information from path: " << path << "\n";
  }

  Size size{};
  char *mChars;

  while (std::getline(infile, line) && !line.empty() && line[0] != 'm') {
    if (line[0] == 'w') {
      if (!sscanf(line.c_str() + 1, "%" SCNu32, &size.W)) {
        std::cout << line.c_str() + 1 << "\n";
        std::cout << "Failed to read width of maze from path: " << path << "\n";
      };
    }

    else if (line[0] == 'h') {
      if (!sscanf(line.c_str() + 1, "%" SCNu32, &size.H)) {
        std::cout << line.c_str() + 1 << "\n";
        std::cout << "Failed to read height of maze from path: " << path << "\n";
      };
    }
  }

  mChars = (char *)malloc(size.area());
  memset(mChars, ' ', size.area());

  for (uint32_t r{0}; r < size.H; ++r) {
    if (!line.empty() && line[0] == 'm') {
      for (uint32_t c{1}; c <= std::min((size_t)size.W, line.size()); ++c) {
        mChars[r * size.W + c - 1] = line[c];
      }
    }
    if (r < size.H - 1 && !std::getline(infile, line)) {
      std::cout << "Failed to read maze from path: " << path << "\n";
      std::exit(-1);
    }
  }

  infile.close();

  return Maze{size, mChars};
}

int main(int argc, char **agrv) {

  setup();

  /* begin scratch */

  /* end scratch */

  Maze maze = readMaze(SOURCE_PATH / "resources/maze/source.txt");

  Anima gottlob{Sprite(SOURCE_PATH / "resources/gottlob.png")};

  int exitCode{0};

  colour_thing colour;

  if (!sdl_init()) {
    exitCode = 1;
  } else {

    bool quit{false};

    NSTimer frameCapTimer{};

    SDL_Event event;
    SDL_zero(event);

    // Draw the maze only once...
    for (uint32_t y{0}; y < maze.size.H; ++y) {
      for (uint32_t x{0}; x < maze.size.W; ++x) {
        if (maze.tileAt(Position{x, y}) != '#') {
          Position p{x * kTileSize, y * kTileSize};
          gRenderer.fillTile(&p, 0xffffffff);
        }
      }
    }

    while (!quit) {

      frameCapTimer.start();

      SDL_RenderClear(gRenderer.renderer);

      gRenderer.fillTile(&gottlob.sprite.position, 0x000000ff);

      colour.advance();
      SDL_SetRenderDrawColor(gRenderer.renderer, colour[0], colour[1], colour[2], 0xFF);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        gottlob.handleEvent(event);
      }

      gottlob.moveWithin(maze);
      gRenderer.drawSprite(&gottlob.sprite);

      gRenderer.update();
      SDL_RenderPresent(gRenderer.renderer);
      SDL_Delay(1);

      Uint64 frameNS{frameCapTimer.getTicksNS()};
      if (frameNS < nsPerFrame) {
        SDL_DelayNS(nsPerFrame - frameNS);
      }
    }
  }

  sdl_close();

  return exitCode;
}
