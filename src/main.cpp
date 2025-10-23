#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <cstdint>
#include <cstring>
#include <iostream>

#include "anima.hpp"
#include "maze.hpp"
#include "toys.hpp"
#include "unethical.hpp"
#include "utils.hpp"

#include "unethical.hpp"

SDL_Window *gWindow{nullptr};

std::ostream &operator<<(std::ostream &os, Position p) {
  return os << "(" << p.x << "," << p.y << ")";
}

struct Renderer {

  SDL_Renderer *renderer{nullptr};
  int *frameBuffer;
  SDL_Texture *texture{nullptr};

  Renderer() {}

  Renderer(SDL_Window *window) {
    renderer = SDL_CreateRenderer(gWindow, NULL);
    frameBuffer = new int[dPixels.area()];
    texture = SDL_CreateTexture(renderer, SDL_PIXELFORMAT_ABGR8888, SDL_TEXTUREACCESS_STREAMING, dPixels.w, dPixels.h);
  }

  void update() {
    char *pix;
    int pitch;

    SDL_LockTexture(this->texture, NULL, (void **)&pix, &pitch);
    for (int i = 0, sp = 0, dp = 0; i < dPixels.h; i++, dp += dPixels.w, sp += pitch) {
      memcpy(pix + sp, this->frameBuffer + dp, dPixels.w * 4);
    }
    SDL_UnlockTexture(this->texture);
    SDL_RenderTexture(this->renderer, this->texture, NULL, NULL);
  }

  void drawSprite(SpritePixels const *pixels, Position const *position, int32_t colour) {
    int cell = 0;
    int32_t yOffset = position->y * dPixels.w + position->x;

    for (int32_t row = 0; row < kTileSize; ++row) {
      for (int32_t col = 0; col < kTileSize; ++col, ++cell) {
        if ((*pixels)[cell]) {
          this->frameBuffer[yOffset + col] = colour;
        }
      }
      yOffset += dPixels.w;
    }
  }

  void fill_tile(Position const *position, int32_t colour) {

    int32_t yOffset = position->y * dPixels.w + position->x;

    for (int32_t row = 0; row < kTileSize; ++row) {
      for (int32_t col = 0; col < kTileSize; ++col) {
        this->frameBuffer[yOffset + col] = colour;
      }
      yOffset += dPixels.w;
    }
  }
};

Renderer gRenderer{};

bool sdl_init() {
  bool success{false};

  if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    gWindow = SDL_CreateWindow("Hello", dScreen.w, dScreen.h, 0);
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

int main(int argc, char **agrv) {

  Maze maze{};
  std::cout << maze.as_string() << "\n";

  int exitCode{0};

  colour_thing colour;

  if (!sdl_init()) {
    exitCode = 1;
  } else {

    bool quit{false};

    NSTimer frameCapTimer{};
    Anima bonnie{};

    SDL_Event event;
    SDL_zero(event);

    while (!quit) {

      frameCapTimer.start();

      SDL_RenderClear(gRenderer.renderer);

      for (uint32_t y{0}; y < maze.size.h; ++y) {
        for (uint32_t x{0}; x < maze.size.w; ++x) {
          if (maze.tiles[y][x] != '#') {
            Position p{x * kTileSize, y * kTileSize};
            gRenderer.fill_tile(&p, 0xff0000ff);
          }
        }
      }

      gRenderer.drawSprite(bonnie.pixels(), bonnie.position(), 0x00000000);

      colour.advance();
      SDL_SetRenderDrawColor(gRenderer.renderer, colour[0], colour[1], colour[2], 0xFF);

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        bonnie.handleEvent(event);
      }

      bonnie.move();
      gRenderer.drawSprite(bonnie.pixels(), bonnie.position(), 0xffff0000);

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
