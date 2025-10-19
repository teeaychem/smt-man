#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>
#include <iostream>
#include <limits>
#include <random>

#include "utils/utils.hpp"

bool sdl_init();
bool sdl_load_media();
void sdl_close();

constexpr int kScreenWidth{480};
constexpr int kScreenHeight{640};
constexpr int kScreenFps{60};

SDL_Window *gWindow{nullptr};
SDL_Surface *gScreenSurface{nullptr};
SDL_Surface *gHelloWorld{nullptr};

bool sdl_init() {
  bool success{false};

  if (SDL_Init(SDL_INIT_VIDEO)) {
    if (gWindow = SDL_CreateWindow("HiHi", kScreenWidth, kScreenHeight, 0); gWindow != nullptr) {
      success = true;
      gScreenSurface = SDL_GetWindowSurface(gWindow);
    }
  }

  return success;
}

void sdl_close() {
  SDL_DestroySurface(gHelloWorld);
  gHelloWorld = nullptr;

  SDL_DestroyWindow(gWindow);
  gWindow = nullptr;
  gScreenSurface = nullptr;

  SDL_Quit();
}

struct colour_thing {
  std::pair<Uint8, bool> state[3];
  Uint8 current{0};

  std::random_device rd{};
  std::minstd_rand0 gen{rd()};
  std::uniform_int_distribution<> distr{0, 2};

  int operator[](std::size_t i) const { return state[i].first; }

  void advance() {
    auto current = distr(gen);

    if (state[current].first == std::numeric_limits<Uint8>::max()) {
      state[current].second = false;
    } else if (state[current].first == std::numeric_limits<Uint8>::min()) {
      state[current].second = true;
    }

    if (state[current].second) {
      state[current].first = (state[current].first + 1);
    } else {
      state[current].first = (state[current].first - 1);
    }
  }
};

int main(int argc, char **agrv) {

  int exitCode{0};

  colour_thing colour;

  if (!sdl_init()) {
    exitCode = 1;
  } else {
    bool quit{false};
    SDLTimer frameCapTimer{};

    SDL_Event event;
    SDL_zero(event);

    while (!quit) {

      frameCapTimer.start();

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
      }

      SDL_FillSurfaceRect(gScreenSurface, nullptr, SDL_MapSurfaceRGB(gScreenSurface, colour[0], colour[1], colour[2]));

      colour.advance();

      SDL_UpdateWindowSurface(gWindow);
      constexpr Uint64 nsPerFrame = 1000000000 / kScreenFps;
      Uint64 frameNS{frameCapTimer.getTicksNS()};
      if (frameNS < nsPerFrame) {
        SDL_DelayNS(nsPerFrame - frameNS);
      }
    }
  }

  sdl_close();

  return exitCode;
}
