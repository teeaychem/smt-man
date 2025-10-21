#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <cstring>
#include <limits>
#include <random>

#include "anima.hpp"
#include "utils.hpp"

#include "unethical.hpp"

SDL_Window *gWindow{nullptr};
SDL_Renderer *gRenderer{nullptr};
int *gFrameBuffer;
SDL_Texture *gTexture{nullptr};

constexpr int kTWidth{480};
constexpr int kTHeight{640};

bool sdl_init() {
  bool success{false};

  if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS)) {
    gWindow = SDL_CreateWindow("HiHi", kScreenWidth, kScreenHeight, 0);
    gRenderer = SDL_CreateRenderer(gWindow, NULL);
    gFrameBuffer = new int[kGridWidthPixels * kGridHeightPixels];
    gTexture = SDL_CreateTexture(gRenderer, SDL_PIXELFORMAT_ABGR8888, SDL_TEXTUREACCESS_STREAMING, kGridWidthPixels, kGridHeightPixels);

    success = true;
  }

  return success;
}

void sdl_close() {

  SDL_DestroyWindow(gWindow);
  gWindow = nullptr;

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

void update() {
  char *pix;
  int pitch;

  SDL_LockTexture(gTexture, NULL, (void **)&pix, &pitch);
  for (int i = 0, sp = 0, dp = 0; i < kGridHeightPixels; i++, dp += kGridWidthPixels, sp += pitch) {
    memcpy(pix + sp, gFrameBuffer + dp, kGridWidthPixels * 4);
  }
  SDL_UnlockTexture(gTexture);
  SDL_RenderTexture(gRenderer, gTexture, NULL, NULL);
}

int main(int argc, char **agrv) {

  int exitCode{0};

  colour_thing colour;

  if (!sdl_init()) {
    exitCode = 1;
  } else {

    bool quit{false};

    NSTimer frameCapTimer{};
    Anima bonnie{};
    bonnie.spawn(gRenderer);

    SDL_Event event;
    SDL_zero(event);

    while (!quit) {

      frameCapTimer.start();

      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
        bonnie.handleEvent(event);
      }

      SDL_RenderClear(gRenderer);


      bonnie.toBuffer(gFrameBuffer, 0x00000000);

      SDL_SetRenderDrawColor(gRenderer, colour[0], colour[1], colour[2], 0xFF);

      update();


      colour.advance();

      bonnie.move();
      bonnie.toBuffer(gFrameBuffer, 0xff000000);

      update();

      SDL_RenderPresent(gRenderer);
      SDL_Delay(1);

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
