#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

bool sdl_init();
bool sdl_load_media();
void sdl_close();

constexpr int kScreenWidth{480};
constexpr int kScreenHeight{640};

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

int main(int argc, char **agrv) {

  int exitCode{0};

  if (!sdl_init()) {
    exitCode = 1;
  } else {
    bool quit{false};

    SDL_Event event;
    SDL_zero(event);

    while (!quit) {
      while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
          quit = true;
        }
      }

      SDL_FillSurfaceRect(gScreenSurface, nullptr, SDL_MapSurfaceRGB(gScreenSurface, 0xFF, 0xFF, 0xAE));

      SDL_UpdateWindowSurface(gWindow);
    }
  }

  sdl_close();

  return exitCode;
}
