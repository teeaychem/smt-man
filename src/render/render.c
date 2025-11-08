#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "render/constants.h"
#include "render/render.h"
#include "utils/pairs.h"

Renderer Renderer_create() {
  Renderer self;

  self.gWindow = SDL_CreateWindow("smt-man", kPIXELS.x * kSCALE, kPIXELS.y * kSCALE, 0);

  self.renderer = SDL_CreateRenderer(self.gWindow, NULL);
  self.frameBuffer = malloc(PairI32_area(&kPIXELS) * sizeof(*self.frameBuffer));
  self.texture = SDL_CreateTexture(self.renderer,
                                   SDL_PIXELFORMAT_RGBA32,
                                   SDL_TEXTUREACCESS_STREAMING,
                                   kPIXELS.x, kPIXELS.y);
  return self;
}

void Renderer_destroy(Renderer *self) {
  SDL_DestroyWindow(self->gWindow);
  self->gWindow = NULL;
};

void Renderer_update(Renderer *self) {
  char *pix;
  int pitch;

  SDL_LockTexture(self->texture, NULL, (void **)&pix, &pitch);
  for (size_t i = 0, sp = 0, dp = 0; i < kPIXELS.y; i++, dp += kPIXELS.x, sp += pitch) {
    memcpy(pix + sp, self->frameBuffer + dp, kPIXELS.x * 4);
  }
  SDL_UnlockTexture(self->texture);
  SDL_RenderTexture(self->renderer, self->texture, NULL, NULL);
}

void Renderer_draw_surface(Renderer *self,
                           PairI32 const *position,
                           Surface const *surface,
                           PairI32 const *origin, PairI32 const *size) {
  for (size_t row = 0; row < size->y; ++row) {
    for (size_t col = 0; col < size->x; ++col) {
      size_t pixel_fb = (position->y + col) * kPIXELS.x + position->x + row;
      if ((self->frameBuffer[pixel_fb] | 0x00000000) == 0x00000000) {
        size_t pixel_s = (origin->y + col) * surface->size.x + origin->x + row;
        self->frameBuffer[pixel_fb] = surface->pixels[pixel_s];
      }
    }
  }
}

void Renderer_erase_surface(Renderer *self,
                            PairI32 const *position,
                            Surface const *surface,
                            PairI32 const *origin, PairI32 const *size) {
  for (size_t row = 0; row < size->y; ++row) {
    for (size_t col = 0; col < size->x; ++col) {
      size_t pixel_fb = (position->y + col) * kPIXELS.x + position->x + row;
      size_t pixel_s = (origin->y + col) * surface->size.x + origin->x + row;
      if (self->frameBuffer[pixel_fb] == surface->pixels[pixel_s]) {
        self->frameBuffer[pixel_fb] = 0x00000000;
      }
    }
  }
}

void Renderer_fill_tile(Renderer *self, PairI32 origin, int32_t colour) {

  for (size_t row = 0; row < kSPRITE; ++row) {
    for (size_t col = 0; col < kSPRITE; ++col) {
      size_t pixel = (origin.y + col) * origin.x + row;
      if ((self->frameBuffer[pixel] | 0x00000000) == 0x00000000) {
        self->frameBuffer[pixel] = colour;
      }
    }
  }
}
