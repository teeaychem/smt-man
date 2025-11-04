#include <stdio.h>
#include <stdlib.h>

#include "render/constants.h"
#include "render/render.h"
#include "utils/pairs.h"

Renderer Renderer_create() {
  Renderer self;

  self.gWindow = SDL_CreateWindow("smt-man", kPIXELS.x * kSCALE, kPIXELS.y * kSCALE, 0);

  self.renderer = SDL_CreateRenderer(self.gWindow, NULL);
  self.frameBuffer = malloc(PairI32_area(&kPIXELS) * kTILE);
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

void Renderer_draw_sprite(Renderer *self, Sprite const *sprite) {
  size_t cell = 0;
  int32_t yOffset = sprite->pos.y * kPIXELS.x + sprite->pos.x;

  for (size_t row = 0; row < sprite->size.y; ++row) {
    for (size_t col = 0; col < sprite->size.x; ++col, ++cell) {
      if ((self->frameBuffer[yOffset + col] | 0x00000000) == 0x00000000) {
        self->frameBuffer[yOffset + col] = sprite->pixels[cell];
      }
    }
    yOffset += kPIXELS.x;
  }
}

void Renderer_erase_sprite(Renderer *self, Sprite const *sprite) {
  size_t cell = 0;
  int32_t yOffset = sprite->pos.y * kPIXELS.x + sprite->pos.x;

  for (size_t row = 0; row < sprite->size.y; ++row) {
    for (size_t col = 0; col < sprite->size.x; ++col, ++cell) {
      if (self->frameBuffer[yOffset + col] == sprite->pixels[cell]) {
        self->frameBuffer[yOffset + col] = 0x00000000;
      }
    }
    yOffset += kPIXELS.x;
  }
}

void Renderer_fill_tile(Renderer *self, PairI32 pos, int32_t colour) {

  int32_t yOffset = pos.y * kPIXELS.x + pos.x;

  for (size_t row = 0; row < kTILE; ++row) {
    for (size_t col = 0; col < kTILE; ++col) {
      if ((self->frameBuffer[yOffset + col] | 0x00000000) == 0x00000000) {
        self->frameBuffer[yOffset + col] = colour;
      }
    }
    yOffset += kPIXELS.x;
  }
}
