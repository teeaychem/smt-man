#include <stdio.h>
#include <stdlib.h>

#include "render/constants.h"
#include "render/render.h"
#include "utils/pairs.h"

Renderer Renderer_create(SDL_Window *window, PairI32 dPixels) {
  Renderer self;
  self.dPixels = dPixels;

  self.renderer = SDL_CreateRenderer(window, NULL);
  self.frameBuffer = malloc(PairI32_area(&dPixels) * kTILE);
  self.texture = SDL_CreateTexture(self.renderer, SDL_PIXELFORMAT_RGBA32, SDL_TEXTUREACCESS_STREAMING, dPixels.x, dPixels.y);
  return self;
}

void Renderer_update(Renderer *self) {
  char *pix;
  int pitch;

  SDL_LockTexture(self->texture, NULL, (void **)&pix, &pitch);
  for (size_t i = 0, sp = 0, dp = 0; i < self->dPixels.y; i++, dp += self->dPixels.x, sp += pitch) {
    memcpy(pix + sp, self->frameBuffer + dp, self->dPixels.x * 4);
  }
  SDL_UnlockTexture(self->texture);
  SDL_RenderTexture(self->renderer, self->texture, NULL, NULL);
}

void Renderer_draw_sprite(Renderer *self, Sprite const *sprite) {
  size_t cell = 0;
  int32_t yOffset = sprite->pos.y * self->dPixels.x + sprite->pos.x;

  for (size_t row = 0; row < sprite->size.y; ++row) {
    for (size_t col = 0; col < sprite->size.x; ++col, ++cell) {
      if ((self->frameBuffer[yOffset + col] | 0x00000000) == 0x00000000) {
        self->frameBuffer[yOffset + col] = sprite->pixels[cell];
      }
    }
    yOffset += self->dPixels.x;
  }
}

void Renderer_erase_sprite(Renderer *self, Sprite const *sprite) {
  size_t cell = 0;
  int32_t yOffset = sprite->pos.y * self->dPixels.x + sprite->pos.x;

  for (size_t row = 0; row < sprite->size.y; ++row) {
    for (size_t col = 0; col < sprite->size.x; ++col, ++cell) {
      if (self->frameBuffer[yOffset + col] == sprite->pixels[cell]) {
        self->frameBuffer[yOffset + col] = 0x00000000;
      }
    }
    yOffset += self->dPixels.x;
  }
}

void Renderer_fill_tile(Renderer *self, PairI32 pos, int32_t colour) {

  int32_t yOffset = pos.y * self->dPixels.x + pos.x;

  for (size_t row = 0; row < kTILE; ++row) {
    for (size_t col = 0; col < kTILE; ++col) {
      if ((self->frameBuffer[yOffset + col] | 0x00000000) == 0x00000000) {
        self->frameBuffer[yOffset + col] = colour;
      }
    }
    yOffset += self->dPixels.x;
  }
}
