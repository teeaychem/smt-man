#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "SDL3/SDL_error.h"

#include "constants.h"
#include "render/render.h"
#include "render/sprite.h"
#include "utils/pairs.h"

Renderer Renderer_create(const PairI32 dimensions) {
  Renderer self = {.dimensions = dimensions};

  self.window = SDL_CreateWindow("smt-man", (int)(self.dimensions.x * UI_SCALE), (int)(self.dimensions.y * UI_SCALE), 0);
  if (self.window == nullptr) {
    SDL_Log("Failed to create window: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  self.renderer = SDL_CreateRenderer(self.window, nullptr);
  if (self.renderer == nullptr) {
    SDL_Log("Failed to create renderer: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  self.frame_buffer = malloc(PairI32_area(&self.dimensions) * sizeof(*self.frame_buffer));
  if (self.frame_buffer == nullptr) {
    SDL_Log("Failed to create frame_buffer");
    exit(-1);
  }

  self.texture = SDL_CreateTexture(self.renderer,
                                   SDL_PIXELFORMAT_ABGR8888,
                                   SDL_TEXTUREACCESS_STREAMING,
                                   (int)self.dimensions.x,
                                   (int)self.dimensions.y);
  if (self.texture == nullptr) {
    SDL_Log("Failed to create texture: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  SDL_SetRenderTarget(self.renderer, self.texture);

  return self;
}

void Renderer_destroy(Renderer *self) {
  SDL_DestroyWindow(self->window);
  self->window = nullptr;
}

void Renderer_update(Renderer *self) {
  /* SDL_RenderPresent(self->renderer); */
  int8_t *pixels = nullptr;
  int pitch;

  SDL_LockTexture(self->texture, nullptr, (void **)&pixels, &pitch);
  for (size_t i = 0, sp = 0, dp = 0; i < self->dimensions.y; i++, dp += self->dimensions.x, sp += (size_t)pitch) {
    memcpy(pixels + sp, self->frame_buffer + dp, self->dimensions.x * sizeof(*self->frame_buffer));
  }

  SDL_UnlockTexture(self->texture);

  auto render_result = SDL_RenderTexture(self->renderer, self->texture, nullptr, nullptr);
  if (!render_result) {
    SDL_Log("Failed to render texture: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  SDL_RenderPresent(self->renderer);
}

void Renderer_draw_sprite(Renderer *self, PairI32 position, SpriteInfo *sprite_info) {
  for (uint32_t row = 0; row < sprite_info->size.y; ++row) {

    for (uint32_t col = 0; col < sprite_info->size.x; ++col) {

      uint32_t pixel_fb = Renderer_pixel_at_point(self, position.y + col, position.x + row);

      if ((self->frame_buffer[pixel_fb] | 0x00000000) == 0x00000000) {

        uint32_t pixel_s = (sprite_info->surface_offset.y + col) * sprite_info->surface.size.x + sprite_info->surface_offset.x + row;

        self->frame_buffer[pixel_fb] = sprite_info->surface.pixels[pixel_s];
      }
    }
  }
}

void Renderer_erase_sprite(Renderer *self, PairI32 position, SpriteInfo *sprite_info) {
  for (uint32_t row = 0; row < sprite_info->size.y; ++row) {
    for (uint32_t col = 0; col < sprite_info->size.x; ++col) {

      uint32_t pixel_fb = Renderer_pixel_at_point(self, position.y + col, position.x + row);

      uint32_t pixel_s = SpriteInfo_pixel_at_point(sprite_info, col, row);
      if (self->frame_buffer[pixel_fb] == sprite_info->surface.pixels[pixel_s]) {
        self->frame_buffer[pixel_fb] = 0x00000000;
      }
    }
  }
}

void Renderer_fill_tile(Renderer *self, PairI32 origin, uint32_t colour) {

  for (size_t row = 0; row < TILE_SCALE; ++row) {
    for (size_t col = 0; col < TILE_SCALE; ++col) {
      size_t pixel = (origin.y + col) * origin.x + row;
      if ((self->frame_buffer[pixel] | 0x00000000) == 0x00000000) {
        self->frame_buffer[pixel] = colour;
      }
    }
  }
}
