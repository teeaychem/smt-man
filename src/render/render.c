#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "SDL3/SDL_error.h"

#include "constants.h"
#include "render/render.h"
#include "utils/pairs.h"

Renderer Renderer_create() {
  Renderer self;

  self.window = SDL_CreateWindow("smt-man", PIXEL_DIMENSIONS.x * UI_SCALE, PIXEL_DIMENSIONS.y * UI_SCALE, 0);
  if (self.window == NULL) {
    SDL_Log("Failed to create window: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  self.renderer = SDL_CreateRenderer(self.window, NULL);
  if (self.renderer == NULL) {
    SDL_Log("Failed to create renderer: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  self.frame_buffer = malloc(PairI32_area(&PIXEL_DIMENSIONS) * sizeof(*self.frame_buffer));
  if (self.frame_buffer == NULL) {
    SDL_Log("Failed to create frame_buffer");
    exit(-1);
  }

  self.texture = SDL_CreateTexture(self.renderer,
                                   SDL_PIXELFORMAT_ABGR8888,
                                   SDL_TEXTUREACCESS_STREAMING,
                                   PIXEL_DIMENSIONS.x,
                                   PIXEL_DIMENSIONS.y);
  if (self.texture == NULL) {
    SDL_Log("Failed to create texture: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  SDL_SetRenderTarget(self.renderer, self.texture);

  return self;
}

void Renderer_destroy(Renderer *self) {
  SDL_DestroyWindow(self->window);
  self->window = NULL;
}

void Renderer_update(Renderer *self) {
  /* SDL_RenderPresent(self->renderer); */
  int8_t *pixels = NULL;
  int pitch;

  SDL_LockTexture(self->texture, NULL, (void **)&pixels, &pitch);
  for (size_t i = 0, sp = 0, dp = 0; i < PIXEL_DIMENSIONS.y; i++, dp += PIXEL_DIMENSIONS.x, sp += pitch) {
    memcpy(pixels + sp, self->frame_buffer + dp, PIXEL_DIMENSIONS.x * sizeof(*(self->frame_buffer)));
  }

  SDL_UnlockTexture(self->texture);

  auto render_result = SDL_RenderTexture(self->renderer, self->texture, NULL, NULL);
  if (!render_result) {
    SDL_Log("Failed to render texture: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  SDL_RenderPresent(self->renderer);
}

void Renderer_draw_sprite(Renderer *self, PairI32 position, SpriteInfo *sprite_info) {
  for (int32_t row = 0; row < sprite_info->size.y; ++row) {
    for (int32_t col = 0; col < sprite_info->size.x; ++col) {
      size_t pixel_fb = (position.y + col) * PIXEL_DIMENSIONS.x + position.x + row;
      if ((self->frame_buffer[pixel_fb] | 0x00000000) == 0x00000000) {
        size_t pixel_s = (sprite_info->surface_offset.y + col) * sprite_info->surface.size.x + sprite_info->surface_offset.x + row;
        self->frame_buffer[pixel_fb] = sprite_info->surface.pixels[pixel_s];
      }
    }
  }
}

void Renderer_erase_sprite(Renderer *self, PairI32 position, SpriteInfo *sprite_info) {
  for (int32_t row = 0; row < sprite_info->size.y; ++row) {
    for (int32_t col = 0; col < sprite_info->size.x; ++col) {
      size_t pixel_fb = (position.y + col) * PIXEL_DIMENSIONS.x + position.x + row;
      size_t pixel_s = (sprite_info->surface_offset.y + col) * sprite_info->surface.size.x + sprite_info->surface_offset.x + row;
      if (self->frame_buffer[pixel_fb] == sprite_info->surface.pixels[pixel_s]) {
        self->frame_buffer[pixel_fb] = 0x00000000;
      }
    }
  }
}

void Renderer_fill_tile(Renderer *self, PairI32 origin, int32_t colour) {

  for (size_t row = 0; row < TILE_SCALE; ++row) {
    for (size_t col = 0; col < TILE_SCALE; ++col) {
      size_t pixel = (origin.y + col) * origin.x + row;
      if ((self->frame_buffer[pixel] | 0x00000000) == 0x00000000) {
        self->frame_buffer[pixel] = colour;
      }
    }
  }
}
