#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "SDL3/SDL_error.h"

#include "constants.h"
#include "pairs.h"
#include "render.h"

Sheetoffsets sheet_offsets = {
    .anima = {
        .size = 16,
        .rt = {{.x = 1, .y = 83}, {.x = 18, .y = 83}},
        .dn = {{.x = 35, .y = 83}, {.x = 52, .y = 83}},
        .lt = {{.x = 69, .y = 83}, {.x = 86, .y = 83}},
        .up = {{.x = 103, .y = 83}, {.x = 120, .y = 83}},
    },
};

Renderer Renderer_create(const Pair_uint32 dimensions, Surface sheet) {
  Renderer self = {
      .dimensions = dimensions,
      .sheet = sheet,
  };

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

  self.frame_buffer = malloc(self.dimensions.x * self.dimensions.y * sizeof(*self.frame_buffer));
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

  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    Surface_destroy(&self->anima_sprites[idx].surface);
  }
}

void Renderer_update(Renderer *self) {
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

void Renderer_fill_tile(Renderer *self, Pair_uint32 origin, uint32_t colour) {

  for (size_t row = 0; row < TILE_SCALE; ++row) {
    for (size_t col = 0; col < TILE_SCALE; ++col) {
      size_t pixel = (origin.y + col) * origin.x + row;
      if ((self->frame_buffer[pixel] | 0x00000000) == 0x00000000) {
        self->frame_buffer[pixel] = colour;
      }
    }
  }
}

void Renderer_read_maze(Renderer *self, Maze *maze) {
  // For each tile...
  for (uint8_t pos_x = 0; pos_x < TILE_COUNTS.x; ++pos_x) {
    for (uint8_t pos_y = 0; pos_y < TILE_COUNTS.y; ++pos_y) {

      bool is_path = Maze_abstract_is_path(maze, pos_x, pos_y);

      for (uint32_t pxl_y = 0; pxl_y < TILE_SCALE; ++pxl_y) {
        uint32_t y_offset = ((pos_y * TILE_SCALE) + pxl_y) * self->dimensions.x;
        for (uint32_t pxl_x = 0; pxl_x < TILE_SCALE; ++pxl_x) {
          uint32_t x_offset = pxl_x + (pos_x * TILE_SCALE);

          self->frame_buffer[y_offset + x_offset] = is_path ? 0x00000000 : 0xffffffff;
        }
      }
    }
  }
}
