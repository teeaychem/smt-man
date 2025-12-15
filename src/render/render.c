#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "SDL3/SDL_error.h"

#include "constants.h"
#include "generic/pairs.h"
#include "render.h"

void Renderer_create(Renderer *renderer, uint32_t scale, const Pair_uint8 maze_dimensions, char *sheet_path) {

  Surface sheet = {};
  Surface_from_path(&sheet, sheet_path);
  Pair_uint32 pixel_dimensions = {.x = maze_dimensions.x * scale, .y = maze_dimensions.y * scale};

  *renderer = (Renderer){
      .frame_buffer = {.size = pixel_dimensions,
                       .pixels = malloc(pixel_dimensions.x * pixel_dimensions.y * sizeof(*renderer->frame_buffer.pixels))},
      .scale = scale,
      .sheet = sheet,
  };
  if (renderer->frame_buffer.pixels == nullptr) {
    SDL_Log("Failed to create frame_buffer");
    exit(-1);
  }

  renderer->window = SDL_CreateWindow("smt-man", (int)(renderer->frame_buffer.size.x * UI_SCALE), (int)(renderer->frame_buffer.size.y * UI_SCALE), 0);
  if (renderer->window == nullptr) {
    SDL_Log("Failed to create window: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  renderer->renderer = SDL_CreateRenderer(renderer->window, nullptr);
  if (renderer->renderer == nullptr) {
    SDL_Log("Failed to create renderer: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  renderer->texture = SDL_CreateTexture(renderer->renderer,
                                        SDL_PIXELFORMAT_ABGR8888,
                                        SDL_TEXTUREACCESS_STREAMING,
                                        (int)renderer->frame_buffer.size.x,
                                        (int)renderer->frame_buffer.size.y);
  if (renderer->texture == nullptr) {
    SDL_Log("Failed to create texture: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  SDL_SetRenderTarget(renderer->renderer, renderer->texture);
}

void Renderer_destroy(Renderer *self) {

  SDL_DestroyWindow(self->window);
  self->window = nullptr;

  // TODO: Free other allocations
}

void Renderer_update(Renderer *self) {

  int8_t *pixels = nullptr;
  int pitch;

  SDL_LockTexture(self->texture, nullptr, (void **)&pixels, &pitch);
  for (size_t i = 0, sp = 0, dp = 0; i < self->frame_buffer.size.y; i++, dp += self->frame_buffer.size.x, sp += (size_t)pitch) {
    memcpy(pixels + sp, self->frame_buffer.pixels + dp, self->frame_buffer.size.x * sizeof(*self->frame_buffer.pixels));
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

  for (size_t row = 0; row < self->scale; ++row) {
    for (size_t col = 0; col < self->scale; ++col) {
      size_t pixel = (origin.y + col) * origin.x + row;
      if ((self->frame_buffer.pixels[pixel] | 0x00000000) == 0x00000000) {
        self->frame_buffer.pixels[pixel] = colour;
      }
    }
  }
}

void Renderer_read_maze(Renderer *self, Maze *maze) {
  // For each tile...
  printf("Tile scale: %d\n", self->frame_buffer.size.x / maze->size.x);

  for (uint8_t pos_x = 0; pos_x < maze->size.x; ++pos_x) {
    for (uint8_t pos_y = 0; pos_y < maze->size.y; ++pos_y) {

      bool is_path = Maze_abstract_is_path(maze, pos_x, pos_y);

      for (uint32_t pxl_y = 0; pxl_y < self->scale; ++pxl_y) {
        uint32_t y_offset = ((pos_y * self->scale) + pxl_y) * self->frame_buffer.size.x;
        for (uint32_t pxl_x = 0; pxl_x < self->scale; ++pxl_x) {
          uint32_t x_offset = pxl_x + (pos_x * self->scale);

          self->frame_buffer.pixels[y_offset + x_offset] = is_path ? 0x00000000 : 0xffffffff;
        }
      }
    }
  }
}


void Renderer_draw_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 offset, Pallete pallete) {

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {

      uint32_t pixel_fb = Surface_offset(&self->frame_buffer, location.x + col, location.y + row);

      if (self->frame_buffer.pixels[pixel_fb] == 0x00000000) {
        uint32_t pixel_s = Surface_offset(&self->sheet, offset.x + col, offset.y + row);

        self->frame_buffer.pixels[pixel_fb] = Pallete_offset(self->sheet.pixels[pixel_s], pallete);
      }
    }
  }
}

void Renderer_erase_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 offset, Pallete pallete) {

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {

      uint32_t pixel_fb = Surface_offset(&self->frame_buffer, location.x + col, location.y + row);
      uint32_t pixel_s = Surface_offset(&self->sheet, offset.x + col, offset.y + row);

      if (self->frame_buffer.pixels[pixel_fb] == Pallete_offset(self->sheet.pixels[pixel_s], pallete)) {
        self->frame_buffer.pixels[pixel_fb] = 0x00000000;
      }
    }
  }
}
