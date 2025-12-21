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

void Renderer_read_maze(Renderer *self, Maze *maze) {
  // For each tile...
  printf("Tile scale: %d\n", self->frame_buffer.size.x / maze->size.x);

  uint32_t indent = TILE_PIXELS / 2;

  for (uint8_t col = 0; col < maze->size.x; ++col) {
    uint32_t col_scaled = (col * self->scale);

    for (uint8_t row = 0; row < maze->size.y; ++row) {
      uint32_t row_scaled = (row * self->scale);

      TileData *tile_data = Maze_abstract_at(maze, col, row);

      switch (tile_data->type) {

      case TILE_EDGE: {

        switch (tile_data->value.edge_value.edge_style) {

        case TILE_STYLE_LINE: {

          if (row == maze->padding_top) {
            Renderer_tile_line(self, col_scaled, row_scaled + indent - 1, RIGHT, TILE_PIXELS, 0xFFFFFFFF);
          } else if (row == (maze->size.y - maze->padding_bot - 1)) {
            Renderer_tile_line(self, col_scaled, row_scaled + indent + 1, RIGHT, TILE_PIXELS, 0xFFFFFFFF);
          } else {
            if (Maze_abstract_at(maze, col, row + 1)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled, row_scaled + indent - 1, RIGHT, TILE_PIXELS, 0xFFFFFFFF);
            } else if (Maze_abstract_at(maze, col, row - 1)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled, row_scaled + indent, RIGHT, TILE_PIXELS, 0xFFFFFFFF);
            } else if (col + 1 < maze->size.x && Maze_abstract_at(maze, col + 1, row)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled + indent - 1, row_scaled, DOWN, TILE_PIXELS, 0xFFFFFFFF);
            } else if (0 < col && Maze_abstract_at(maze, col - 1, row)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled + indent, row_scaled, DOWN, TILE_PIXELS, 0xFFFFFFFF);
            } else {
              printf("??? %d %d\n", row, col);
            }
          }

        } break;
        case TILE_STYLE_ARC: {
          Pair_uint32 tile_position = {.x = col_scaled, .y = row_scaled};

          if ((row == maze->padding_top) || (row == (maze->size.y - maze->padding_bot - 1)) ||
              (col == 0) || (col + 1 == maze->size.x)) {
            Renderer_tile_arc(self, tile_position, indent, tile_data->value.edge_value.edge_arc_value, 0xFFFFFFFF);
          } else {
            Renderer_tile_arc(self, tile_position, indent - 1, tile_data->value.edge_value.edge_arc_value, 0xFFFFFFFF);
          }
        } break;
        }

      } break;
      case TILE_EMPTY: {
        for (uint32_t pxl_y = 0; pxl_y < self->scale; ++pxl_y) {
          uint32_t y_offset = (row_scaled + pxl_y) * self->frame_buffer.size.x;
          for (uint32_t pxl_x = 0; pxl_x < self->scale; ++pxl_x) {
            uint32_t x_offset = pxl_x + col_scaled;
            self->frame_buffer.pixels[y_offset + x_offset] = 0x00f00fff;
          }
        }
      } break;
      case TILE_INFO: {
        for (uint32_t pxl_y = 0; pxl_y < self->scale; ++pxl_y) {
          uint32_t y_offset = (row_scaled + pxl_y) * self->frame_buffer.size.x;
          for (uint32_t pxl_x = 0; pxl_x < self->scale; ++pxl_x) {
            uint32_t x_offset = pxl_x + col_scaled;
            self->frame_buffer.pixels[y_offset + x_offset] = 0x00ff00ff;
          }
        }
      } break;
      case TILE_PATH: {
        for (uint32_t pxl_y = 0; pxl_y < self->scale; ++pxl_y) {
          uint32_t y_offset = (row_scaled + pxl_y) * self->frame_buffer.size.x;
          for (uint32_t pxl_x = 0; pxl_x < self->scale; ++pxl_x) {
            uint32_t x_offset = pxl_x + col_scaled;
            self->frame_buffer.pixels[y_offset + x_offset] = 0x00000000;
          }
        }
      } break;
      }
    }
  }
}

void Renderer_draw_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 offset, Pallete pallete) {

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {

      uint32_t pixel_fb = Surface_offset(&self->frame_buffer,
                                         location.x + col - Renderer_centre_offset(self, size),
                                         location.y + row - Renderer_centre_offset(self, size));

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

      uint32_t pixel_fb = Surface_offset(&self->frame_buffer,
                                         location.x + col - Renderer_centre_offset(self, size),
                                         location.y + row - Renderer_centre_offset(self, size));
      uint32_t pixel_s = Surface_offset(&self->sheet, offset.x + col, offset.y + row);

      if (self->frame_buffer.pixels[pixel_fb] == Pallete_offset(self->sheet.pixels[pixel_s], pallete)) {
        self->frame_buffer.pixels[pixel_fb] = 0x00000000;
      }
    }
  }
}

void Renderer_tile_fill(Renderer *self, Pair_uint32 origin, uint32_t colour) {

  for (size_t row = 0; row < self->scale; ++row) {
    for (size_t col = 0; col < self->scale; ++col) {
      size_t pixel = (origin.y + col) * origin.x + row;
      if ((self->frame_buffer.pixels[pixel] | 0x00000000) == 0x00000000) {
        self->frame_buffer.pixels[pixel] = colour;
      }
    }
  }
}

void Renderer_tile_line(Renderer *self, uint32_t x, uint32_t y, Direction direction, uint32_t length, uint32_t colour) {

  switch (direction) {

  case UP: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->frame_buffer.pixels[Renderer_buffer_index(self, x, y - idx)] = colour;
    }
  } break;
  case RIGHT: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->frame_buffer.pixels[Renderer_buffer_index(self, x + idx, y)] = colour;
    }
  } break;
  case DOWN: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->frame_buffer.pixels[Renderer_buffer_index(self, x, y + idx)] = colour;
    }
  } break;
  case LEFT: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->frame_buffer.pixels[Renderer_buffer_index(self, x - idx, y)] = colour;
    }
  } break;
  }
}

void Renderer_circle_draw(Renderer *self, Pair_uint32 *origin, Pair_uint32 *offset, Quadrant quadrant, uint32_t colour) {

  uint32_t pixel;

  switch (quadrant) {

  case FIRST: {
    pixel = Renderer_buffer_index(self, origin->x + offset->x, origin->y - offset->y);
    self->frame_buffer.pixels[pixel] = colour;

    pixel = Renderer_buffer_index(self, origin->x + offset->y, origin->y - offset->x);
    self->frame_buffer.pixels[pixel] = colour;
  } break;
  case SECOND: {
    pixel = Renderer_buffer_index(self, origin->x - offset->y, origin->y - offset->x);
    self->frame_buffer.pixels[pixel] = colour;

    pixel = Renderer_buffer_index(self, origin->x - offset->x, origin->y - offset->y);
    self->frame_buffer.pixels[pixel] = colour;
  } break;
  case THIRD: {
    pixel = Renderer_buffer_index(self, origin->x - offset->x, origin->y + offset->y);
    self->frame_buffer.pixels[pixel] = colour;

    pixel = Renderer_buffer_index(self, origin->x - offset->y, origin->y + offset->x);
    self->frame_buffer.pixels[pixel] = colour;
  } break;
  case FOURTH: {
    pixel = Renderer_buffer_index(self, origin->x + offset->x, origin->y + offset->y);
    self->frame_buffer.pixels[pixel] = colour;

    pixel = Renderer_buffer_index(self, origin->x + offset->y, origin->y + offset->x);
    self->frame_buffer.pixels[pixel] = colour;

  } break;
  }
}

void Renderer_tile_arc(Renderer *self, Pair_uint32 origin, uint32_t radius, Quadrant quadrant, uint32_t colour) {

  assert(radius <= INT32_MAX);

  Pair_uint32 offset = {.x = 0, .y = radius};

  switch (quadrant) {
  case FIRST: {
    origin.y += (TILE_PIXELS - 1);
  } break;
  case SECOND: {
    origin.x += (TILE_PIXELS - 1);
    origin.y += (TILE_PIXELS - 1);
  } break;
  case THIRD: {
    origin.x += (TILE_PIXELS - 1);
  } break;
  case FOURTH: {
  } break;
  }

  int32_t direction_relative = 1 - (int32_t)radius;
  int32_t turn_left = 3;
  int32_t turn_right = -((int32_t)radius << 1) + 5;

  Renderer_circle_draw(self, &origin, &offset, quadrant, colour);
  while (offset.y > offset.x) {
    if (direction_relative <= 0) {
      direction_relative += turn_left;
    } else {
      direction_relative += turn_right;
      turn_right += 2;
      offset.y -= 1;
    }
    turn_left += 2;
    turn_right += 2;
    offset.x += 1;

    Renderer_circle_draw(self, &origin, &offset, quadrant, colour);
  }
}
