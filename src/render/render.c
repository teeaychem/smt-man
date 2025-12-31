#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <SDL3/SDL_error.h>

#include "generic/pairs.h"
#include "render.h"
#include "render/sheet.h"

void Renderer_create(Renderer *renderer, const Pair_uint8 maze_dimensions, const char *sheet_path) {

  Surface sheet = {};
  Surface_from_path(&sheet, sheet_path);
  Pair_uint32 pixel_dimensions = {.x = maze_dimensions.x * TILE_PIXELS, .y = maze_dimensions.y * TILE_PIXELS};

  *renderer = (Renderer){
      .frame_buffer = {.size = pixel_dimensions,
                       .pixels = malloc(pixel_dimensions.x * pixel_dimensions.y * sizeof(*renderer->frame_buffer.pixels))},
      .pre_buffer = {.size = {TILE_PIXELS * 4, TILE_PIXELS * 4},
                     .pixels = malloc((TILE_PIXELS * 4) * (TILE_PIXELS * 4) * sizeof(*renderer->pre_buffer.pixels))},
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

void Renderer_drop(Renderer *self) {

  SDL_DestroyWindow(self->window);
  self->window = nullptr;

  // TODO: Free other allocations
}

void Renderer_render_frame_buffer(Renderer *self) {

  { // Write out the frame buffer
    int8_t *pixels = nullptr;
    int pitch;

    SDL_LockTexture(self->texture, nullptr, (void **)&pixels, &pitch);
    size_t i = 0;
    size_t sp = 0;
    size_t dp = 0;
    for (; i < self->frame_buffer.size.y; i++, dp += self->frame_buffer.size.x, sp += (size_t)pitch) {
      memcpy(pixels + sp, self->frame_buffer.pixels + dp, self->frame_buffer.size.x * sizeof(*self->frame_buffer.pixels));
    }

    SDL_UnlockTexture(self->texture);
  }

  auto render_result = SDL_RenderTexture(self->renderer, self->texture, nullptr, nullptr);
  if (!render_result) {
    SDL_Log("Failed to render texture: %s", SDL_GetError());
    exit(SDL_APP_FAILURE);
  }

  SDL_RenderPresent(self->renderer);
}

void Renderer_read_maze(Renderer *self, const Maze *maze) {
  // For each tile...
  uint32_t indent = TILE_PIXELS / 2;

  for (uint8_t col = 0; col < maze->size.x; ++col) {
    uint32_t col_scaled = (col * TILE_PIXELS);

    for (uint8_t row = 0; row < maze->size.y; ++row) {
      uint32_t row_scaled = (row * TILE_PIXELS);

      TileData *tile_data = Maze_abstract_at(maze, col, row);

      switch (tile_data->type) {

      case TILE_EDGE: {

        switch (tile_data->value.edge_value.edge_style) {

        case TILE_STYLE_LINE: {

          if (row == maze->padding_top) {
            Renderer_tile_line(self, col_scaled, row_scaled + indent - 1, PLANE_HORIZONTAL, TILE_PIXELS, 0xffffffff);
          } else if (row == (maze->size.y - maze->padding_bot - 1)) {
            Renderer_tile_line(self, col_scaled, row_scaled + indent, PLANE_HORIZONTAL, TILE_PIXELS, 0xffffffff);
          } else {
            if (Maze_abstract_at(maze, col, row + 1)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled, row_scaled + indent - 1, PLANE_HORIZONTAL, TILE_PIXELS, 0xffffffff);
            } else if (Maze_abstract_at(maze, col, row - 1)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled, row_scaled + indent, PLANE_HORIZONTAL, TILE_PIXELS, 0xffffffff);
            } else if (col + 1 < maze->size.x && Maze_abstract_at(maze, col + 1, row)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled + indent - 1, row_scaled, PLANE_VERTICAL, TILE_PIXELS, 0xffffffff);
            } else if (0 < col && Maze_abstract_at(maze, col - 1, row)->type == TILE_PATH) {
              Renderer_tile_line(self, col_scaled + indent, row_scaled, PLANE_VERTICAL, TILE_PIXELS, 0xffffffff);
            } else {
              printf("??? %d %d\n", row, col);
            }
          }

        } break;
        case TILE_STYLE_ARC: {
          Pair_uint32 tile_position = {.x = col_scaled, .y = row_scaled};

          if ((row == maze->padding_top) || (row == (maze->size.y - maze->padding_bot - 1)) ||
              (col == 0) || (col + 1 == maze->size.x)) {
            Renderer_tile_arc(self, tile_position, indent, tile_data->value.edge_value.edge_arc_value, 0xffffffff);
          } else {
            Renderer_tile_arc(self, tile_position, indent - 1, tile_data->value.edge_value.edge_arc_value, 0xffffffff);
          }
        } break;
        }

      } break;
      case TILE_EMPTY: {
        for (uint32_t pxl_y = 0; pxl_y < TILE_PIXELS; ++pxl_y) {
          uint32_t y_offset = (row_scaled + pxl_y) * self->frame_buffer.size.x;
          for (uint32_t pxl_x = 0; pxl_x < TILE_PIXELS; ++pxl_x) {
            uint32_t x_offset = pxl_x + col_scaled;
            self->frame_buffer.pixels[y_offset + x_offset] = 0x00ff00ff;
          }
        }
      } break;
      case TILE_INFO: {
        for (uint32_t pxl_y = 0; pxl_y < TILE_PIXELS; ++pxl_y) {
          uint32_t y_offset = (row_scaled + pxl_y) * self->frame_buffer.size.x;
          for (uint32_t pxl_x = 0; pxl_x < TILE_PIXELS; ++pxl_x) {
            uint32_t x_offset = pxl_x + col_scaled;
            self->frame_buffer.pixels[y_offset + x_offset] = 0x00ff00ff;
          }
        }
      } break;
      case TILE_PATH: {
        for (uint32_t pxl_y = 0; pxl_y < TILE_PIXELS; ++pxl_y) {
          uint32_t y_offset = (row_scaled + pxl_y) * self->frame_buffer.size.x;
          for (uint32_t pxl_x = 0; pxl_x < TILE_PIXELS; ++pxl_x) {
            uint32_t x_offset = pxl_x + col_scaled;
            self->frame_buffer.pixels[y_offset + x_offset] = 0x00000000;
          }
        }
      } break;
      }
    }
  }
}

void Renderer_draw_from_sheet(Renderer *self, const Pair_uint32 destination, const uint32_t size, const Pair_uint32 source, const Pallete pallete) {

  uint32_t pixel_fb;
  uint32_t pixel_s;
  uint32_t centre_offset = Renderer_centre_offset(size);

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {

      pixel_fb = Surface_offset(&self->frame_buffer, destination.x + col - centre_offset, destination.y + row - centre_offset);

      if (self->frame_buffer.pixels[pixel_fb] == 0x00000000) {
        pixel_s = Surface_offset(&self->sheet, source.x + col, source.y + row);
        self->frame_buffer.pixels[pixel_fb] = Pallete_offset(self->sheet.pixels[pixel_s], pallete);
      }
    }
  }
}

void Renderer_tile_fill(Renderer *self, const Pair_uint32 origin, const uint32_t colour) {

  for (size_t row = 0; row < TILE_PIXELS; ++row) {
    for (size_t col = 0; col < TILE_PIXELS; ++col) {
      size_t pixel = (origin.y + col) * origin.x + row;
      if ((self->frame_buffer.pixels[pixel] | 0x00000000) == 0x00000000) {
        self->frame_buffer.pixels[pixel] = colour;
      }
    }
  }
}

void Renderer_tile_line(Renderer *self, const uint32_t x, const uint32_t y, const Plane plane, const uint32_t length, const uint32_t colour) {

  switch (plane) {
  case PLANE_HORIZONTAL: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->frame_buffer.pixels[Surface_offset(&self->frame_buffer, x + idx, y)] = colour;
    }
  } break;
  case PLANE_VERTICAL: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->frame_buffer.pixels[Surface_offset(&self->frame_buffer, x, y + idx)] = colour;
    }
  } break;
  }
}

void Renderer_circle_draw(Renderer *self, Pair_uint32 *origin, Pair_uint32 *offset, Quadrant quadrant, uint32_t colour) {

  switch (quadrant) {

  case QUADRANT_FIRST: {
    uint32_t pixel_a = Surface_offset(&self->frame_buffer, origin->x + offset->x, origin->y - offset->y);
    self->frame_buffer.pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(&self->frame_buffer, origin->x + offset->y, origin->y - offset->x);
    self->frame_buffer.pixels[pixel_b] = colour;
  } break;
  case QUADRANT_SECOND: {
    uint32_t pixel_a = Surface_offset(&self->frame_buffer, origin->x - offset->y, origin->y - offset->x);
    self->frame_buffer.pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(&self->frame_buffer, origin->x - offset->x, origin->y - offset->y);
    self->frame_buffer.pixels[pixel_b] = colour;
  } break;
  case QUADRANT_THIRD: {
    uint32_t pixel_a = Surface_offset(&self->frame_buffer, origin->x - offset->x, origin->y + offset->y);
    self->frame_buffer.pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(&self->frame_buffer, origin->x - offset->y, origin->y + offset->x);
    self->frame_buffer.pixels[pixel_b] = colour;
  } break;
  case QUADRANT_FOURTH: {
    uint32_t pixel_a = Surface_offset(&self->frame_buffer, origin->x + offset->x, origin->y + offset->y);
    self->frame_buffer.pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(&self->frame_buffer, origin->x + offset->y, origin->y + offset->x);
    self->frame_buffer.pixels[pixel_b] = colour;

  } break;
  }
}

void Renderer_tile_arc(Renderer *self, const Pair_uint32 origin, const uint32_t radius, const Quadrant quadrant, const uint32_t colour) {

  assert(radius <= INT32_MAX);

  Pair_uint32 offset = {.x = 0, .y = radius};

  Pair_uint32 origin_offset = origin;

  switch (quadrant) {
  case QUADRANT_FIRST: {
    origin_offset.y += (TILE_PIXELS - 1);
  } break;
  case QUADRANT_SECOND: {
    origin_offset.x += (TILE_PIXELS - 1);
    origin_offset.y += (TILE_PIXELS - 1);
  } break;
  case QUADRANT_THIRD: {
    origin_offset.x += (TILE_PIXELS - 1);
  } break;
  case QUADRANT_FOURTH: {
  } break;
  }

  int32_t direction_relative = 1 - (int32_t)radius;
  int32_t turn_left = 3;
  int32_t turn_right = -((int32_t)radius << 1) + 5;

  Renderer_circle_draw(self, &origin_offset, &offset, quadrant, colour);
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

    Renderer_circle_draw(self, &origin_offset, &offset, quadrant, colour);
  }
}

void Renderer_anima(Renderer *self, const Anima animas[ANIMA_COUNT], const uint8_t id, const RenderAction action) {

  switch (action) {
  case RENDER_DRAW: {
    Renderer_sprite_buffer_map_to(self, Sheet_anima_offset(&animas[id]), animas[id].sprite_size);
    Surface_pallete_mut(&self->pre_buffer, animas[id].sprite_size, animas[id].pallete);

    Renderer_draw_from_sprite_buffer(self, animas[id].sprite_location, animas[id].sprite_size);
  } break;
  case RENDER_ERASE: {
    Renderer_sprite_fill(self, animas[id].sprite_location, animas[id].sprite_size, 0x00000000);
  } break;
  }
}

void Renderer_persona(Renderer *self, const Persona *persona, const Situation *situation, const RenderAction action) {

  switch (action) {
  case RENDER_DRAW: {
    Renderer_sprite_buffer_map_to(self, Sheet_persona_offset(persona, situation), persona->sprite_size);

    switch (situation->persona.direction_actual) {
    case DIRECTION_NONE: {
      // Do nothing
    } break;
    case DIRECTION_N: {
      Surface_mirror_mut(&self->pre_buffer, persona->sprite_size);
      Surface_transpose_mut(&self->pre_buffer, persona->sprite_size);
    } break;
    case DIRECTION_E: {
      // No transformation
    } break;
    case DIRECTION_S: {
      Surface_transpose_mut(&self->pre_buffer, persona->sprite_size);
    } break;
    case DIRECTION_W: {
      Surface_mirror_mut(&self->pre_buffer, persona->sprite_size);
    } break;
    }

    Surface_pallete_mut(&self->pre_buffer, persona->sprite_size, persona->pallete);
    Renderer_draw_from_sprite_buffer(self, persona->sprite_location, persona->sprite_size);
  } break;
  case RENDER_ERASE: {
    Renderer_sprite_fill(self, persona->sprite_location, persona->sprite_size, 0x00000000);
  } break;
  }
}

void Renderer_sprite_buffer_map_to(Renderer *self, const Pair_uint32 sprite_offset, const uint8_t size) {

  for (uint32_t idx = 0; idx < size; ++idx) {
    uint32_t pre_offset = Surface_offset(&self->pre_buffer, 0, idx);
    uint32_t sheet_offset = Surface_offset(&self->sheet, sprite_offset.x, sprite_offset.y + idx);

    memcpy(&self->pre_buffer.pixels[pre_offset], &self->sheet.pixels[sheet_offset], size * sizeof(*self->pre_buffer.pixels));
  }
}

void Renderer_draw_from_sprite_buffer(Renderer *self, const Pair_uint32 destination, const uint32_t size) {
  uint32_t pixel_fb;
  uint32_t pixel_s;
  uint32_t centre_offset = Renderer_centre_offset(size);

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {
      pixel_fb = Surface_offset(&self->frame_buffer, destination.x + col - centre_offset, destination.y + row - centre_offset);

      if (self->frame_buffer.pixels[pixel_fb] == 0x00000000) {
        pixel_s = Surface_offset(&self->pre_buffer, col, row);
        self->frame_buffer.pixels[pixel_fb] = self->pre_buffer.pixels[pixel_s];
      }
    }
  }
}

void Renderer_sprite_fill(Renderer *self, const Pair_uint32 location, const uint32_t size, const uint32_t colour) {
  uint32_t centre_offset = Renderer_centre_offset(size);

  Pair_uint32 location_offset = {.x = location.x - centre_offset,
                                 .y = location.y - centre_offset};

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {
      size_t pixel = Surface_offset(&self->frame_buffer, location_offset.x + row, location_offset.y + col);
      self->frame_buffer.pixels[pixel] = colour;
    }
  }
}
