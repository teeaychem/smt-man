#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include <SDL3/SDL_error.h>

#include "err.h"
#include "generic/pairs.h"
#include "render.h"
#include "render/sheet.h"

void renderer_ctor(renderer_s *self, const Pair_uint8 maze_dimensions, const char *sheet_path) {

  Pair_uint32 pixel_dimensions = {
      .x = (maze_dimensions.x + RENDER_TOP + RENDER_BOT) * TILE_PIXELS,
      .y = maze_dimensions.y * TILE_PIXELS,
  };

  *self = (renderer_s){
      .frame_buffer = {
          .dimensions = pixel_dimensions,
          .pixels = malloc(pixel_dimensions.x * pixel_dimensions.y * sizeof(*self->frame_buffer.pixels)),
      },

      .sprite_buffer = {
          .dimensions = (Pair_uint32){
              .x = SPRITE_BUFFER_SIZE,
              .y = SPRITE_BUFFER_SIZE,
          },
          .pixels = malloc(SPRITE_BUFFER_SIZE * SPRITE_BUFFER_SIZE * sizeof(*self->sprite_buffer.pixels)),
      },
  };

  panic(self->frame_buffer.pixels == nullptr, "Failed to create frame buffer", SDL_APP_FAILURE);
  panic(self->sprite_buffer.pixels == nullptr, "Failed to create sprite buffer", -1);

  surface_ctor(&self->sheet, sheet_path);

  {     // Renderer texture
    {   // Renderer
      { // Window
        self->window = SDL_CreateWindow("smt-man", (int)(self->frame_buffer.dimensions.y * UI_SCALE), (int)(self->frame_buffer.dimensions.x * UI_SCALE), 0);
        panic(self->window == nullptr, "Failed to create window", SDL_APP_FAILURE);
      }

      self->renderer = SDL_CreateRenderer(self->window, nullptr);
      panic(self->renderer == nullptr, "Failed to create renderer", SDL_APP_FAILURE);
    }

    self->texture = SDL_CreateTexture(self->renderer,
                                      SDL_PIXELFORMAT_ABGR8888,
                                      SDL_TEXTUREACCESS_STREAMING,
                                      (int)self->frame_buffer.dimensions.y,
                                      (int)self->frame_buffer.dimensions.x);
    panic(self->texture == nullptr, "Failed to create texture", SDL_APP_FAILURE);
  }

  SDL_SetRenderTarget(self->renderer, self->texture);
}

void renderer_dtor(renderer_s *self) {

  SDL_DestroyTexture(self->texture);
  self->texture = nullptr;

  SDL_DestroyRenderer(self->renderer);
  self->renderer = nullptr;

  SDL_DestroyWindow(self->window);
  self->window = nullptr;

  surface_dtor(&self->sprite_buffer);
  surface_dtor(&self->frame_buffer);

  surface_dtor(&self->sheet);
}

void renderer_clear(renderer_s *self) {
  memset(self->frame_buffer.pixels, 0, sizeof(*self->frame_buffer.pixels) * self->frame_buffer.dimensions.x * self->frame_buffer.dimensions.y);
}

void renderer_render_frame_buffer(renderer_s *self) {

  { // Write out the frame buffer
    int8_t *pixels = nullptr;
    int pitch;

    SDL_LockTexture(self->texture, nullptr, (void **)&pixels, &pitch);
    size_t i = 0;
    size_t sp = 0;
    size_t dp = 0;
    for (; i < self->frame_buffer.dimensions.x; i++, dp += self->frame_buffer.dimensions.y, sp += (size_t)pitch) {
      memcpy(pixels + sp, self->frame_buffer.pixels + dp, self->frame_buffer.dimensions.y * sizeof(*self->frame_buffer.pixels));
    }

    SDL_UnlockTexture(self->texture);
  }

  auto render_result = SDL_RenderTexture(self->renderer, self->texture, nullptr, nullptr);
  panic(!render_result, "Failed to render texture", SDL_APP_FAILURE);

  SDL_RenderPresent(self->renderer);
}

void renderer_draw_maze(renderer_s *self, const maze_s *maze) {

  for (uint8_t row = 0; row < maze->dimensions.x; ++row) {
    uint32_t row_scaled = ((row + RENDER_TOP) * TILE_PIXELS);

    for (uint8_t col = 0; col < maze->dimensions.y; ++col) {
      uint32_t col_scaled = (col * TILE_PIXELS);

      Pair_uint32 tile_position = {.x = row_scaled, .y = col_scaled};

      tile_data_s *tile_data = maze_tile_data_at(maze, row, col);

      switch (tile_data->type) {

      case TILE_EDGE: {

        switch (tile_data->value.edge_value.edge_style) {

        case TILE_STYLE_NONE: {
        } break;

        case TILE_STYLE_LINE: {

          plane_e plane = tile_data->value.edge_value.edge_line_plane;

          uint32_t adjustment;
          switch (tile_data->value.edge_value.lines) {
          case TILE_LINES_P: {
            adjustment = MAZE_INDENT;
          } break;
          case TILE_LINES_M: {
            adjustment = MAZE_INDENT - 1;
          } break;
          }

          switch (plane) {
          case PLANE_H: {
            surface_tile_line(&self->frame_buffer, row_scaled + adjustment, col_scaled, plane, TILE_PIXELS, 0xffffffff);
          } break;
          case PLANE_V: {
            surface_tile_line(&self->frame_buffer, row_scaled, col_scaled + adjustment, plane, TILE_PIXELS, 0xffffffff);
          } break;
          }

        } break;

        case TILE_STYLE_ARC: {
          surface_tile_fixed_arc(&self->frame_buffer, tile_position, tile_data, 0xffffffff);
        } break;
        }
      } break;

      case TILE_EMPTY: {
        surface_fill_tile(&self->frame_buffer, tile_position, TILE_PIXELS, 0x00000000);
      } break;

      case TILE_INFO: {
        surface_fill_tile(&self->frame_buffer, tile_position, TILE_PIXELS, 0x00ffffff);
      } break;

      case TILE_PATH: {
        surface_fill_tile(&self->frame_buffer, tile_position, TILE_PIXELS, 0x00000000);
      } break;
      }
    }
  }
}

void renderer_drawn_from_sheet(renderer_s *self, const Pair_uint32 destination, const uint32_t size, const Pair_uint32 source, const Pallete pallete) {

  uint32_t pixel_fb;
  uint32_t pixel_s;
  uint32_t centre_offset = renderer_centre_offset(size);

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {

      pixel_fb = (uint32_t)Pair_uint32_flatten(&self->frame_buffer.dimensions, destination.x + col - centre_offset, destination.y + row - centre_offset);

      if (self->frame_buffer.pixels[pixel_fb] == 0x00000000) {
        pixel_s = (uint32_t)Pair_uint32_flatten(&self->sheet.dimensions, source.x + col, source.y + row);
        self->frame_buffer.pixels[pixel_fb] = Pallete_offset(self->sheet.pixels[pixel_s], pallete);
      }
    }
  }
}

void renderer_anima(renderer_s *self, const anima_s *anima, const situation_s *situation, sprite_s *sprite, const renderer_action_e action) {

  switch (action) {
  case RENDER_DRAW: {
    renderer_sprite_buffer_map_to(self, sheet_offset_anima(anima, situation), sprite->size);
    surface_apply_pallete(&self->sprite_buffer, sprite->size, DEFAULT_PALLETES.animas[anima->id]);

    renderer_draw_from_sprite_buffer(self, sprite->location, sprite->size);
  } break;
  case RENDER_ERASE: {
    renderer_sprite_fill(self, sprite->location, sprite->size, 0x00000000, false);
  } break;
  }
}

void renderer_persona(renderer_s *self, const persona_s *persona, sprite_s *sprite, const situation_s *situation, const renderer_action_e action) {

  switch (action) {
  case RENDER_DRAW: {
    renderer_sprite_buffer_map_to(self, sheet_offset_persona(persona, situation), sprite->size);

    switch (situation->persona.direction_actual) {
    case CARDINAL_NONE: {
      // No transformation
    } break;
    case CARDINAL_N: {
      surface_mirror(&self->sprite_buffer, sprite->size);
      surface_transpose(&self->sprite_buffer, sprite->size);
    } break;
    case CARDINAL_E: {
      // No transformation
    } break;
    case CARDINAL_S: {
      surface_transpose(&self->sprite_buffer, sprite->size);
    } break;
    case CARDINAL_W: {
      surface_mirror(&self->sprite_buffer, sprite->size);
    } break;
    }

    surface_apply_pallete(&self->sprite_buffer, sprite->size, DEFAULT_PALLETES.persona);
    renderer_draw_from_sprite_buffer(self, sprite->location, sprite->size);
  } break;
  case RENDER_ERASE: {
    renderer_sprite_fill(self, sprite->location, sprite->size, 0x00000000, false);
  } break;
  }
}

void renderer_sprite_buffer_map_to(renderer_s *self, const Pair_uint32 sprite_offset, const uint8_t size) {

  for (uint32_t row = 0; row < size; ++row) {
    size_t buffer_offset = Pair_uint32_flatten(&self->sprite_buffer.dimensions, row, 0);
    size_t sheet_offset = Pair_uint32_flatten(&self->sheet.dimensions, sprite_offset.x + row, sprite_offset.y);

    memcpy(&self->sprite_buffer.pixels[buffer_offset], &self->sheet.pixels[sheet_offset], size * sizeof(*self->sprite_buffer.pixels));
  }
}

void renderer_draw_from_sprite_buffer(renderer_s *self, const Pair_uint32 destination, const uint32_t size) {
  size_t pixel_fb;
  size_t pixel_s;
  uint32_t centre_offset = renderer_centre_offset(size);

  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {
      pixel_fb = Pair_uint32_flatten(&self->frame_buffer.dimensions,
                                     destination.x + row - centre_offset,
                                     destination.y + col - centre_offset);

      if (self->frame_buffer.pixels[pixel_fb] == 0x00000000) {
        pixel_s = Pair_uint32_flatten(&self->sprite_buffer.dimensions, row, col);
        self->frame_buffer.pixels[pixel_fb] = self->sprite_buffer.pixels[pixel_s];
      }
    }
  }
}

void renderer_sprite_fill(renderer_s *self, const Pair_uint32 location, const uint32_t size, const uint32_t colour, const bool edge) {
  uint32_t centre_offset = renderer_centre_offset(size);

  Pair_uint32 location_offset = {.x = location.x - centre_offset + (edge ? 0 : 1),
                                 .y = location.y - centre_offset + (edge ? 0 : 1)};

  surface_fill_tile(&self->frame_buffer, location_offset, size - (edge ? 0 : 2), colour);
}
