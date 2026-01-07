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
  Pair_uint32 pixel_dimensions = {.x = maze_dimensions.x * TILE_PIXELS, .y = (maze_dimensions.y + (RENDER_TOP + RENDER_BOT)) * TILE_PIXELS};

  *renderer = (Renderer){
      .frame_buffer = {.size = pixel_dimensions,
                       .pixels = malloc(pixel_dimensions.x * pixel_dimensions.y * sizeof(*renderer->frame_buffer.pixels))},
      .sprite_buffer = {.size = {SPRITE_BUFFER_SIZE, SPRITE_BUFFER_SIZE},
                        .pixels = malloc(SPRITE_BUFFER_SIZE * SPRITE_BUFFER_SIZE * sizeof(*renderer->sprite_buffer.pixels))},
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

void Renderer_draw_maze(Renderer *self, const Maze *maze) {
  // For each tile...

  for (uint8_t col = 0; col < maze->size.x; ++col) {
    uint32_t col_scaled = (col * TILE_PIXELS);

    for (uint8_t row = 0; row < maze->size.y; ++row) {
      uint32_t row_scaled = ((row + RENDER_TOP) * TILE_PIXELS);
      Pair_uint32 tile_position = {.x = col_scaled, .y = row_scaled};

      TileData *tile_data = Maze_tile_data_at(maze, col, row);

      switch (tile_data->type) {

      case TILE_EDGE: {

        switch (tile_data->value.edge_value.edge_style) {

        case TILE_STYLE_NONE: {
        } break;

        case TILE_STYLE_LINE: {
          Plane plane = tile_data->value.edge_value.edge_line_plane;

          uint32_t adjustment;
          switch (tile_data->value.edge_value.lines) {
          case TILE_LINES_INNER: {
            adjustment = MAZE_INDENT - 1;
          } break;
          case TILE_LINES_OUTER: {
            adjustment = MAZE_INDENT;
          } break;
          }

          switch (plane) {
          case PLANE_H: {
            Surface_tile_line(&self->frame_buffer, col_scaled, row_scaled + adjustment, plane, TILE_PIXELS, 0xffffffff);
          } break;
          case PLANE_V: {
            Surface_tile_line(&self->frame_buffer, col_scaled + adjustment, row_scaled, plane, TILE_PIXELS, 0xffffffff);
          } break;
          }

          switch (plane) {
          case PLANE_H: {

            Surface_tile_line(&self->frame_buffer, col_scaled, row_scaled + adjustment, plane, TILE_PIXELS, 0xffffffff);

          } break;
          case PLANE_V: {

            Surface_tile_line(&self->frame_buffer, col_scaled + adjustment, row_scaled, plane, TILE_PIXELS, 0xffffffff);

          } break;
          }

        } break;
        case TILE_STYLE_ARC: {
          Surface_tile_fixed_arc(&self->frame_buffer, tile_position, tile_data, 0xffffffff);
        } break;
        }

      } break;
      case TILE_EMPTY: {
        Surface_fill_tile(&self->frame_buffer, tile_position, TILE_PIXELS, 0x00000000);
      } break;

      case TILE_INFO: {
        Surface_fill_tile(&self->frame_buffer, tile_position, TILE_PIXELS, 0x00ffffff);
      } break;

      case TILE_PATH: {
        Surface_fill_tile(&self->frame_buffer, tile_position, TILE_PIXELS, 0x00000000);
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

void Renderer_anima(Renderer *self, const Anima *anima, Sprite *sprite, const RenderAction action) {

  switch (action) {
  case RENDER_DRAW: {
    Renderer_sprite_buffer_map_to(self, Sheet_anima_offset(anima), sprite->sprite_size);
    Surface_apply_pallete(&self->sprite_buffer, sprite->sprite_size, DEFAULT_PALLETES.animas[anima->id]);

    Renderer_draw_from_sprite_buffer(self, sprite->sprite_location, sprite->sprite_size);
  } break;
  case RENDER_ERASE: {
    Renderer_sprite_fill(self, sprite->sprite_location, sprite->sprite_size, 0x00000000, false);
  } break;
  }
}

void Renderer_persona(Renderer *self, const Persona *persona, Sprite *sprite, const Situation *situation, const RenderAction action) {

  switch (action) {
  case RENDER_DRAW: {
    Renderer_sprite_buffer_map_to(self, Sheet_persona_offset(persona, situation), sprite->sprite_size);

    switch (situation->persona.direction_actual) {
    case DIRECTION_NONE: {
      // No transformation
    } break;
    case DIRECTION_N: {
      Surface_mirror(&self->sprite_buffer, sprite->sprite_size);
      Surface_transpose(&self->sprite_buffer, sprite->sprite_size);
    } break;
    case DIRECTION_E: {
      // No transformation
    } break;
    case DIRECTION_S: {
      Surface_transpose(&self->sprite_buffer, sprite->sprite_size);
    } break;
    case DIRECTION_W: {
      Surface_mirror(&self->sprite_buffer, sprite->sprite_size);
    } break;
    }

    Surface_apply_pallete(&self->sprite_buffer, sprite->sprite_size, DEFAULT_PALLETES.persona);
    Renderer_draw_from_sprite_buffer(self, sprite->sprite_location, sprite->sprite_size);
  } break;
  case RENDER_ERASE: {
    Renderer_sprite_fill(self, sprite->sprite_location, sprite->sprite_size, 0x00000000, false);
  } break;
  }
}

void Renderer_sprite_buffer_map_to(Renderer *self, const Pair_uint32 sprite_offset, const uint8_t size) {

  for (uint32_t row = 0; row < size; ++row) {
    uint32_t pre_offset = Surface_offset(&self->sprite_buffer, 0, row);
    uint32_t sheet_offset = Surface_offset(&self->sheet, sprite_offset.x, sprite_offset.y + row);

    memcpy(&self->sprite_buffer.pixels[pre_offset], &self->sheet.pixels[sheet_offset], size * sizeof(*self->sprite_buffer.pixels));
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
        pixel_s = Surface_offset(&self->sprite_buffer, col, row);
        self->frame_buffer.pixels[pixel_fb] = self->sprite_buffer.pixels[pixel_s];
      }
    }
  }
}

void Renderer_sprite_fill(Renderer *self, const Pair_uint32 location, const uint32_t size, const uint32_t colour, const bool edge) {
  uint32_t centre_offset = Renderer_centre_offset(size);

  Pair_uint32 location_offset = {.x = location.x - centre_offset + (edge ? 0 : 1),
                                 .y = location.y - centre_offset + (edge ? 0 : 1)};

  Surface_fill_tile(&self->frame_buffer, location_offset, size - (edge ? 0 : 2), colour);
}
