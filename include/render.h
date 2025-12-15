#pragma once

#include <stddef.h>
#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "generic/pairs.h"
#include "maze.h"
#include "render/palette.h"
#include "render/surface.h"

typedef struct renderer_t Renderer;
struct renderer_t {
  uint32_t scale;
  Surface sheet;
  Surface frame_buffer;

  SDL_Window *window;
  SDL_Renderer *renderer;
  SDL_Texture *texture;
};

void Renderer_create(Renderer *renderer, uint32_t scale, const Pair_uint8 maze_size, char *sheet_path);

void Renderer_destroy(Renderer *self);

void Renderer_update(Renderer *self);

void Renderer_fill_tile(Renderer *self, Pair_uint32 pos, uint32_t colour);

void Renderer_read_maze(Renderer *self, Maze *maze);

void Renderer_draw_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 offset, Pallete pallete);

void Renderer_erase_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 offset, Pallete pallete);
