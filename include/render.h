#pragma once

#include <stddef.h>
#include <stdint.h>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "generic/pairs.h"
#include "maze.h"
#include "render/surface.h"

struct sheet_offsets_t {
  struct {
    uint32_t size;
    Pair_uint32 rt[2];
    Pair_uint32 dn[2];
    Pair_uint32 lt[2];
    Pair_uint32 up[2];

  } anima;
};
typedef struct sheet_offsets_t Sheetoffsets;

extern Sheetoffsets sheet_offsets;

typedef struct renderer_t Renderer;
struct renderer_t {
  Surface sheet;
  Surface frame_buffer;

  SDL_Window *window;
  SDL_Renderer *renderer;
  SDL_Texture *texture;
};

Renderer Renderer_create(const Pair_uint32 dimensions, Surface sheet);

void Renderer_destroy(Renderer *self);

void Renderer_update(Renderer *self);

void Renderer_fill_tile(Renderer *self, Pair_uint32 pos, uint32_t colour);

void Renderer_read_maze(Renderer *self, Maze *maze);

void Renderer_draw_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 *offset);

void Renderer_erase_from_sheet(Renderer *self, Pair_uint32 location, uint32_t size, Pair_uint32 *offset);
