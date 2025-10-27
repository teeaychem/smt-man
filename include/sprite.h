#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <png.h>

struct sprite_t {
  int32_t size_w;
  int32_t size_h;

  int32_t pos_x;
  int32_t pos_y;

  int32_t *pixels;
};

typedef struct sprite_t Sprite;

#ifdef __cplusplus
extern "C" {
#endif

Sprite Sprite_create(char *path);
void Sprite_destroy(Sprite *path);

int Sprite_char_projection(Sprite *sprite, char *dest, size_t *len);

#ifdef __cplusplus
}
#endif
