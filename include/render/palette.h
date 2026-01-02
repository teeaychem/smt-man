#pragma once

#include "constants.h"
#include <stdint.h>

struct pallete_t {
  uint32_t a;
  uint32_t b;
  uint32_t c;
  uint32_t d;
};
typedef struct pallete_t Pallete;

/// Default palettes

struct palletes_t {
  Pallete persona;
  Pallete animas[ANIMA_COUNT];
};

typedef struct palletes_t Palletes;

#ifdef PALETTE_IMPLEMENTATION

const Palletes DEFAULT_PALLETES = {
    .persona = {
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xff00ffff,
    },
    .animas = {{
                   .a = 0x00000000,
                   .b = 0x00000000,
                   .c = 0x00000000,
                   .d = 0xffff00ff,
               },
               {
                   .a = 0x00000000,
                   .b = 0x00000000,
                   .c = 0x00000000,
                   .d = 0xffffbb00,
               },
               {
                   .a = 0x00000000,
                   .b = 0x00000000,
                   .c = 0x00000000,
                   .d = 0xfa8072ff,
               },
               {
                   .a = 0x00000000,
                   .b = 0x00000000,
                   .c = 0x00000000,
                   .d = 0xff808080,
               }},
};

#endif

#ifndef PALETTE_IMPLEMENTATION
const extern Palletes DEFAULT_PALLETES;
#endif

/// Palette methods

static inline uint32_t Pallete_offset(const uint32_t pixel, const Pallete pallete) {
  uint32_t colour;
  switch (pixel) {
  case 0x000000ff: {
    colour = pallete.a;
  } break;
  case 0xdedeffff: {
    colour = pallete.b;
  } break;
  case 0x2121ffff: {
    colour = pallete.c;
  } break;
  case 0xff0000ff: {
    colour = pallete.d;
  } break;
  default:
    /* printf("Missed: %#010x\n", pixel); */
    colour = pixel;
  }
  return colour;
}

static inline void Pallete_apply(uint32_t *pixel, const Pallete pallete) {
  switch (*pixel) {
  case 0x000000ff: {
    *pixel = pallete.a;
  } break;
  case 0xdedeffff: {
    *pixel = pallete.b;
  } break;
  case 0x2121ffff: {
    *pixel = pallete.c;
  } break;
  case 0xff0000ff: {
    *pixel = pallete.d;
  } break;
  default:
    // No action
  }
}
