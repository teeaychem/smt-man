#pragma once

#include <cstdint>

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include <png.h>

#include "utils/NVec.h"

struct Sprite {

  Size size{0, 0};
  Position position{0, 0};
  int32_t *pixels{nullptr};

  ~Sprite() {}

  Sprite(char *path) {

    png_image image;

    memset(&image, 0, (sizeof image));
    image.version = PNG_IMAGE_VERSION;

    if (png_image_begin_read_from_file(&image, path) != 0) {
      image.format = PNG_FORMAT_RGBA;

      this->size.elements[0] = image.width;
      this->size.elements[1] = image.height;
      printf("x: %d%d", this->size.elements[0], this->size.elements[1]);

      pixels = (int32_t *)malloc(PNG_IMAGE_SIZE(image));

      if (pixels != nullptr &&
          png_image_finish_read(&image, nullptr, pixels, 0, nullptr) != 0) {
      } else {
        if (pixels == nullptr)
          png_image_free(&image);
        else {
          free(pixels);
        }
      }
    }
  }

  char *charProjection() {

    size_t space_required = (this->size.x() * (this->size.y() + 1)) + 1;
    char *out = (char *)malloc(space_required);
    memset(out, ' ', space_required);
    out[space_required - 1] = '\0';

    size_t idx{0};
    for (int r{0}; r < this->size.y(); ++r) {
      for (int c{0}; c < this->size.x(); ++c, ++idx) {
        if ((this->pixels)[r * this->size.x() + c] != 0x00000000) {
          out[idx] = '#';
        }
      }
      out[idx++] = '\n';
    }

    return out;
  }
};
