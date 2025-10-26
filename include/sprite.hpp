#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>
#include <cstdint>
#include <filesystem>
#include <string>

#include <png.h>

#include "utils.hpp"

struct Sprite {

  Size size;
  Position position{0, 0};
  int32_t *pixels{nullptr};

  ~Sprite() {}

  Sprite(std::filesystem::path path) {
    png_image image;

    memset(&image, 0, (sizeof image));
    image.version = PNG_IMAGE_VERSION;

    if (png_image_begin_read_from_file(&image, path.c_str()) != 0) {
      image.format = PNG_FORMAT_RGBA;

      this->size.elements.push_back(image.width);
      this->size.elements.push_back(image.height);

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

  std::string stringProjection() {
    std::string out{};

    for (int x{0}; x < this->size.y(); ++x) {
      for (int y{0}; y < this->size.x(); ++y) {
        if ((this->pixels)[x * this->size.x() + y] != 0x00000000) {
          out.push_back('#');
        } else {
          out.push_back(' ');
        }
      }
      out.push_back('\n');
    }

    return out;
  }
};
