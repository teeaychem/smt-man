#include <stdint.h>
#include <stdlib.h>

#include "render/surface.h"

void Surface_from_path(Surface *self, const char *path) {

  png_image image;

  memset(&image, 0, sizeof(image));
  image.version = PNG_IMAGE_VERSION;

  if (png_image_begin_read_from_file(&image, path)) {
    image.format = PNG_FORMAT_RGBA;

    self->size.x = image.width;
    self->size.y = image.height;
    self->pixels = malloc(PNG_IMAGE_SIZE(image));

    if (self->pixels != nullptr &&
        png_image_finish_read(&image, NULL, self->pixels, 0, nullptr) != 0) {
    } else {
      png_image_free(&image);
      free(self->pixels);
    }
  }
}

void Surface_destroy(Surface *self) {
  free(self->pixels);

  self->pixels = nullptr;
  self->size.x = 0;
  self->size.y = 0;
}

void Surface_char_projection(const Surface *self, char *destination, size_t *length) {

  size_t size = (self->size.x * (self->size.y + 1)) + 1;
  *length = size;

  destination = malloc(size * sizeof(*destination));
  memset(destination, ' ', size);
  destination[size - 1] = '\0';

  size_t idx = 0;
  for (uint32_t r = 0; r < self->size.y; ++r) {
    for (uint32_t c = 0; c < self->size.x; ++c, ++idx) {
      if ((self->pixels)[r * self->size.x + c] != 0x00000000) {
        destination[idx] = '#';
      }
    }
    destination[idx++] = '\n';
  }
}

void Surface_mirror_mut(Surface *self, const uint32_t size) {
  for (uint32_t i = 0; i < size; ++i) {
    for (uint32_t j = 0; j < size / 2; ++j) {
      uint32_t tmp = self->pixels[Surface_offset(self, j, i)];
      self->pixels[Surface_offset(self, j, i)] = self->pixels[Surface_offset(self, size - j - 1, i)];
      self->pixels[Surface_offset(self, size - j - 1, i)] = tmp;
    }
  }
}

void Surface_transpose_mut(Surface *self, const uint32_t size) {
  for (uint32_t i = 0; i < size; ++i) {
    for (uint32_t j = i + 1; j < size; ++j) {
      uint32_t tmp = self->pixels[Surface_offset(self, j, i)];
      self->pixels[Surface_offset(self, j, i)] = self->pixels[Surface_offset(self, i, j)];
      self->pixels[Surface_offset(self, i, j)] = tmp;
    }
  }
}

void Surface_pallete_mut(Surface *self, const uint32_t size, const Pallete pallete) {
  for (uint32_t i = 0; i < size; ++i) {
    for (uint32_t j = 0; j < size; ++j) {

      uint32_t pix = Surface_offset(self, j, i);

      /* if (self->pixels[pix] == 0x00000000) { */
      /* self->pixels[pix] = */

      self->pixels[pix] = Pallete_offset(self->pixels[pix], pallete);
      /* } */
    }
  }
}
