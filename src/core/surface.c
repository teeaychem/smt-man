#include <stdint.h>
#include <stdlib.h>

#include "render/surface.h"

void Surface_from_path(Surface *self, char *path) {

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

void Surface_char_projection(Surface *self, char *dest, size_t *len) {

  size_t size = (self->size.x * (self->size.y + 1)) + 1;
  *len = size;

  dest = malloc(size * sizeof(*dest));
  memset(dest, ' ', size);
  dest[size - 1] = '\0';

  size_t idx = 0;
  for (uint32_t r = 0; r < self->size.y; ++r) {
    for (uint32_t c = 0; c < self->size.x; ++c, ++idx) {
      if ((self->pixels)[r * self->size.x + c] != 0x00000000) {
        dest[idx] = '#';
      }
    }
    dest[idx++] = '\n';
  }
}

inline uint32_t Surface_offset(Surface *self, uint32_t col, uint32_t row) {
  return (row * self->size.x) + col;
}
