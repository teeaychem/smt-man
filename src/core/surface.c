#include "surface.h"
#include <stdint.h>
#include <stdlib.h>

Surface Surface_from_path(char *path) {

  Surface surface;

  png_image image;

  memset(&image, 0, sizeof(image));
  image.version = PNG_IMAGE_VERSION;

  if (png_image_begin_read_from_file(&image, path) != 0) {
    image.format = PNG_FORMAT_RGBA;

    surface.size.x = image.width;
    surface.size.y = image.height;

    surface.pixels = malloc(PNG_IMAGE_SIZE(image) * sizeof(*surface.pixels));

    if (surface.pixels != NULL &&
        png_image_finish_read(&image, NULL, surface.pixels, 0, NULL) != 0) {
    } else {
      if (surface.pixels == NULL)
        png_image_free(&image);
      else {
        free(surface.pixels);
      }
    }
  }

  return surface;
}

void Surface_destroy(Surface *self) {
  free(self->pixels);
}

int Surface_char_projection(Surface *surface, char *dest, size_t *len) {

  int return_value = 1;

  size_t size = (surface->size.x * (surface->size.y + 1)) + 1;
  *len = size;

  dest = malloc(size * sizeof(*dest));
  memset(dest, ' ', size);
  dest[size - 1] = '\0';

  size_t idx = 0;
  for (int r = 0; r < surface->size.y; ++r) {
    for (int c = 0; c < surface->size.x; ++c, ++idx) {
      if ((surface->pixels)[r * surface->size.x + c] != 0x00000000) {
        dest[idx] = '#';
      }
    }
    dest[idx++] = '\n';
  }

  return return_value;
}
