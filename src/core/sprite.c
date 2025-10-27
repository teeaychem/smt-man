#include "sprite.h"
#include <stdlib.h>

Sprite *Sprite_create(char *path) {

  Sprite *sprite = (Sprite *)malloc(sizeof(Sprite));

  png_image image;

  memset(&image, 0, (sizeof image));
  image.version = PNG_IMAGE_VERSION;

  if (png_image_begin_read_from_file(&image, path) != 0) {
    image.format = PNG_FORMAT_RGBA;

    sprite->size_w = image.width;
    sprite->size_h = image.height;

    sprite->pixels = (int32_t *)malloc(PNG_IMAGE_SIZE(image));

    if (sprite->pixels != NULL &&
        png_image_finish_read(&image, NULL, sprite->pixels, 0, NULL) != 0) {
    } else {
      if (sprite->pixels == NULL)
        png_image_free(&image);
      else {
        free(sprite->pixels);
      }
    }
  }

  return sprite;
}

int Sprite_char_projection(Sprite *sprite, char *dest, size_t *len) {

  int return_value = 1;

  size_t size = (sprite->size_w * (sprite->size_h + 1)) + 1;
  *len = size;

  dest = (char *)malloc(size);
  memset(dest, ' ', size);
  dest[size - 1] = '\0';

  size_t idx = 0;
  for (int r = 0; r < sprite->size_h; ++r) {
    for (int c = 0; c < sprite->size_w; ++c, ++idx) {
      if ((sprite->pixels)[r * sprite->size_w + c] != 0x00000000) {
        dest[idx] = '#';
      }
    }
    dest[idx++] = '\n';
  }

  return return_value;
}
