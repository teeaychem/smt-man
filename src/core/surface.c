#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#include "constants.h"
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

void Surface_fill_tile(Surface *self, const Pair_uint32 destination, const uint32_t size, const uint32_t colour) {
  for (uint32_t i = 0; i < size; ++i) {
    for (uint32_t j = 0; j < size; ++j) {
      self->pixels[Surface_offset(self, destination.x + j, destination.y + i)] = colour;
    }
  }
}

void Surface_tile_line(Surface *self, const uint32_t x, const uint32_t y, const Plane plane, const uint32_t length, const uint32_t colour) {

  switch (plane) {
  case PLANE_H: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->pixels[Surface_offset(self, x + idx, y)] = colour;
    }
  } break;
  case PLANE_V: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->pixels[Surface_offset(self, x, y + idx)] = colour;
    }
  } break;
  }
}

void Surface_circle_draw(Surface *self, Pair_uint32 *origin, Pair_uint32 *offset, Quadrant quadrant, uint32_t colour) {

  switch (quadrant) {

  case QUADRANT_1: {
    uint32_t pixel_a = Surface_offset(self, origin->x + offset->x, origin->y - offset->y);
    self->pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(self, origin->x + offset->y, origin->y - offset->x);
    self->pixels[pixel_b] = colour;
  } break;
  case QUADRANT_2: {
    uint32_t pixel_a = Surface_offset(self, origin->x - offset->y, origin->y - offset->x);
    self->pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(self, origin->x - offset->x, origin->y - offset->y);
    self->pixels[pixel_b] = colour;
  } break;
  case QUADRANT_3: {
    uint32_t pixel_a = Surface_offset(self, origin->x - offset->x, origin->y + offset->y);
    self->pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(self, origin->x - offset->y, origin->y + offset->x);
    self->pixels[pixel_b] = colour;
  } break;
  case QUADRANT_4: {
    uint32_t pixel_a = Surface_offset(self, origin->x + offset->x, origin->y + offset->y);
    self->pixels[pixel_a] = colour;

    uint32_t pixel_b = Surface_offset(self, origin->x + offset->y, origin->y + offset->x);
    self->pixels[pixel_b] = colour;

  } break;
  }
}

void Surface_tile_arc(Surface *self, const Pair_uint32 origin, const uint32_t radius, const Quadrant quadrant, const uint32_t colour) {

  assert(radius <= INT32_MAX);

  Pair_uint32 offset = {.x = 0, .y = radius};

  Pair_uint32 origin_offset = origin;

  switch (quadrant) {
  case QUADRANT_1: {
    origin_offset.y += (TILE_PIXELS - 1);
  } break;
  case QUADRANT_2: {
    origin_offset.x += (TILE_PIXELS - 1);
    origin_offset.y += (TILE_PIXELS - 1);
  } break;
  case QUADRANT_3: {
    origin_offset.x += (TILE_PIXELS - 1);
  } break;
  case QUADRANT_4: {
  } break;
  }

  int32_t direction_relative = 1 - (int32_t)radius;
  int32_t turn_left = 3;
  int32_t turn_right = -((int32_t)radius << 1) + 5;

  Surface_circle_draw(self, &origin_offset, &offset, quadrant, colour);
  while (offset.y > offset.x) {
    if (direction_relative <= 0) {
      direction_relative += turn_left;
    } else {
      direction_relative += turn_right;
      turn_right += 2;
      offset.y -= 1;
    }
    turn_left += 2;
    turn_right += 2;
    offset.x += 1;

    Surface_circle_draw(self, &origin_offset, &offset, quadrant, colour);
  }
}

void Surface_tile_fixed_arc_length(Surface *self, const Pair_uint32 origin, const TileData *tile_data, const uint32_t colour, uint32_t length) {
  uint32_t corner_y_12 = origin.y + (TILE_PIXELS - (length + 1));
  uint32_t corner_y_34 = origin.y + length;

  uint32_t corner_x_23 = origin.x + (TILE_PIXELS - (length + 1));
  uint32_t corner_x_14 = origin.x + length;

  switch (tile_data->value.edge_value.edge_arc_quadrant) {
  case QUADRANT_1: {
    Surface_tile_line(self, origin.x, corner_y_12 - 1, PLANE_H, length, colour);
    Surface_tile_line(self, corner_x_14 + 1, corner_y_12 + 1, PLANE_V, length, colour);
    Surface_tile_line(self, corner_x_14, corner_y_12, PLANE_H, 1, colour);
  } break;

  case QUADRANT_2: {
    Surface_tile_line(self, corner_x_23 + 1, corner_y_12 - 1, PLANE_H, length, colour);
    Surface_tile_line(self, corner_x_23 - 1, corner_y_12 + 1, PLANE_V, length, colour);
    Surface_tile_line(self, corner_x_23, corner_y_12, PLANE_H, 1, colour);
  } break;

  case QUADRANT_3: {
    Surface_tile_line(self, corner_x_23 + 1, corner_y_34 + 1, PLANE_H, length, colour);
    Surface_tile_line(self, corner_x_23 - 1, origin.y, PLANE_V, length, colour);
    Surface_tile_line(self, corner_x_23, corner_y_34, PLANE_H, 1, colour);
  } break;

  case QUADRANT_4: {
    Surface_tile_line(self, origin.x, corner_y_34 + 1, PLANE_H, length, colour);
    Surface_tile_line(self, corner_x_14 + 1, origin.y, PLANE_V, length, colour);
    Surface_tile_line(self, corner_x_14, corner_y_34, PLANE_H, 1, colour);
  } break;
  }
}

void Surface_tile_fixed_arc(Surface *self, const Pair_uint32 origin, const TileData *tile_data, const uint32_t colour) {

  if (tile_data->value.edge_value.lines == TILE_LINES_INNER) {
    Surface_tile_fixed_arc_length(self, origin, tile_data, colour, TILE_PIXELS / 4);
  }

  if (tile_data->value.edge_value.lines == TILE_LINES_OUTER) {
    Surface_tile_fixed_arc_length(self, origin, tile_data, colour, (TILE_PIXELS / 4) + 1);
  }
}
