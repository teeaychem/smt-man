#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

#include "consts.h"
#include "render/surface.h"

void surface_ctor(surface_s *self, const char *path) {

  png_image image;

  memset(&image, 0, sizeof(image));
  image.version = PNG_IMAGE_VERSION;

  if (png_image_begin_read_from_file(&image, path)) {
    image.format = PNG_FORMAT_RGBA;

    self->dimensions = (Pair_uint32){
        .x = image.height,
        .y = image.width,
    };

    self->pixels = malloc(PNG_IMAGE_SIZE(image));

    if (self->pixels != nullptr &&
        png_image_finish_read(&image, NULL, self->pixels, 0, nullptr) != 0) {
    } else {
      png_image_free(&image);
      free(self->pixels);
      panic(true, "Failed to create surface", -1);
    }
  }
}

void surface_dtor(surface_s *self) {
  free(self->pixels);

  self->pixels = nullptr;
  self->dimensions.x = 0;
  self->dimensions.y = 0;
}

void surface_char_projection(const surface_s *self, char **destination, size_t *length) {

  size_t size = (self->dimensions.x * (self->dimensions.y + 2)) + 1;
  *length = size;

  char *buffer = malloc(size * sizeof(*buffer));
  memset(buffer, ' ', size);
  buffer[size - 1] = '\0';

  size_t idx = 0;
  for (uint32_t row = 0; row < self->dimensions.x; ++row) {
    for (uint32_t col = 0; col < self->dimensions.y; ++col, ++idx) {
      if (self->pixels[Pair_uint32_flatten(&self->dimensions, row, col)] != 0x00000000) {
        buffer[idx] = '#';
      }
    }
    buffer[idx++] = '|';
    buffer[idx++] = '\n';
  }

  *destination = buffer;
}

void surface_stdout(const surface_s *self) {

  size_t length = 0;
  char *buffer = nullptr;
  surface_char_projection(self, &buffer, &length);
  printf("%s", buffer);
  free(buffer);
}

void surface_mirror(surface_s *self, const uint32_t size) {
  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size / 2; ++col) {
      uint32_t tmp = self->pixels[Pair_uint32_flatten(&self->dimensions, row, col)];
      self->pixels[Pair_uint32_flatten(&self->dimensions, row, col)] = self->pixels[Pair_uint32_flatten(&self->dimensions, row, size - col - 1)];
      self->pixels[Pair_uint32_flatten(&self->dimensions, row, size - col - 1)] = tmp;
    }
  }
}

void surface_transpose(surface_s *self, const uint32_t size) {
  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = row + 1; col < size; ++col) {
      uint32_t tmp = self->pixels[Pair_uint32_flatten(&self->dimensions, row, col)];
      self->pixels[Pair_uint32_flatten(&self->dimensions, row, col)] = self->pixels[Pair_uint32_flatten(&self->dimensions, col, row)];
      self->pixels[Pair_uint32_flatten(&self->dimensions, col, row)] = tmp;
    }
  }
}

void surface_apply_pallete(surface_s *self, const uint32_t size, const Pallete pallete) {
  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {
      size_t pix = Pair_uint32_flatten(&self->dimensions, row, col);
      Pallete_apply(&self->pixels[pix], pallete);
    }
  }
}

void surface_fill_tile(surface_s *self, const Pair_uint32 destination, const uint32_t size, const uint32_t colour) {
  for (uint32_t row = 0; row < size; ++row) {
    for (uint32_t col = 0; col < size; ++col) {
      self->pixels[Pair_uint32_flatten(&self->dimensions, destination.x + row, destination.y + col)] = colour;
    }
  }
}

void surface_tile_line(surface_s *self, const uint32_t row, const uint32_t col, const plane_e plane, const uint32_t length, const uint32_t colour) {

  switch (plane) {
  case PLANE_H: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->pixels[Pair_uint32_flatten(&self->dimensions, row, col + idx)] = colour;
    }
  } break;
  case PLANE_V: {
    for (uint32_t idx = 0; idx < length; ++idx) {
      self->pixels[Pair_uint32_flatten(&self->dimensions, row + idx, col)] = colour;
    }
  } break;
  }
}

void surface_circle_draw(surface_s *self, const Pair_uint32 *origin, const Pair_uint32 *offset, const quadrant_e quadrant, const uint32_t colour) {

  switch (quadrant) {

  case QUADRANT_1: {
    size_t pixel_a = Pair_uint32_flatten(&self->dimensions, origin->x + offset->x, origin->y - offset->y);
    self->pixels[pixel_a] = colour;

    size_t pixel_b = Pair_uint32_flatten(&self->dimensions, origin->x + offset->y, origin->y - offset->x);
    self->pixels[pixel_b] = colour;
  } break;

  case QUADRANT_2: {
    size_t pixel_a = Pair_uint32_flatten(&self->dimensions, origin->x - offset->y, origin->y - offset->x);
    self->pixels[pixel_a] = colour;

    size_t pixel_b = Pair_uint32_flatten(&self->dimensions, origin->x - offset->x, origin->y - offset->y);
    self->pixels[pixel_b] = colour;
  } break;

  case QUADRANT_3: {
    size_t pixel_a = Pair_uint32_flatten(&self->dimensions, origin->x - offset->x, origin->y + offset->y);
    self->pixels[pixel_a] = colour;

    size_t pixel_b = Pair_uint32_flatten(&self->dimensions, origin->x - offset->y, origin->y + offset->x);
    self->pixels[pixel_b] = colour;
  } break;

  case QUADRANT_4: {
    size_t pixel_a = Pair_uint32_flatten(&self->dimensions, origin->x + offset->x, origin->y + offset->y);
    self->pixels[pixel_a] = colour;

    size_t pixel_b = Pair_uint32_flatten(&self->dimensions, origin->x + offset->y, origin->y + offset->x);
    self->pixels[pixel_b] = colour;
  } break;
  }
}

void surface_tile_arc(surface_s *self, const Pair_uint32 origin, const uint32_t radius, const quadrant_e quadrant, const uint32_t colour) {

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

  surface_circle_draw(self, &origin_offset, &offset, quadrant, colour);
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

    surface_circle_draw(self, &origin_offset, &offset, quadrant, colour);
  }
}

void surface_tile_fixed_arc(surface_s *self, const Pair_uint32 origin, const tile_data_s *tile_data, const uint32_t colour) {

  uint32_t half_pixels = TILE_PIXELS / 2;

  switch (tile_data->value.edge_value.lines) {

  case TILE_LINES_P: {

    uint32_t length = TILE_PIXELS / 4;

    switch (tile_data->value.edge_value.edge_arc_quadrant) {
    case QUADRANT_1: {
      surface_tile_line(self, origin.x + half_pixels, origin.y, PLANE_H, length, colour);
      surface_tile_line(self, origin.x + half_pixels + 2, origin.y + length + 1, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels + 1, origin.y + length, PLANE_H, 1, colour);
    } break;

    case QUADRANT_2: {
      surface_tile_line(self, origin.x + half_pixels, origin.y + half_pixels + 2, PLANE_H, length, colour);
      surface_tile_line(self, origin.x + half_pixels + 2, origin.y + half_pixels, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels + 1, origin.y + half_pixels + 1, PLANE_H, 1, colour);
    } break;

    case QUADRANT_3: {
      surface_tile_line(self, origin.x + half_pixels - 1, origin.y + half_pixels + 2, PLANE_H, length, colour);
      surface_tile_line(self, origin.x, origin.y + half_pixels, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels - 2, origin.y + half_pixels + 1, PLANE_H, 1, colour);
    } break;

    case QUADRANT_4: {
      surface_tile_line(self, origin.x + half_pixels - 1, origin.y, PLANE_H, length, colour);
      surface_tile_line(self, origin.x, origin.y + half_pixels - 1, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels - 2, origin.y + 2, PLANE_H, 1, colour);
    } break;
    }
  } break;
  case TILE_LINES_M: {

    uint32_t length = (TILE_PIXELS / 4) + 1;

    switch (tile_data->value.edge_value.edge_arc_quadrant) {

    case QUADRANT_1: {
      surface_tile_line(self, origin.x + half_pixels - 1, origin.y, PLANE_H, length, colour);
      surface_tile_line(self, origin.x + half_pixels + 1, origin.y + length + 1, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels, origin.y + length, PLANE_H, 1, colour);
    } break;

    case QUADRANT_2: {
      surface_tile_line(self, origin.x + half_pixels - 1, origin.y + half_pixels + 1, PLANE_H, length, colour);
      surface_tile_line(self, origin.x + half_pixels + 1, origin.y + half_pixels - 1, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels, origin.y + half_pixels, PLANE_H, 1, colour);
    } break;

    case QUADRANT_3: {
      surface_tile_line(self, origin.x + half_pixels, origin.y + half_pixels + 1, PLANE_H, length, colour);
      surface_tile_line(self, origin.x, origin.y + half_pixels - 1, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels - 1, origin.y + half_pixels, PLANE_H, 1, colour);
    } break;

    case QUADRANT_4: {
      surface_tile_line(self, origin.x + half_pixels, origin.y, PLANE_H, length, colour);
      surface_tile_line(self, origin.x, origin.y + half_pixels, PLANE_V, length, colour);
      surface_tile_line(self, origin.x + half_pixels - 1, origin.y + length, PLANE_H, 1, colour);
    } break;
    }

  } break;
  }
}
