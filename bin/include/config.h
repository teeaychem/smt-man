#pragma once

#include <assert.h>
#include <stdlib.h>

#include <cwalk.h>
#include <whereami.h>

/*
  Take a copy of the situation for a solve.
  There's no need to update the situation after, as this is handled by reading from a the anima's path
 */

// Set the source path for resources, etc.
static inline void source_path_build(char **source_path, int *length) {

  *length = wai_getExecutablePath(nullptr, 0, nullptr) + 1;
  assert(*length >= 0);
  *source_path = malloc((size_t)*length * sizeof(*source_path));

  int dirname_length;
  wai_getExecutablePath(*source_path, *length - 1, &dirname_length);
  (*source_path)[dirname_length] = '\0';
}
