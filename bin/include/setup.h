#pragma once

#include "SML/maze.h"

#include "render.h"

/// Setup functions
///
/// Called by main.

struct spirit_setup_t {
  pthread_cond_t cond_frame;
  pthread_mutex_t mtx_spirit;

  anima_s *anima;
  size_t anima_count;
  const maze_s *maze;
  const char *source_path;
  Situation *situation;
  pthread_t *thread;
};
typedef struct spirit_setup_t spirit_setup_s;

void source_path_build(char **source_path, int *length);

void setup_renderer(Renderer *renderer, const maze_s *maze, const char *source_path);

void *spirit_ctor(void *void_setup_struct);
