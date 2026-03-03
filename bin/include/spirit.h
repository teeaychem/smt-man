#pragma once

#include <pthread.h>

#include "SML/logic/situation.h"
#include "SML/maze.h"

#include "sprite/anima.h"

struct spirit_setup_t {
  bool *hold;
  pthread_cond_t cond_held;
  pthread_mutex_t mtx_held;

  pthread_cond_t cond_frame;

  pthread_mutex_t mtx_spirit;

  anima_s *anima;
  size_t anima_count;
  const maze_s *maze;
  const char *source_path;
  situation_s *the_situation;
  pthread_t *thread;
};
typedef struct spirit_setup_t spirit_setup_s;

void *spirit_ctor(void *void_setup_struct);
