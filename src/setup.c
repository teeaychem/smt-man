/// Generic struct setup

#define PAIR_IMPLEMENTATION
#include "pairs.h"
#undef PAIR_IMPLEMENTATION

/// Other setup

#include "setup.h"

#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

#include "cwalk.h"
#include <whereami.h>

// Set the source path for resources, etc.
char *setup_source_path() {
  int source_path_size = wai_getExecutablePath(nullptr, 0, nullptr) + 1;
  char *source_path = malloc((size_t)source_path_size * sizeof(*source_path));

  int dirname_length;
  wai_getExecutablePath(source_path, source_path_size - 1, &dirname_length);

  source_path[dirname_length] = '\0';

  return source_path;
}

Maze setup_maze(char *source_path) {
  char path_buffer[FILENAME_MAX];
  cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
  return Maze_create(path_buffer);
}

void setup_anima(char *source_path, Anima animas[ANIMA_COUNT], SpriteInfo anima_sprites[ANIMA_COUNT], uint8_t id, Pair_uint8 location) {
  animas[id] = Anima_create(id, location, DOWN, DOWN, PAIR_SPRITE_EDGE);

  char path_b[40];
  char path_buffer[FILENAME_MAX];

  sprintf(path_b, "resources/%s.png", animas[id].name);
  cwk_path_join(source_path, path_b, path_buffer, FILENAME_MAX);

  anima_sprites[id] = (SpriteInfo){
      .size = PAIR_SPRITE_EDGE,
      .surface = Surface_from_path(path_buffer),
      .surface_offset = Pair_uint32_create(0, 0),
  };
  pthread_create(&ANIMA_THREADS[id], nullptr, setup_spirit, (void *)&animas[id]);
}
void *setup_spirit(void *void_anima) {

  Anima *anima = void_anima;
  Mind mind = Mind_default();

  pthread_mutex_lock(&MTX_SOLVER);
  Anima_touch(anima, &mind);
  pthread_mutex_unlock(&MTX_SOLVER);

  atomic_store(&anima->sync.flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->sync.mtx_suspend);
    if (!atomic_load(&anima->sync.flag_suspend)) {
      Anima_deduct(anima, &mind);

      sleep(1);
      atomic_store(&anima->sync.flag_suspend, true);
    }
    pthread_cond_wait(&anima->sync.cond_resume, &anima->sync.mtx_suspend);
    pthread_mutex_unlock(&anima->sync.mtx_suspend);
  }
  return 0;
}
