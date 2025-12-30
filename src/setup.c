/// Generic struct setup
#define ARITHMETIC_IMPLEMENTATION
#include "generic/arithmetic.h"
#undef ARITHMETIC_IMPLEMENTATION

#define BITVEC_IMPLEMENTATION
#include "generic/bitvec.h"
#undef BITVEC_IMPLEMENTATION

#define PAIR_IMPLEMENTATION
#include "generic/pairs.h"
#undef PAIR_IMPLEMENTATION

/// Other setup
#include "setup.h"

#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

#include <cwalk.h>
#include <whereami.h>

#include "constants.h"

// Private

// Set the source path for resources, etc.
void setup_source_path(char **source_path) {

  int source_path_size = wai_getExecutablePath(nullptr, 0, nullptr) + 1;
  *source_path = malloc((size_t)source_path_size * sizeof(*source_path));

  int dirname_length;
  wai_getExecutablePath(*source_path, source_path_size - 1, &dirname_length);
  (*source_path)[dirname_length] = '\0';
}

void setup_maze(Maze *maze, char *source_path) {

  char path_buffer[FILENAME_MAX];
  cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
  Maze_create(maze, path_buffer);
  Maze_detail(maze);
}

void *setup_spirit(void *void_anima) {

  Anima *anima = void_anima;

  Mind_touch(&anima->mind);

  atomic_store(&anima->contact.flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->contact.mtx_suspend);
    if (!atomic_load(&anima->contact.flag_suspend)) {
      Mind_deduct(&anima->mind);
      atomic_store(&anima->contact.flag_suspend, true);
    }
    pthread_cond_wait(&anima->contact.cond_resume, &anima->contact.mtx_suspend);
    pthread_mutex_unlock(&anima->contact.mtx_suspend);
  }
  return 0;
}

void setup_anima(Anima animas[ANIMA_COUNT], uint8_t id, Pair_uint8 location) {

  Anima_default(&animas[id], id, 16, location, DIRECTION_S);
  pthread_create(&ANIMA_THREADS[id], nullptr, setup_spirit, (void *)&animas[id]);
}

// Public

void setup_resources(Renderer *renderer, Maze *maze) { // Resource setup
  char *source_path;

  setup_source_path(&source_path);

  setup_maze(maze, source_path);

  { // Renderer
    char path_buffer[FILENAME_MAX];
    cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);

    Renderer_create(renderer, maze->size, path_buffer);
  }

  free(source_path);
}

void setup_animas(Anima animas[ANIMA_COUNT]) { // Resource setup

  setup_anima(animas, 0, Pair_uint8_create(1, 4));
  animas[0].pallete = (Pallete){
      .a = 0x00000000,
      .b = 0x00000000,
      .c = 0x00000000,
      .d = 0xffff00ff,
  };

  setup_anima(animas, 1, Pair_uint8_create(16, 26));
  animas[1].pallete = (Pallete){
      .a = 0x00000000,
      .b = 0x00000000,
      .c = 0x00000000,
      .d = 0xffffbb00,
  };

  setup_anima(animas, 2, Pair_uint8_create(21, 12));
  animas[2].pallete = (Pallete){
      .a = 0x00000000,
      .b = 0x00000000,
      .c = 0x00000000,
      .d = 0xfa8072ff,
  };

  setup_anima(animas, 3, Pair_uint8_create(4, 29));
  animas[3].pallete = (Pallete){
      .a = 0x00000000,
      .b = 0x00000000,
      .c = 0x00000000,
      .d = 0xff808080,
  };
}
