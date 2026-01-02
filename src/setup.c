/// Generic struct setup
#include "macro.h"
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

// Set the source path for resources, etc.
void set_source_path(char **source_path, int *length) {

  *length = wai_getExecutablePath(nullptr, 0, nullptr) + 1;
  assert(*length >= 0);
  *source_path = malloc((size_t)*length * sizeof(*source_path));

  int dirname_length;
  wai_getExecutablePath(*source_path, *length - 1, &dirname_length);
  (*source_path)[dirname_length] = '\0';
}

Maze setup_maze(const char *source_path) {

  Maze maze;

  char path_buffer[FILENAME_MAX];
  cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
  PANIC(Maze_create(&maze, path_buffer));
  PANIC(Maze_detail(&maze));
  PANIC(Maze_complete_data(&maze));

  return maze;
}

struct spirit_setup_t {
  Anima *anima;
  const Maze *maze;
};
typedef struct spirit_setup_t SpiritSetup;

void *setup_spirit(void *void_setup_struct) {

  struct spirit_setup_t *setup_struct = void_setup_struct;
  Anima *anima = setup_struct->anima;

  Mind_touch(&anima->mind, setup_struct->maze);

  atomic_store(&anima->contact.flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->contact.mtx_suspend);
    if (!atomic_load(&anima->contact.flag_suspend)) {
      Mind_deduct(&anima->mind, setup_struct->maze);
      atomic_store(&anima->contact.flag_suspend, true);
    }
    pthread_cond_wait(&anima->contact.cond_resume, &anima->contact.mtx_suspend);
    pthread_mutex_unlock(&anima->contact.mtx_suspend);
  }
  return 0;
}

void setup_anima(Anima animas[ANIMA_COUNT], uint8_t id, Pair_uint8 location, const Maze *maze) {

  Anima_default(&animas[id], id, 16, location, DIRECTION_S);

  SpiritSetup setup = {
      .anima = &animas[id],
      .maze = maze,
  };
  SpiritSetup *setup_ptr = malloc(sizeof(setup));
  *setup_ptr = setup;

  pthread_create(&ANIMA_THREADS[id], nullptr, setup_spirit, (void *)setup_ptr);
}

void setup_renderer(Renderer *renderer, const Maze *maze, const char *source_path) {

  char path_buffer[FILENAME_MAX];
  cwk_path_join(source_path, "resources/sheet.png", path_buffer, FILENAME_MAX);

  g_log(nullptr, G_LOG_LEVEL_INFO, "Loading sheet from: %s", path_buffer);

  Renderer_create(renderer, maze->size, path_buffer);
}

void setup_animas(Anima animas[ANIMA_COUNT], const Maze *maze) { // Resource setup

  if (1 <= ANIMA_COUNT) {
    setup_anima(animas, 0, Pair_uint8_create(1, 2), maze);
    animas[0].pallete = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xffff00ff,
    };
  }

  if (2 <= ANIMA_COUNT) {
    setup_anima(animas, 1, Pair_uint8_create(16, 26), maze);
    animas[1].pallete = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xffffbb00,
    };
  }

  if (3 <= ANIMA_COUNT) {
    setup_anima(animas, 2, Pair_uint8_create(21, 12), maze);
    animas[2].pallete = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xfa8072ff,
    };
  }

  if (4 <= ANIMA_COUNT) {
    setup_anima(animas, 3, Pair_uint8_create(4, 29), maze);
    animas[3].pallete = (Pallete){
        .a = 0x00000000,
        .b = 0x00000000,
        .c = 0x00000000,
        .d = 0xff808080,
    };
  }
}
