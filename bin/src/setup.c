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

#define PALETTE_IMPLEMENTATION
#include "render/palette.h"
#undef PALETTE_IMPLEMENTATION

/// Other setup
#include "setup.h"

#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

#include <cwalk.h>
#include <whereami.h>

#include "render/sprite.h"

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
  size_t anima_count;
  Anima *anima;
  const Maze *maze;
  pthread_t *thread;
};
typedef struct spirit_setup_t SpiritSetup;

void *setup_spirit(void *void_setup_struct) {

  struct spirit_setup_t *setup_struct = void_setup_struct;
  Anima *anima = setup_struct->anima;

  Anima_touch(anima, setup_struct->maze, setup_struct->anima_count);

  atomic_store(&anima->contact.flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->contact.mtx_suspend);
    if (!atomic_load(&anima->contact.flag_suspend)) {
      Anima_deduct(anima, setup_struct->maze);
      atomic_store(&anima->contact.flag_suspend, true);
    }
    pthread_cond_wait(&anima->contact.cond_resume, &anima->contact.mtx_suspend);
    pthread_mutex_unlock(&anima->contact.mtx_suspend);
  }
  return 0;
}

void setup_anima(Anima *animas, pthread_t *threads, Sprites *sprites, uint8_t id, Pair_uint8 location, const Maze *maze, size_t anima_count) {
  assert(id < anima_count);

  Anima_default(&animas[id], id, location, CARDINAL_S);
  if (sprites != nullptr) {
    Sprite_init(&sprites->animas[id], 16, location, RENDER_TOP);
  }

  SpiritSetup setup = {
      .anima_count = anima_count,
      .anima = &animas[id],
      .maze = maze,
  };
  SpiritSetup *setup_ptr = malloc(sizeof(setup));
  *setup_ptr = setup;

  pthread_create(&threads[id], nullptr, setup_spirit, (void *)setup_ptr);
}

void setup_animas(Anima *animas, pthread_t *threads, Sprites *sprites, const Maze *maze, size_t anima_count) {

  if (1 <= anima_count) {
    setup_anima(animas, threads, sprites, 0, Pair_uint8_create(1, 2), maze, anima_count);
  }

  if (2 <= anima_count) {
    setup_anima(animas, threads, sprites, 1, Pair_uint8_create(16, 26), maze, anima_count);
  }

  if (3 <= anima_count) {
    setup_anima(animas, threads, sprites, 2, Pair_uint8_create(21, 12), maze, anima_count);
  }

  if (4 <= anima_count) {
    setup_anima(animas, threads, sprites, 3, Pair_uint8_create(4, 29), maze, anima_count);
  }
}

void setup_situation(Situation *situation, Pair_uint8 location) {
  printf("Setting up situation with location: %dx%d\n", location.x, location.y);
  atomic_init(&situation->persona.direction_actual, CARDINAL_E);
  atomic_init(&situation->persona.location, location);
  atomic_init(&situation->persona.movement_pattern, 0x552a552a);
}
