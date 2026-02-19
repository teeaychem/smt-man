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
  ENSURE(Maze_from_path(&maze, path_buffer));
  ENSURE(Maze_detail(&maze));
  ENSURE(Maze_complete_data(&maze));

  return maze;
}

struct spirit_setup_t {
  Anima *anima;
  size_t anima_count;
  const Maze *maze;
  const char *source_path;
  pthread_t *thread;
};
typedef struct spirit_setup_t spirit_setup_s;

void *setup_spirit(void *void_setup_struct) {

  struct spirit_setup_t *setup_struct = void_setup_struct;
  Anima *anima = setup_struct->anima;

  Anima_touch(anima, setup_struct->anima_count);
  /* Anima_restrict(anima, setup_struct->maze); */

  {
    char smt_path[FILENAME_MAX];
    cwk_path_join(setup_struct->source_path, "resources/anima_0.smt2", smt_path, FILENAME_MAX);
    Anima_parse_fundamentals(anima, smt_path);
  }

  Lexicon_assert_shortest_path_empty_hints(&anima->smt.lexicon, anima->smt.ctx, anima->smt.opz, setup_struct->maze);

  atomic_store(&anima->contact.flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->contact.mtx_suspend);
    if (!atomic_load(&anima->contact.flag_suspend)) {
      ENSURE(Anima_deduct(anima, setup_struct->maze));
      atomic_store(&anima->contact.flag_suspend, true);
    }
    pthread_cond_wait(&anima->contact.cond_resume, &anima->contact.mtx_suspend);
    pthread_mutex_unlock(&anima->contact.mtx_suspend);
  }
  return 0;
}

void setup_animas(Anima *animas, pthread_t *threads, Sprites *sprites, const Maze *maze, size_t anima_count, const char *source_path) {
  static Pair_uint8 locations[] = {{3, 1}, {26, 16}, {12, 21}, {29, 4}};
  assert(anima_count <= ARRAY_LEN(locations));

  for (uint8_t idx = 0; idx < anima_count; ++idx) {

    Pair_uint8 location = Pair_uint8_create(locations[idx].x, locations[idx].y);

    spirit_setup_s *setup = malloc(sizeof(*setup));
    // binary lifetime, as thread lives until exit
    *setup = (spirit_setup_s){
        .anima = &animas[idx],
        .anima_count = anima_count,
        .maze = maze,
        .source_path = source_path,
    };

    Anima_init(&animas[idx], idx, location, CARDINAL_S, maze);
    if (sprites != nullptr) {
      Sprite_init(&sprites->animas[idx], 16, location, RENDER_TOP);
    }

    pthread_create(&threads[setup->anima->id], nullptr, setup_spirit, (void *)setup);
  }
}

void setup_situation(Situation *situation, Pair_uint8 location) {
  atomic_init(&situation->persona.direction_actual, CARDINAL_E);
  atomic_init(&situation->persona.location, location);
  atomic_init(&situation->persona.movement_pattern, 0x552a552a);
}
