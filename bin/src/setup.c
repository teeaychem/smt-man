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

// Set the source path for resources, etc.
void set_source_path(char **source_path, int *length) {

  *length = wai_getExecutablePath(nullptr, 0, nullptr) + 1;
  assert(*length >= 0);
  *source_path = malloc((size_t)*length * sizeof(*source_path));

  int dirname_length;
  wai_getExecutablePath(*source_path, *length - 1, &dirname_length);
  (*source_path)[dirname_length] = '\0';
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
    char smt2_path[32];
    sprintf(smt2_path, "resources/anima_%d.smt2", anima->id);

    char smt_path[FILENAME_MAX];
    cwk_path_join(setup_struct->source_path, smt2_path, smt_path, FILENAME_MAX);
    Anima_parse_fundamentals(anima, smt_path);
  }

  Lexicon_assert_shortest_path_empty_hints(&anima->smt.lexicon, anima->smt.ctx, anima->smt.opz, setup_struct->maze);

  atomic_store(&anima->contact.flag_suspend, true);

  while (true) {
    pthread_mutex_lock(&anima->contact.mtx_suspend);
    if (!atomic_load(&anima->contact.flag_suspend)) {
      ensure(Anima_deduct(anima, setup_struct->maze));
      atomic_store(&anima->contact.flag_suspend, true);
    }
    pthread_cond_wait(&anima->contact.cond_resume, &anima->contact.mtx_suspend);
    pthread_mutex_unlock(&anima->contact.mtx_suspend);
  }

  return 0;
}

void setup_animas(Anima *animas, pthread_t *threads, const Maze *maze, size_t anima_count, const char *source_path) {

  for (uint8_t idx = 0; idx < anima_count; ++idx) {

    spirit_setup_s *setup = malloc(sizeof(*setup));
    // static lifetime, as thread lives until exit
    *setup = (spirit_setup_s){
        .anima = &animas[idx],
        .anima_count = anima_count,
        .maze = maze,
        .source_path = source_path,
    };

    Anima_ctor(&animas[idx], anima_count, idx, maze);

    pthread_create(&threads[setup->anima->id], nullptr, setup_spirit, (void *)setup);
  }
}
