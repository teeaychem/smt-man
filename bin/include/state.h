#include <stddef.h>

#include "sprite/anima.h"
#include "sprite/persona.h"

struct state {
  struct {
    size_t count;
    anima_s *data;
  } animas;
  maze_s maze;

  persona_s persona;

  situation_s situation;
};
typedef struct state state_s;

void state_ctor(state_s *self, size_t anima_count, const char *source_path);

void stateg_dtor(state_s *self);
