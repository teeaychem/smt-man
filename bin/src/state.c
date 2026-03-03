#include "cwalk.h"

#include "state.h"

void state_ctor(state_s *self, size_t anima_count, const char *source_path) {

  *self = (state_s){
      .animas = {
          .count = anima_count,
          .data = malloc(anima_count * sizeof(*self->animas.data)),
      },
      .maze = {},
      .situation = {
          .animas = {
              .count = anima_count,
              .data = malloc(anima_count * sizeof(*self->animas.data)),
          },
      },
  };

  {
    char path_buffer[FILENAME_MAX];
    cwk_path_join(source_path, "resources/maze/source.txt", path_buffer, FILENAME_MAX);
    maze_ctor_from_path(&self->maze, path_buffer);
  }
  situation_reset(&self->situation);

  persona_ctor(&self->persona, &self->situation);
}

void state_dtor(state_s *self) {
  assert(self != nullptr);
  // TODO
}
