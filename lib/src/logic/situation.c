#include <assert.h>
#include <stdatomic.h>
#include <stdlib.h>

#include "SML/logic/situation.h"
#include "macro.h"

void situation_ctor(situation_s *self, size_t anima_count) {

  *self = (situation_s){
      .animas = {
          .count = anima_count,
          .data = malloc(anima_count * sizeof(*self->animas.data)),
      },
  };
}

void situation_dtor(situation_s *self) {

  // TODO
  free(self->animas.data);
  self->animas.count = 0;
}

void situation_reset(situation_s *self) {

  { // animas
    static Pair_uint8 locations[] = {{11, 13}, {2, 15}, {12, 21}, {29, 4}};
    assert(self->animas.count <= ARRAY_LEN(locations));

    for (uint8_t idx = 0; idx < self->animas.count; ++idx) {
      Pair_uint8 location = Pair_uint8_create(locations[idx].x, locations[idx].y);
      atomic_store(&self->animas.data[idx].location, location);
      atomic_store(&self->animas.data[idx].direction_actual, CARDINAL_S);
      atomic_store(&self->animas.data[idx].status, ANIMA_STATUS_SEARCH);
      atomic_store(&self->animas.data[idx].movement_pattern, 0x552a552a);
    }
  }
  { // persona
    Pair_uint8 persona_location = {.x = 17, .y = 15};
    atomic_init(&self->persona.direction_actual, CARDINAL_NONE);
    atomic_init(&self->persona.location, persona_location);
    atomic_init(&self->persona.movement_pattern, 0x552a552a);
  }
}

void situation_copy(const situation_s *from, situation_s *to) {

  { // animas
    assert(from->animas.count == to->animas.count);

    for (size_t idx = 0; idx < from->animas.count; ++idx) {
      atomic_store(&to->animas.data[idx].direction_actual, atomic_load(&from->animas.data[idx].direction_actual));
      atomic_store(&to->animas.data[idx].location, atomic_load(&from->animas.data[idx].location));
      atomic_store(&to->animas.data[idx].movement_pattern, atomic_load(&from->animas.data[idx].movement_pattern));
      atomic_store(&to->animas.data[idx].status, atomic_load(&from->animas.data[idx].status));
    }
  }

  { // persona
    atomic_store(&to->persona.direction_actual, atomic_load(&from->persona.direction_actual));
    atomic_store(&to->persona.location, atomic_load(&from->persona.location));
    atomic_store(&to->persona.movement_pattern, atomic_load(&from->persona.movement_pattern));
  }
}
