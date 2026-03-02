#include <assert.h>
#include <stdatomic.h>
#include <stdlib.h>

#include "SML/logic/situation.h"
#include "macro.h"

void situation_ctor(Situation *self, size_t anima_count) {

  *self = (Situation){
      .animas = {
          .count = anima_count,
          .data = malloc(anima_count * sizeof(*self->animas.data)),
      },
  };
}

void situation_dtor(Situation *self) {

  // TODO
  free(self->animas.data);
  self->animas.count = 0;
}

void situation_reset(Situation *self) {

  { // animas
    static Pair_uint8 locations[] = {{11, 13}, {14, 11}, {12, 21}, {29, 4}};
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
