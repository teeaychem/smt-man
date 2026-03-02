#include <stdatomic.h>

#include "SML/logic/synchronization.h"

void Sync_update_animas(const Situation *situation, Anima *animas) {

  for (size_t id = 0; id < situation->animas.count; ++id) {
    atomic_store(&animas[id].smt.situation.persona.direction_actual,
                 atomic_load(&situation->persona.direction_actual));

    atomic_store(&animas[id].smt.situation.persona.location,
                 atomic_load(&situation->persona.location));

    atomic_store(&animas[id].smt.situation.persona.movement_pattern,
                 atomic_load(&situation->persona.movement_pattern));
  }
}

void Sync_update_situation(Situation *situation, const Anima *animas) {

  for (size_t id = 0; id < situation->animas.count; ++id) {
    atomic_store(&situation->animas.data[id].direction_actual,
                 atomic_load(&animas[id].smt.situation.animas.data[id].direction_actual));

    atomic_store(&situation->animas.data[id].location,
                 atomic_load(&animas[id].smt.situation.animas.data[id].location));

    atomic_store(&situation->animas.data[id].movement_pattern,
                 atomic_load(&animas[id].smt.situation.animas.data[id].movement_pattern));

    atomic_store(&situation->animas.data[id].status,
                 atomic_load(&animas[id].smt.situation.animas.data[id].status));
  }
}

void sync_situation_to_situation(const Situation *from, Situation *to) {

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
