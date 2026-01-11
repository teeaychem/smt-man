#include <stdatomic.h>

#include "SML/logic/synchronization.h"

void Sync_update_animas(const Situation *situation, Anima *animas) {

  for (size_t id = 0; id < situation->anima_count; ++id) {
    atomic_store(&animas[id].smt.situation.persona.direction_actual, atomic_load(&situation->persona.direction_actual));
    atomic_store(&animas[id].smt.situation.persona.location, atomic_load(&situation->persona.location));
    atomic_store(&animas[id].smt.situation.persona.movement_pattern, atomic_load(&situation->persona.movement_pattern));
  }
}

void Sync_update_situation(Situation *situation, const Anima *animas) {

  for (size_t id = 0; id < situation->anima_count; ++id) {
    atomic_store(&situation->animas[id].direction_actual, atomic_load(&animas[id].smt.situation.animas[id].direction_actual));
    atomic_store(&situation->animas[id].location, atomic_load(&animas[id].smt.situation.animas[id].location));
    atomic_store(&situation->animas[id].movement_pattern, atomic_load(&animas[id].smt.situation.animas[id].movement_pattern));
    atomic_store(&situation->animas[id].status, atomic_load(&animas[id].smt.situation.animas[id].status));
  }
}
