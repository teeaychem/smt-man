#include <stdatomic.h>

#include "logic/synchronization.h"

void Sync_update_animas(const Situation *situation, Anima animas[ANIMA_COUNT]) {

  for (size_t id = 0; id < ANIMA_COUNT; ++id) {
    atomic_store(&animas[id].mind.view.persona.direction_actual, atomic_load(&situation->persona.direction_actual));
    atomic_store(&animas[id].mind.view.persona.location, atomic_load(&situation->persona.location));
    atomic_store(&animas[id].mind.view.persona.movement_pattern, atomic_load(&situation->persona.movement_pattern));
  }
}

void Sync_update_situation(Situation *situation, const Anima animas[ANIMA_COUNT]) {

  for (size_t id = 0; id < ANIMA_COUNT; ++id) {
    atomic_store(&situation->anima[id].direction_actual, atomic_load(&animas[id].mind.view.anima[id].direction_actual));
    atomic_store(&situation->anima[id].location, atomic_load(&animas[id].mind.view.anima[id].location));
    atomic_store(&situation->anima[id].movement_pattern, atomic_load(&animas[id].mind.view.anima[id].movement_pattern));
    atomic_store(&situation->anima[id].status, atomic_load(&animas[id].mind.view.anima[id].status));
  }
}
