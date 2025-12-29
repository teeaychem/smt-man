#include <stdatomic.h>

#include "logic/synchronization.h"

void Sync_situations(Situation *situation, Anima animas[ANIMA_COUNT]) {
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    { // From
      atomic_store(&situation->anima[idx].direction_actual, atomic_load(&animas[idx].mind.view.anima[idx].direction_actual));
      atomic_store(&situation->anima[idx].location, atomic_load(&animas[idx].mind.view.anima[idx].location));
      atomic_store(&situation->anima[idx].movement_pattern, atomic_load(&animas[idx].mind.view.anima[idx].movement_pattern));
      atomic_store(&situation->anima[idx].status, atomic_load(&animas[idx].mind.view.anima[idx].status));
    }

    { // To
      atomic_store(&animas[idx].mind.view.persona.direction_actual, atomic_load(&situation->persona.direction_actual));
      atomic_store(&animas[idx].mind.view.persona.location, atomic_load(&situation->persona.location));
      atomic_store(&animas[idx].mind.view.persona.movement_pattern, atomic_load(&situation->persona.movement_pattern));
    }
  }
}
