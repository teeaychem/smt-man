#include <stdatomic.h>

#include "logic/synchronization.h"

void Sync_situation_animas(Situation *situation, Anima animas[ANIMA_COUNT]) {
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    { // From
      atomic_store(&situation->anima[idx].location, atomic_load(&animas[idx].mind.view.anima[idx].location));
      atomic_store(&situation->anima[idx].direction, atomic_load(&animas[idx].mind.view.anima[idx].direction));
      atomic_store(&situation->anima[idx].status, atomic_load(&animas[idx].mind.view.anima[idx].status));
      atomic_store(&situation->anima[idx].velocity, atomic_load(&animas[idx].mind.view.anima[idx].velocity));
      atomic_store(&situation->anima[idx].movement, atomic_load(&animas[idx].mind.view.anima[idx].movement));
    }

    { // To
      atomic_store(&animas[idx].mind.view.persona.location, atomic_load(&situation->persona.location));
      atomic_store(&animas[idx].mind.view.persona.direction, atomic_load(&situation->persona.direction));
      atomic_store(&animas[idx].mind.view.persona.velocity, atomic_load(&situation->persona.velocity));
      atomic_store(&animas[idx].mind.view.persona.movement, atomic_load(&situation->persona.movement));
    }
  }
}
