#include <stdatomic.h>

#include "logic/synchronization.h"

void Sync_situation_animas(Situation *situation, Anima animas[ANIMA_COUNT]) {
  for (size_t idx = 0; idx < ANIMA_COUNT; ++idx) {
    atomic_store(&situation->anima[idx].location, atomic_load(&animas[idx].mind.view.anima[idx].location));
    atomic_store(&situation->anima[idx].status, atomic_load(&animas[idx].mind.view.anima[idx].status));
  }
}
