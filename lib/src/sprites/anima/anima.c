#include <stdatomic.h>
#include <stdint.h>

#include <slog.h>

#include "enums.h"
#include "generic/pairs.h"
#include "sprites/anima.h"

void Anima_default(Anima *anima, const uint8_t id, const Pair_uint8 location, const Direction direction, uint32_t offset_n) {
  slog_display(SLOG_DEBUG, 0, "Creating anima: %d", id);

  *anima = (Anima){
      .id = id,
      .tick_action = 0,

      .contact = {
          .cond_resume = PTHREAD_COND_INITIALIZER,
          .mtx_suspend = PTHREAD_MUTEX_INITIALIZER,
      },

      .mind = {},
  };

  Mind_default(&anima->mind, id, location, direction);

  atomic_init(&anima->contact.flag_suspend, false);
}

void Anima_destroy(Anima *self) {
  assert(self != nullptr);
}

void Anima_handle_event(Anima *self, const SDL_Event *event) {
  assert(self != nullptr && event != nullptr);
}

void Anima_instinct(Anima *self) {
  assert(self != nullptr);
}
