#include <SDL3/SDL_main.h>

struct ns_timer_t {
  Uint64 mStartedTicks;
  Uint64 mPausedTicks;

  bool mPaused;
  bool mStarted;
};

typedef struct ns_timer_t NSTimer;

NSTimer NSTimer_default();

void NSTimer_start(NSTimer *self);

void NSTimer_stop(NSTimer *self);

void NSTimer_pause(NSTimer *self);

void NSTimer_unpause(NSTimer *self);

Uint64 NSTimer_get_ticks(NSTimer *self);

bool NSTimer_is_started(NSTimer *self);

bool NSTimer_is_paused(NSTimer *self);
