#pragma once

#include <SDL3/SDL_main.h>

class SDLTimer {
public:
  SDLTimer();

  void start();
  void stop();
  void pause();
  void unpause();

  Uint64 getTicksNS();

  bool isStarted();
  bool isPaused();

private:
  Uint64 mStartedTicks;

  Uint64 mPausedTicks;

  bool mPaused;
  bool mStarted;
};
