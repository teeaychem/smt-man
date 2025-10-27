
#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "maze.hpp"
#include "sprite.h"

struct Anima {

  Position _position{1, 1};

  Direction intent;
  Direction momentum;

  int mVel;

  Sprite sprite;

  static constexpr int kAnimaVelocity = 2;

  ~Anima() {
    free(sprite.pixels);
  };

  Anima(Sprite sprite) : _position{Position(1, 1)},
                          intent{Direction::down},
                          momentum{Direction::down},
                          mVel{1},
                          sprite(sprite) {
    this->sprite.pos_x = this->_position.x() * this->sprite.size_w;
    this->sprite.pos_y = this->_position.x() * this->sprite.size_h;
  }

  void handleEvent(SDL_Event &event);

  void moveWithin(Maze &maze);

  const Position *position() const { return &this->_position; }
};
