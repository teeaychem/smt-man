
#pragma once

#include <SDL3/SDL.h>
#include <SDL3/SDL_main.h>
#include <SDL3/SDL_render.h>

#include "maze.hpp"
#include "sprite.hpp"
#include "utils.hpp"

struct Anima {

  Position _position{1, 1};

  Direction intent;
  Direction momentum;

  int mVel;

  Sprite sprite;

  static constexpr int kAnimaVelocity = 2;

  Anima();

  Anima(Sprite &&sprite) : _position{Position(1, 1)},
                           intent{Direction::down},
                           momentum{Direction::down},
                           mVel{1},
                           sprite(std::move(sprite)) {
    this->sprite.position.elements[0] = this->_position.x() * this->sprite.size.x();
    this->sprite.position.elements[1] = this->_position.x() * this->sprite.size.y();
  }

  void handleEvent(SDL_Event &event);

  void moveWithin(Maze &maze);

  const Position *position() const { return &this->_position; }
};
