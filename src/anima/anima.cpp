#include "anima.hpp"
#include "sprite.h"
#include "utils.h"

void Anima::handleEvent(SDL_Event &event) {

  if (event.type == SDL_EVENT_KEY_DOWN && !event.key.repeat) {

    switch (event.key.key) {
    case SDLK_UP:
      intent = Direction::up;
      break;
    case SDLK_DOWN:
      intent = Direction::down;
      break;
    case SDLK_LEFT:
      intent = Direction::left;
      break;
    case SDLK_RIGHT:
      intent = Direction::right;
      break;
    }
  }
}

void Anima::moveWithin(Maze &maze) {

  if (this->sprite.pos_x % this->sprite.size_w == 0 && this->sprite.pos_y % this->sprite.size_h == 0) {
    this->_position.elements[0] = sprite.pos_x / 16;
    this->_position.elements[1] = sprite.pos_y / 16;

    momentum = intent;

    auto next = nvec_direction_steps(this->_position, momentum, 1);

    if (maze.isOpen(next)) {
      this->mVel = 1;
    } else {
      this->mVel = 0;
    }
  }

  switch (momentum) {
  case up: {
    this->sprite.pos_y -= mVel;
  } break;
  case right: {
    this->sprite.pos_x += mVel;
  } break;
  case down: {
    this->sprite.pos_y += mVel;
  } break;
  case left: {
    this->sprite.pos_x -= mVel;
  } break;
  }
}
