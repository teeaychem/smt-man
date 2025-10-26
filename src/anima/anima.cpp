#include "anima.hpp"
#include "sprite.hpp"
#include "utils.hpp"

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

  if (this->sprite.position.x() % this->sprite.size.x() == 0 && this->sprite.position.y() % this->sprite.size.y() == 0) {
    this->_position.elements[0] = sprite.position.x() / 16;
    this->_position.elements[1] = sprite.position.y() / 16;

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
    this->sprite.position.elements[1] -= mVel;
  } break;
  case right: {
    this->sprite.position.elements[0] += mVel;
  } break;
  case down: {
    this->sprite.position.elements[1] += mVel;
  } break;
  case left: {
    this->sprite.position.elements[0] -= mVel;
  } break;
  }
}
