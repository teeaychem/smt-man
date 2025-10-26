#include <iostream>

#include "anima.hpp"
#include "sprite.hpp"
#include "unethical.hpp"
#include "utils.hpp"

Anima::Anima(Sprite sprite) : _position{Position(1, 1)},
                              intent{Direction::down},
                              momentum{Direction::down},
                              mVel{1},
                              sprite(sprite) {
  this->sprite.position.x = this->_position.x * this->sprite.size.W;
  this->sprite.position.y = this->_position.x * this->sprite.size.H;
}

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

  if (this->sprite.position.x % this->sprite.size.W == 0 && this->sprite.position.y % this->sprite.size.H == 0) {

    this->_position.x = sprite.position.x / 16;
    this->_position.y = sprite.position.y / 16;

    momentum = intent;

    auto next = this->_position.inDirection(momentum, 1);

    if (maze.isOpen(next)) {
      this->mVel = 1;
    } else {
      this->mVel = 0;
    }
  }

  switch (momentum) {
  case up: {
    this->sprite.position.y -= mVel;
  } break;
  case right: {
    this->sprite.position.x += mVel;
  } break;
  case down: {
    this->sprite.position.y += mVel;
  } break;
  case left: {
    this->sprite.position.x -= mVel;
  } break;
  }
}
