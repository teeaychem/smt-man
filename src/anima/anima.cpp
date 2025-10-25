#include "anima.hpp"
#include "unethical.hpp"
#include "utils.hpp"
#include <iostream>

Anima::Anima() : _position{Position(6 * kTileSize, 16 * kTileSize)},
                 intent{Direction::down},
                 momentum{Direction::down},
                 mVel{1} {
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

void Anima::move() {

  if (this->sprite.position.x % 16 == 0 && this->sprite.position.y % 16 == 0) {
    momentum = intent;
    this->_position.x = sprite.position.x / 16;
    this->_position.y = sprite.position.y / 16;
    std::cout << this->_position.toString() << "\n";
  }

  switch (momentum) {
  case up: {
    this->sprite.position.y -= mVel;
    break;
  }
  case right: {
    this->sprite.position.x += mVel;
    break;
  }
  case down: {
    this->sprite.position.y += mVel;
    break;
  }
  case left: {
    this->sprite.position.x -= mVel;
    break;
  }
  }

  // posC.x += mVelX;

  // if ((posC.x < 0) || (posC.x + kAnimaHeight > kScreenWidth)) {
  //   posC.x -= mVelX;
  // }

  // posC.y += mVelY;

  // if ((posC.y < 0) || (posC.y + kAnimaWidth > kScreenHeight)) {
  //   posC.y -= mVelY;
  // }
}
