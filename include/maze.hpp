#pragma once

#include "utils.hpp"
#include <cstdint>

class Maze {
public:
  const Size size{0, 0};
  const char *tiles;

  Maze(Size size, char *tiles) : size(size), tiles(tiles) {}

  bool isOpen(Position &position) {
    bool yOk = 0 <= position.y && position.y < this->size.H;
    bool xOk = 0 <= position.x && position.x < this->size.W;
    bool locationOk = this->tileAt(position) == '#';

    return yOk && xOk && locationOk;
  }

  uint8_t tileAt(Position const &position) {
    return this->tiles[position.y * this->size.W + position.x];
  }

  std::string as_string() {
    std::string maze_string{};
    for (uint32_t r{0}; r < size.H; ++r) {
      for (uint32_t c{0}; c < size.W; ++c) {
        maze_string.push_back(this->tiles[r * size.W + c]);
      }
      maze_string.push_back('\n');
    }

    return maze_string;
  }
};
