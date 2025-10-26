#pragma once

#include "spdlog/spdlog.h"
#include "utils.hpp"
#include <cinttypes>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>

class Maze {
public:
  Size size{0, 0};
  char *tiles;

  Maze(Size size, char *tiles) : size(size), tiles(tiles) {}

  Maze(std::filesystem::path path) {

    bool preambleOk = true;

    std::ifstream infile(path);
    if (!infile) {
      spdlog::error(std::format("Failed to open maze", path.string()));
      preambleOk = false;
    }

    std::string line;

    while (std::getline(infile, line) && !line.empty() && line[0] != 'm') {
      if (line[0] == 'w') {
        if (!sscanf(line.c_str() + 1, "%" SCNu32, &this->size.W)) {
          spdlog::error("Failed to read maze width");
          preambleOk = false;
        };
      }

      else if (line[0] == 'h') {
        if (!sscanf(line.c_str() + 1, "%" SCNu32, &this->size.H)) {
          spdlog::error("Failed to read maze height");
          preambleOk = false;
        };
      }
    }

    if (!preambleOk) {
      spdlog::error(std::format("Failed to construct maze from path {}", path.string()));
      exit(1);
    }

    this->tiles = (char *)malloc(size.area());
    memset(this->tiles, ' ', size.area());

    for (uint32_t r{0}; r < size.H; ++r) {
      if (!line.empty() && line[0] == 'm') {
        for (uint32_t c{1}; c <= std::min((size_t)size.W, line.size()); ++c) {
          this->tiles[r * size.W + c - 1] = line[c];
        }
      }
      if (r < size.H - 1 && !std::getline(infile, line)) {
        spdlog::error(std::format("Failed to read maze line {}", r + 1));
        std::exit(-1);
      }
    }

    infile.close();
  }

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
