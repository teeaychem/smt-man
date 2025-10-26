#pragma once

#include "stumpless/log.h"
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

  // Maze(Size size, char *tiles) : size(size), tiles(tiles) {}

  ~Maze() {

  };

  Maze(std::filesystem::path path) {

    bool preambleOk = true;

    std::ifstream infile(path);
    if (!infile) {
      stumplog(LOG_ERR, "Failed to open maze");
      preambleOk = false;
    }

    std::string line;

    while (std::getline(infile, line) && !line.empty() && line[0] != 'm') {
      if (line[0] == 'w') {
        if (!sscanf(line.c_str() + 1, "%" SCNu32, &this->size.elements[0])) {
          stumplog(LOG_ERR, "Failed to read maze width");
          preambleOk = false;
        };
      }

      else if (line[0] == 'h') {
        if (!sscanf(line.c_str() + 1, "%" SCNu32, &this->size.elements[1])) {
          stumplog(LOG_ERR, "Failed to read maze height");
          preambleOk = false;
        };
      }
    }

    if (!preambleOk) {
      stumplog(LOG_INFO, path.c_str());
      stumplog(LOG_CRIT, "Failed to construct maze");
      exit(1);
    }

    this->tiles = (char *)malloc(size.area());
    memset(this->tiles, ' ', size.area());

    for (uint32_t r{0}; r < size.y(); ++r) {
      if (!line.empty() && line[0] == 'm') {
        for (uint32_t c{1}; c <= std::min((size_t)size.x(), line.size()); ++c) {
          this->tiles[r * size.x() + c - 1] = line[c];
        }
      }
      if (r < size.y() - 1 && !std::getline(infile, line)) {
        // spdlog::critical(std::format("Failed to read maze line {}", r + 1));
        std::exit(-1);
      }
    }

    infile.close();
  }

  bool isOpen(Position &position) {
    bool yOk = 0 <= position.y && position.y < this->size.y();
    bool xOk = 0 <= position.x && position.x < this->size.x();
    bool locationOk = this->tileAt(position) == '#';

    return yOk && xOk && locationOk;
  }

  uint8_t tileAt(Position const &position) {
    return this->tiles[position.y * this->size.x() + position.x];
  }

  std::string as_string() {
    std::string maze_string{};
    for (uint32_t r{0}; r < size.y(); ++r) {
      for (uint32_t c{0}; c < size.x(); ++c) {
        maze_string.push_back(this->tiles[r * size.x() + c]);
      }
      maze_string.push_back('\n');
    }

    return maze_string;
  }
};
