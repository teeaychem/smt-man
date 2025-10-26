#pragma once

#include "stumpless/log.h"
#include "utils/NVec.h"
#include <cinttypes>
#include <cstdint>
#include <filesystem>

inline void next_line(FILE *file) {
  char c;
  while (c != EOF && c != '\n') {
    c = fgetc(file);
  }
}

struct Maze {

  Size size{0, 0};
  char *tiles;

  ~Maze() {};

  Maze(std::filesystem::path path) {

    bool preambleOk = true;

    FILE *file = fopen(path.c_str(), "r");
    if (file == NULL) {
      stumplog(LOG_ERR, "Failed to open maze");
      preambleOk = false;
    }

    char read;

    while (read != EOF) {
      read = fgetc(file);

      switch (read) {
      case EOF:
        break;

      case 'c': {
      } break;

      case 'w': {
        if (!fscanf(file, "%" SCNu32, &this->size.elements[0])) {
          stumplog(LOG_ERR, "Failed to read maze width");
          preambleOk = false;
        };
      } break;

      case 'h': {
        if (!fscanf(file, "%" SCNu32, &this->size.elements[1])) {
          stumplog(LOG_ERR, "Failed to read maze height");
          preambleOk = false;
        };
      } break;

      case 'm': {
        ungetc(read, file);
        read = EOF;
      } break;

      default: {
      } break;
      }

      if (read != EOF) {
        next_line(file);
      }
    }

    if (!preambleOk) {
      stumplog(LOG_INFO, path.c_str());
      stumplog(LOG_CRIT, "Failed to construct maze");
      exit(1);
    }

    this->tiles = (char *)malloc(this->size.area());
    memset(this->tiles, ' ', size.area());

    int32_t tile_idx = 0;

    while ((read = fgetc(file)) != EOF) {
      switch (read) {
      case 'c': {
        next_line(file);
      } break;

      case 'm': {
      } break;

      case '\n': {
        while (tile_idx % this->size.elements[0] != 0 || tile_idx == 0) {
          ++tile_idx;
        }
      } break;

      default: {
        this->tiles[tile_idx] = read;
        ++tile_idx;
      }
      }
    }
  }

  bool isOpen(Position &position) {
    bool yOk = 0 <= position.y() && position.y() < this->size.y();
    bool xOk = 0 <= position.x() && position.x() < this->size.x();
    bool locationOk = this->tileAt(position) == '#';

    return yOk && xOk && locationOk;
  }

  uint8_t tileAt(Position const &position) {
    return this->tiles[position.y() * this->size.x() + position.x()];
  }
};
