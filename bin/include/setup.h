#pragma once

#include "constants.h"
#include "maze.h"
#include "render.h"
#include "render/sprite.h"
#include "sprites/anima.h"

/// Setup functions
///
/// Called by main.

void set_source_path(char **source_path, int *length);

Maze setup_maze(const char *source_path);

void setup_renderer(Renderer *renderer, const Maze *maze, const char *source_path);

void setup_animas(Anima animas[ANIMA_COUNT], pthread_t threads[ANIMA_COUNT], Sprites *sprites, const Maze *maze);

void setup_situation(Situation *situation, Pair_uint8 location);
