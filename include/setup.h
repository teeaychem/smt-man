#pragma once

#include "anima.h"
#include "maze.h"

#include "constants.h"

/// Setup functions
///
/// Called by main.
/// Ordered here by call priority, where relevant.

/// Before maze and anima
void setup_source_path(char **source_path);

void setup_maze(Maze *maze, char *source_path);

void setup_anima(Anima animas[ANIMA_COUNT], uint8_t id, Pair_uint8 location);

void *setup_spirit(void *void_anima);
