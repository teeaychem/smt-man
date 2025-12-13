#pragma once

#include "anima.h"
#include "maze.h"


#include "constants.h"
#include "render.h"

/// Setup functions
///
/// Called by main.
/// Ordered here by call priority, where relevant.

/// Before maze and anima
char *setup_source_path();

Maze setup_maze(char *source_path);

void setup_anima(char *source_path, Anima animas[ANIMA_COUNT], uint8_t id, Pair_uint8 location);

void *setup_spirit(void *void_anima);
