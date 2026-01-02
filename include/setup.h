#pragma once

#include "constants.h"
#include "lyf/anima.h"
#include "maze.h"
#include "render.h"

/// Setup functions
///
/// Called by main.
void setup_resources(Renderer *renderer, Maze *maze);

void setup_animas(Anima animas[ANIMA_COUNT], const Maze *maze);
