#pragma once

#include "SML/maze.h"
#include "SML/sprite/anima.h"

#include "render.h"

/// Setup functions
///
/// Called by main.

void set_source_path(char **source_path, int *length);

void setup_renderer(Renderer *renderer, const Maze *maze, const char *source_path);

void setup_animas(Anima *animas, pthread_t *threads, const Maze *maze, size_t anima_count, const char *source_path);
