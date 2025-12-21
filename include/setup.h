#pragma once

#include "anima.h"
#include "maze.h"

#include "constants.h"
#include "render.h"

/// Setup functions
///
/// Called by main.
void setup_resources(Renderer *renderer, Maze *maze, Anima animas[ANIMA_COUNT], Pallete anima_palletes[ANIMA_COUNT]);

void setup_sprites(Renderer *renderer, Anima animas[ANIMA_COUNT], Pair_uint32 anima_sprite_location[ANIMA_COUNT]);
