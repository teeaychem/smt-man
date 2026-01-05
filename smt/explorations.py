from smt_man.path7 import path7_t
from smt_man.path4 import path4_t
import time

import z3

import smt_man
from smt_man.maze import maze_t
from smt_man.mind import mind
from smt_man.types import *
from smt_man.language import *

VARIABLE_HINTS: bool = False

anima_locations: list[location_t] = [
    (1, 4),
    (11, 26),
]


maze = smt_man.maze.Maze("./resources/maze/source.txt")


optimizer = z3.Optimize()
mind.set_defaults(optimizer)


###

animas: list[z3_expr_t] = [
    z3.Const("gottlob", z3s_anima_t),
    z3.Const("smt-man", z3s_anima_t),
]

## Path

path = path4_t()

path.assert_empty_constraints(optimizer, maze)
path.assert_constant_tile_constraints(optimizer, maze)
for anima in animas:
    path.assert_anima_is_origin(optimizer, anima)

if not VARIABLE_HINTS:
    path.assert_constant_origin_is_anima(optimizer, maze, animas)
    path.assert_constant_hints(optimizer, maze, anima_locations)


mind.to_file(optimizer, "./anima.smt2")
# exit()

optimizer.check()

optimizer.push()

for id in range(len(animas)):
    path.assert_variable_anima_location(optimizer, animas[id], anima_locations[id][0], anima_locations[id][1])

if VARIABLE_HINTS:
    path.assert_variable_hints(optimizer, maze, anima_locations)

model = mind.timed_solve(optimizer, print_stats=True)
if type(model) == z3_model_t:
    path.print_path(maze, model)  # ty:ignore[invalid-argument-type]
    print(model)


optimizer.pop()
