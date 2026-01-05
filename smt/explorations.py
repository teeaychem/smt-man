from smt_man.path7 import path7_t
import time

import z3

import smt_man
import smt_man.mind as mind
from smt_man.maze import maze_t
from smt_man.types import *
from smt_man.language import *

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
    z3.Const("smtman", z3s_anima_t),
]

## Path


path7 = path7_t()

path7.assert_tile_constraints(optimizer, maze)
path7.assert_path_empty_constraints(optimizer, maze)

for anima in animas:
    path7.anima_is_origin(optimizer, anima)

path7.assert_path_hints(optimizer, maze, anima_locations)
for id in range(len(animas)):
    path7.assert_anima_location(optimizer, animas[id], anima_locations[id][0], anima_locations[id][1])


def print_path(maze: maze_t, model: z3_model_t):
    for r in range(0, maze.height):
        bvr = z3s_bv8.cast(r)
        for c in range(0, maze.width):
            bvc = z3s_bv8.cast(c)
            if model.eval(path7.z3_path_v(bvc, bvr) != path7.EX):
                print("x", end="")
            else:
                print(" ", end="")
        print("")


model = mind.timed_solve(optimizer, print_stats=True)
if type(model) == z3_model_t:
    print_path(maze, model)  # ty:ignore[invalid-argument-type]
