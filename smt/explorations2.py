from smt_man import path4_t
import typing
import z3
import smt_man
import smt_man.mind as mind
from smt_man.types import *
from smt_man.language import *

import time

maze = smt_man.maze.Maze("./resources/maze/source.txt")
optimizer = z3.Optimize()
mind.solver_set_defaults(optimizer)

#

## Anima

animas: list[z3_expr_t] = [
    z3.Const("gottlob", z3s_anima_t),
    z3.Const("smtman", z3s_anima_t),
]
anima_locations: list[location_t] = [
    (1, 4),
    (11, 26),
]

path4: path4_t = path4_t()

path4.assert_empty_constraints(optimizer, maze)
path4.assert_general_tile_constraints(optimizer, maze)

for id in range(len(animas)):
    path4.assert_anima_location(optimizer, animas[id], anima_locations[id][0], anima_locations[id][1])

for anima in animas:
    path4.assert_anima_is_origin(optimizer, anima)

path4.assert_hints(optimizer, maze, anima_locations)


time_solve_start: float = time.perf_counter()
time_solve_end = 0

result = optimizer.check()
time_solve_end: float = time.perf_counter()
print(f"Result: {result} in {time_solve_end - time_solve_start:0.4f} seconds")

if result == z3.sat:
    print(optimizer.statistics())

    model = optimizer.model()
    path4.print_path(maze, model)

    print(model)


# print(optimizer.help())
