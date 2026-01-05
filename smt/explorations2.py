from smt_man import path4_t
import typing
import z3
import smt_man
import smt_man.mind as mind
from smt_man.types import *
from smt_man.language import *
from smt_man.maze import maze_t


maze = smt_man.maze.Maze("./resources/maze/source.txt")
optimizer = z3.Optimize()
mind.set_defaults(optimizer)

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
for anima in animas:
    path4.assert_anima_is_origin(optimizer, anima)

optimizer.check()

optimizer.push()

for id in range(len(animas)):
    path4.assert_anima_location(optimizer, animas[id], anima_locations[id][0], anima_locations[id][1])

path4.assert_hints(optimizer, maze, anima_locations)

model = mind.timed_solve(optimizer, print_stats=True)
if type(model) == z3_model_t:
    path4.print_path(maze, model)  # ty:ignore[invalid-argument-type]


optimizer.pop()

# print(optimizer.help())
