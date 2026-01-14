from smt_man.path7 import path7_t
from smt_man.path4 import path4_t
import time

import z3

import smt_man
from smt_man.maze import maze_t
from smt_man.mind import mind
from smt_man.types import *
from smt_man.language import *

persona: z3_expr_t = z3.Const("persona", z3s_persona_t)
persona_location: location_t = (11, 26)


maze = smt_man.maze.Maze("./bin/resources/maze/source.txt")


optimizer = z3.Optimize()
mind.set_defaults(optimizer)


###

animas: list[z3_expr_t] = [
    z3.Const("gottlob", z3s_anima_t),
]
anima_locations: list[location_t] = [
    (1, 4),
]

## Path

path = path4_t()

path.assert_empty_constraints(optimizer, maze)
path.assert_constant_tile_constraints(optimizer, maze)
path.assert_constant_origin_is_anima_or_persona(optimizer, maze, animas, persona)
path.assert_constant_hints(optimizer, maze, anima_locations)

path.assert_persona_is_origin(optimizer, persona)
for anima in animas:
    path.assert_anima_is_origin(optimizer, anima)

optimizer.check()

unsat_instances: list[tuple[location_t, location_t]] = []

for anima_location in maze.tiles():
    if maze.is_path(anima_location[0], anima_location[1]):
        for persona_location in maze.tiles():
            if maze.is_path(persona_location[0], persona_location[1]):
                if anima_location != persona_location:
                    print(f"{anima_location} -> {persona_location}")
                    optimizer.push()

                    path.assert_variable_anima_location(optimizer, animas[0], anima_location[0], anima_location[1])
                    path.assert_variable_persona_location(optimizer, persona, persona_location[0], persona_location[1])

                    model = mind.timed_solve(optimizer, print_stats=True)
                    if model is not None:
                        print(path.to_string(maze, model))
                        # print(model)
                    else:
                        unsat_instances.append((anima_location, persona_location))
                        input("Hm... ")

                    optimizer.pop()


# mind.to_file(optimizer, "./anima.smt2")
# exit()
