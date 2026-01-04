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


###

## Base types


## Anima

animas: list[z3_expr_t] = [
    z3.Const("gottlob", z3s_anima_t),
    z3.Const("smtman", z3s_anima_t),
]
anima_locations: list[location_t] = [
    (1, 4),
    (11, 26),
]

## Path


## General assertion fns


class path4_t:
    def __init__(self):
        self.z3_path_enum_return: tuple[z3_datatype_sort_t, list[z3_fn_t]] = z3.EnumSort(
            "path_e",
            ("o", "a", "b", "x"),
            #      0    1    2    3
        )
        self.z3_path4_t: z3_datatype_sort_t = self.z3_path_enum_return[0]
        self.z3e_path4: list[z3_fn_t] = self.z3_path_enum_return[1]

        self.z3e_path4_o: z3_fn_t = self.z3e_path4[0]
        self.z3e_path4_a: z3_fn_t = self.z3e_path4[1]
        self.z3e_path4_b: z3_fn_t = self.z3e_path4[2]
        self.z3e_path4_x: z3_fn_t = self.z3e_path4[3]

        self.z3f_path4_v: z3_fn_t = z3.Function("path_type_v", z3s_bitvec_t, z3s_bitvec_t, self.z3_path4_t)
        self.z3f_path4_h: z3_fn_t = z3.Function("path_type_h", z3s_bitvec_t, z3s_bitvec_t, self.z3_path4_t)

    def print_path(self, maze: maze_t, model: z3_model_t):
        for r in range(0, maze.height):
            bvr = z3s_bitvec_t.cast(r)
            for c in range(0, maze.width):
                bvc = z3s_bitvec_t.cast(c)
                if model.eval(self.z3f_path4_h(bvc, bvr) != self.z3e_path4_x) or model.eval(self.z3f_path4_v(bvc, bvr) != self.z3e_path4_x):
                    print("x", end="")
                else:
                    print(" ", end="")
            print("")

    def assert_empty_constraints(self, optimizer: z3_optimizer_t, maze: maze_t):
        for r in range(0, maze.height):
            for c in range(0, maze.width):
                this_tile = [z3s_bitvec_t.cast(c), z3s_bitvec_t.cast(r)]
                if maze.is_path(c, r):
                    optimizer.add_soft(self.z3f_path4_h(this_tile) == self.z3e_path4_x, weight=1)
                    optimizer.add_soft(self.z3f_path4_v(this_tile) == self.z3e_path4_x, weight=1)
                else:
                    optimizer.add(self.z3f_path4_h(this_tile) == self.z3e_path4_x)
                    optimizer.add(self.z3f_path4_v(this_tile) == self.z3e_path4_x)

    def assert_anima_location(self, optimizer: z3_optimizer_t, anima: z3_expr_t, col: int, row: int):
        optimizer.add(z3f_anima_location_c(anima) == z3s_bitvec_t.cast(col))
        optimizer.add(z3f_anima_location_r(anima) == z3s_bitvec_t.cast(row))

    def assert_tile_constraints(self, optimizer: z3_optimizer_t, maze: maze_t):
        for r in range(0, maze.height):
            bvr = z3s_bitvec_t.cast(r)
            for c in range(0, maze.width):
                bvc = z3s_bitvec_t.cast(c)

                if maze.is_path(c, r):
                    this_tile = [z3s_bitvec_t.cast(c), z3s_bitvec_t.cast(r)]

                    up_tile = [z3s_bitvec_t.cast(c), z3s_bitvec_t.cast(r - 1)]
                    rt_tile = [z3s_bitvec_t.cast(c + 1), z3s_bitvec_t.cast(r)]
                    dn_tile = [z3s_bitvec_t.cast(c), z3s_bitvec_t.cast(r + 1)]
                    lt_tile = [z3s_bitvec_t.cast(c - 1), z3s_bitvec_t.cast(r)]

                    # Up disjunction
                    if r > 0:
                        up_tile_req = [self.z3f_path4_h(up_tile) == self.z3e_path4_o]
                        if c < maze.width - 1 and 0 < r and maze.is_path(c + 1, r - 1):
                            up_tile_req.append(self.z3f_path4_h(up_tile) == self.z3e_path4_a)
                        if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                            up_tile_req.append(self.z3f_path4_h(up_tile) == self.z3e_path4_b)
                        up_tile_or = z3.Or(up_tile_req)
                        consequent = [z3.And([self.z3f_path4_v(up_tile) == self.z3e_path4_b, up_tile_or])]
                        if 0 < r - 1 and maze.is_path(c, r - 2):
                            consequent.append(z3.And([self.z3f_path4_h(up_tile) == self.z3e_path4_x, self.z3f_path4_v(up_tile) == self.z3e_path4_a]))
                        consequent = z3.Or(consequent)
                        optimizer.add(z3.Implies(self.z3f_path4_v(this_tile) == self.z3e_path4_a, consequent))
                        optimizer.add(z3.Implies(z3.And([self.z3f_path4_v(this_tile) == self.z3e_path4_a, self.z3f_path4_h(this_tile) == self.z3e_path4_x]), consequent))

                    # Down disjunction
                    if r < maze.height - 1:
                        dn_tile_req = [self.z3f_path4_h(dn_tile) == self.z3e_path4_o]
                        if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                            dn_tile_req.append(self.z3f_path4_h(dn_tile) == self.z3e_path4_a)
                        if r < maze.height - 1 and 0 < c and maze.is_path(c - 1, r + 1):
                            dn_tile_req.append(self.z3f_path4_h(dn_tile) == self.z3e_path4_b)
                        dn_tile_or = z3.Or(dn_tile_req)
                        consequent = [z3.And([self.z3f_path4_v(dn_tile) == self.z3e_path4_a, dn_tile_or])]
                        if r + 1 < maze.height - 1 and maze.is_path(c, r + 2):
                            consequent.append(z3.And([self.z3f_path4_h(dn_tile) == self.z3e_path4_x, self.z3f_path4_v(dn_tile) == self.z3e_path4_a]))
                        consequent = z3.Or(consequent)
                        optimizer.add(z3.Implies(self.z3f_path4_v(this_tile) == self.z3e_path4_b, consequent))
                        optimizer.add(z3.Implies(z3.And([self.z3f_path4_v(this_tile) == self.z3e_path4_a, self.z3f_path4_h(this_tile) == self.z3e_path4_x]), consequent))

                    # Right disjunction
                    if c < maze.width - 1:
                        rt_tile_req = [self.z3f_path4_v(rt_tile) == self.z3e_path4_o]
                        if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                            rt_tile_req.append(self.z3f_path4_v(rt_tile) == self.z3e_path4_b)
                        if 0 < r and c < maze.width - 1 and maze.is_path(c + 1, r - 1):
                            rt_tile_req.append(self.z3f_path4_v(rt_tile) == self.z3e_path4_a)
                        rt_tile_or = z3.Or(rt_tile_req)
                        consequent = [z3.And([self.z3f_path4_h(rt_tile) == self.z3e_path4_b, rt_tile_or])]
                        if c + 1 < maze.width - 1 and maze.is_path(c + 2, r):
                            consequent.append(z3.And([self.z3f_path4_v(rt_tile) == self.z3e_path4_x, self.z3f_path4_h(rt_tile) == self.z3e_path4_a]))
                        consequent = z3.Or(consequent)
                        optimizer.add(z3.Implies(self.z3f_path4_h(this_tile) == self.z3e_path4_a, consequent))
                        optimizer.add(z3.Implies(z3.And([self.z3f_path4_h(this_tile) == self.z3e_path4_a, self.z3f_path4_v(this_tile) == self.z3e_path4_x]), consequent))

                    # Left disjunction
                    if c > 0:
                        lt_tile_req = [self.z3f_path4_v(lt_tile) == self.z3e_path4_o]
                        if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                            lt_tile_req.append(self.z3f_path4_v(lt_tile) == self.z3e_path4_a)
                        if 0 < c and r < maze.height - 1 and maze.is_path(c - 1, r + 1):
                            lt_tile_req.append(self.z3f_path4_v(lt_tile) == self.z3e_path4_b)
                        lt_tile_or = z3.Or(lt_tile_req)
                        consequent = [z3.And([self.z3f_path4_h(lt_tile) == self.z3e_path4_a, lt_tile_or])]
                        if 0 < c - 1 and maze.is_path(c - 2, r):
                            consequent.append(z3.And([self.z3f_path4_v(lt_tile) == self.z3e_path4_x, self.z3f_path4_h(lt_tile) == self.z3e_path4_a]))
                        consequent = z3.Or(consequent)
                        optimizer.add(z3.Implies(self.z3f_path4_h(this_tile) == self.z3e_path4_b, consequent))
                        optimizer.add(z3.Implies(z3.And([self.z3f_path4_h(this_tile) == self.z3e_path4_a, self.z3f_path4_v(this_tile) == self.z3e_path4_x]), consequent))

                    # Origin v disjunction
                    og_v_tile_req = []
                    if c < maze.width - 1:
                        og_v_tile_req.append(self.z3f_path4_h(rt_tile) == self.z3e_path4_b)
                    if 0 < c:
                        og_v_tile_req.append(self.z3f_path4_h(lt_tile) == self.z3e_path4_a)
                    origin_h_or = z3.Or(og_v_tile_req)
                    optimizer.add(z3.Implies(self.z3f_path4_v(this_tile) == self.z3e_path4_o, origin_h_or))

                    # Origin h disjunction
                    og_h_tile_req = []
                    if 0 < r:
                        og_h_tile_req.append(self.z3f_path4_v(up_tile) == self.z3e_path4_b)
                    if r < maze.height - 1:
                        og_h_tile_req.append(self.z3f_path4_v(dn_tile) == self.z3e_path4_a)
                    origin_v_or = z3.Or(og_h_tile_req)
                    optimizer.add(z3.Implies(self.z3f_path4_h(this_tile) == self.z3e_path4_o, origin_v_or))

    ## Specific assertion fns

    def assert_anima_is_origin(self, optimizer: z3_optimizer_t, anima: z3_expr_t):
        anima_location = [z3f_anima_location_c(anima), z3f_anima_location_r(anima)]
        optimizer.add(
            z3.Or(
                [
                    z3.And([self.z3f_path4_h(anima_location) == self.z3e_path4_o, self.z3f_path4_v(anima_location) != self.z3e_path4_o]),
                    z3.And([self.z3f_path4_h(anima_location) != self.z3e_path4_o, self.z3f_path4_v(anima_location) == self.z3e_path4_o]),
                ]
            )
        )

    def assert_hints(self, optimizer: z3_optimizer_t, locations: list[location_t]):
        for r in range(0, maze.height):
            for c in range(0, maze.width):
                this_tile = [z3s_bitvec_t.cast(c), z3s_bitvec_t.cast(r)]
                skip = False

                for idx in range(len(locations)):
                    if anima_locations[idx][0] == c and anima_locations[idx][1] == r:
                        skip = True

                if not skip:
                    optimizer.add(z3.Or([self.z3f_path4_h(this_tile) == self.z3e_path4_a, self.z3f_path4_h(this_tile) == self.z3e_path4_b, self.z3f_path4_h(this_tile) == self.z3e_path4_x]))
                    optimizer.add(z3.Or([self.z3f_path4_v(this_tile) == self.z3e_path4_a, self.z3f_path4_v(this_tile) == self.z3e_path4_b, self.z3f_path4_v(this_tile) == self.z3e_path4_x]))


path4 = path4_t()


path4.assert_empty_constraints(optimizer, maze)
path4.assert_tile_constraints(optimizer, maze)

for id in range(len(animas)):
    path4.assert_anima_location(optimizer, animas[id], anima_locations[id][0], anima_locations[id][1])

for anima in animas:
    path4.assert_anima_is_origin(optimizer, anima)
path4.assert_hints(optimizer, anima_locations)


time_solve_start = time.perf_counter()
time_solve_end = 0

result = optimizer.check()
time_solve_end = time.perf_counter()
print(f"Result: {result} in {time_solve_end - time_solve_start:0.4f} seconds")

if result == z3.sat:
    print(optimizer.statistics())

    model = optimizer.model()
    path4.print_path(maze, model)

    print(model)


# print(optimizer.help())
