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
        self.z3_return: tuple[z3_datatype_sort_t, list[z3_fn_t]] = z3.EnumSort("path_e", ("o", "a", "b", "x"))
        self.z3_t: z3_datatype_sort_t = self.z3_return[0]
        self.z3e: list[z3_fn_t] = self.z3_return[1]

        self.z3e_o: z3_fn_t = self.z3e[0]
        self.z3e_a: z3_fn_t = self.z3e[1]
        self.z3e_b: z3_fn_t = self.z3e[2]
        self.z3e_x: z3_fn_t = self.z3e[3]

        self.z3f_v: z3_fn_t = z3.Function("path_type_v", z3s_bv_t, z3s_bv_t, self.z3_t)
        self.z3f_h: z3_fn_t = z3.Function("path_type_h", z3s_bv_t, z3s_bv_t, self.z3_t)

    def print_path(self, maze: maze_t, model: z3_model_t):
        for row in range(0, maze.height):
            for col in range(0, maze.width):
                bvc, bvr = z3s_bv_t.cast(col), z3s_bv_t.cast(row)
                if model.eval(self.z3f_h(bvc, bvr) != self.z3e_x) or model.eval(self.z3f_v(bvc, bvr) != self.z3e_x):
                    print("x", end="")
                else:
                    print(" ", end="")
            print("")

    def direct_h(self, tile: list[z3_expr_t]):
        return z3.And([self.z3f_v(tile) == self.z3e_x, self.z3f_h(tile) == self.z3e_a])

    def direct_v(self, tile: list[z3_expr_t]):
        return z3.And([self.z3f_v(tile) == self.z3e_a, self.z3f_h(tile) == self.z3e_x])

    def assert_empty_constraints(self, optimizer: z3_optimizer_t, maze: maze_t):
        for col, row in maze.tiles():
            tile_x = [z3s_bv_t.cast(col), z3s_bv_t.cast(row)]

            if maze.is_path(col, row):
                optimizer.add_soft(self.z3f_h(tile_x) == self.z3e_x, weight=1)
                optimizer.add_soft(self.z3f_v(tile_x) == self.z3e_x, weight=1)
            else:
                optimizer.add(self.z3f_h(tile_x) == self.z3e_x)
                optimizer.add(self.z3f_v(tile_x) == self.z3e_x)

    def assert_anima_location(self, optimizer: z3_optimizer_t, anima: z3_expr_t, col: int, row: int):
        optimizer.add(z3f_anima_location_c(anima) == z3s_bv_t.cast(col))
        optimizer.add(z3f_anima_location_r(anima) == z3s_bv_t.cast(row))

    def assert_tile_constraint_n(self, col: int, row: int):
        if row <= 0:
            return

        tile_x = [z3s_bv_t.cast(col), z3s_bv_t.cast(row)]
        tile_n = [z3s_bv_t.cast(col), z3s_bv_t.cast(row - 1)]

        up_tile_req = [self.z3f_h(tile_n) == self.z3e_o]

        if col < maze.width - 1 and 0 < row and maze.is_path(col + 1, row - 1):
            up_tile_req.append(self.z3f_h(tile_n) == self.z3e_a)
        if 0 < col and 0 < row and maze.is_path(col - 1, row - 1):
            up_tile_req.append(self.z3f_h(tile_n) == self.z3e_b)

        consequent = [z3.And([self.z3f_v(tile_n) == self.z3e_b, z3.Or(up_tile_req)])]

        if 0 < row - 1 and maze.is_path(col, row - 2):
            consequent.append(self.direct_v(tile_n))

        consequent = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_v(tile_x) == self.z3e_a, consequent))
        optimizer.add(z3.Implies(self.direct_v(tile_x), consequent))

    def assert_tile_constraint_s(self, col: int, row: int):
        if row >= maze.height - 1:
            return

        tile_x = [z3s_bv_t.cast(col), z3s_bv_t.cast(row)]
        tile_s = [z3s_bv_t.cast(col), z3s_bv_t.cast(row + 1)]

        dn_tile_req = [self.z3f_h(tile_s) == self.z3e_o]

        if row < maze.height - 1 and col < maze.width - 1 and maze.is_path(col + 1, row + 1):
            dn_tile_req.append(self.z3f_h(tile_s) == self.z3e_a)
        if row < maze.height - 1 and 0 < col and maze.is_path(col - 1, row + 1):
            dn_tile_req.append(self.z3f_h(tile_s) == self.z3e_b)

        consequent = [z3.And([self.z3f_v(tile_s) == self.z3e_a, z3.Or(dn_tile_req)])]

        if row + 1 < maze.height - 1 and maze.is_path(col, row + 2):
            consequent.append(self.direct_v(tile_s))

        consequent = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_v(tile_x) == self.z3e_b, consequent))
        optimizer.add(z3.Implies(self.direct_v(tile_x), consequent))

    def assert_tile_constraint_e(self, col: int, row: int):
        if col >= maze.width - 1:
            return

        tile_x = [z3s_bv_t.cast(col), z3s_bv_t.cast(row)]
        tile_e = [z3s_bv_t.cast(col + 1), z3s_bv_t.cast(row)]

        rt_tile_req = [self.z3f_v(tile_e) == self.z3e_o]

        if row < maze.height - 1 and col < maze.width - 1 and maze.is_path(col + 1, row + 1):
            rt_tile_req.append(self.z3f_v(tile_e) == self.z3e_b)
        if 0 < row and col < maze.width - 1 and maze.is_path(col + 1, row - 1):
            rt_tile_req.append(self.z3f_v(tile_e) == self.z3e_a)
        rt_tile_or = z3.Or(rt_tile_req)

        consequent = [z3.And([self.z3f_h(tile_e) == self.z3e_b, rt_tile_or])]

        if col + 1 < maze.width - 1 and maze.is_path(col + 2, row):
            consequent.append(self.direct_h(tile_e))

        consequent = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_h(tile_x) == self.z3e_a, consequent))
        optimizer.add(z3.Implies(self.direct_h(tile_x), consequent))

    def assert_tile_constraint_w(self, col: int, row: int):
        if col <= 0:
            return

        tile_x = [z3s_bv_t.cast(col), z3s_bv_t.cast(row)]
        tile_w = [z3s_bv_t.cast(col - 1), z3s_bv_t.cast(row)]

        lt_tile_req = [self.z3f_v(tile_w) == self.z3e_o]

        if 0 < col and 0 < row and maze.is_path(col - 1, row - 1):
            lt_tile_req.append(self.z3f_v(tile_w) == self.z3e_a)
        if 0 < col and row < maze.height - 1 and maze.is_path(col - 1, row + 1):
            lt_tile_req.append(self.z3f_v(tile_w) == self.z3e_b)

        consequent = [z3.And([self.z3f_h(tile_w) == self.z3e_a, z3.Or(lt_tile_req)])]

        if 0 < col - 1 and maze.is_path(col - 2, row):
            consequent.append(self.direct_h(tile_w))

        consequent = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_h(tile_x) == self.z3e_b, consequent))
        optimizer.add(z3.Implies(self.direct_h(tile_x), consequent))

    def assert_tile_constraints(self, optimizer: z3_optimizer_t, maze: maze_t):
        for col, row in maze.tiles():
            if not maze.is_path(col, row):
                continue

            bvc, bvr = z3s_bv_t.cast(col), z3s_bv_t.cast(row)

            tile_x = [z3s_bv_t.cast(col), z3s_bv_t.cast(row)]

            tile_n = [z3s_bv_t.cast(col), z3s_bv_t.cast(row - 1)]
            tile_e = [z3s_bv_t.cast(col + 1), z3s_bv_t.cast(row)]
            tile_s = [z3s_bv_t.cast(col), z3s_bv_t.cast(row + 1)]
            tile_w = [z3s_bv_t.cast(col - 1), z3s_bv_t.cast(row)]

            self.assert_tile_constraint_n(col, row)
            self.assert_tile_constraint_s(col, row)
            self.assert_tile_constraint_e(col, row)
            self.assert_tile_constraint_w(col, row)

            # Origin v disjunction
            og_v_tile_req = []

            if col < maze.width - 1:
                og_v_tile_req.append(self.z3f_h(tile_e) == self.z3e_b)
            if 0 < col:
                og_v_tile_req.append(self.z3f_h(tile_w) == self.z3e_a)

            origin_h_or = z3.Or(og_v_tile_req)
            optimizer.add(z3.Implies(self.z3f_v(tile_x) == self.z3e_o, origin_h_or))

            # Origin h disjunction
            og_h_tile_req = []

            if 0 < row:
                og_h_tile_req.append(self.z3f_v(tile_n) == self.z3e_b)
            if row < maze.height - 1:
                og_h_tile_req.append(self.z3f_v(tile_s) == self.z3e_a)

                origin_v_or = z3.Or(og_h_tile_req)

            optimizer.add(z3.Implies(self.z3f_h(tile_x) == self.z3e_o, origin_v_or))

    ## Specific assertion fns

    def assert_anima_is_origin(self, optimizer: z3_optimizer_t, anima: z3_expr_t):
        anima_location = [z3f_anima_location_c(anima), z3f_anima_location_r(anima)]
        optimizer.add(
            z3.Or(
                [
                    z3.And([self.z3f_h(anima_location) == self.z3e_o, self.z3f_v(anima_location) != self.z3e_o]),
                    z3.And([self.z3f_h(anima_location) != self.z3e_o, self.z3f_v(anima_location) == self.z3e_o]),
                ]
            )
        )

    def assert_hints(self, optimizer: z3_optimizer_t, locations: list[location_t]):
        for col, row in maze.tiles():
            this_tile = [z3s_bv_t.cast(col), z3s_bv_t.cast(row)]
            skip = False

            for idx in range(len(locations)):
                if anima_locations[idx][0] == col and anima_locations[idx][1] == row:
                    skip = True

            if not skip:
                h_d = z3.Or(
                    [
                        self.z3f_h(this_tile) == self.z3e_a,
                        self.z3f_h(this_tile) == self.z3e_b,
                        self.z3f_h(this_tile) == self.z3e_x,
                    ]
                )
                v_d = z3.Or(
                    [
                        self.z3f_v(this_tile) == self.z3e_a,
                        self.z3f_v(this_tile) == self.z3e_b,
                        self.z3f_v(this_tile) == self.z3e_x,
                    ]
                )

                optimizer.add(h_d)
                optimizer.add(v_d)


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
