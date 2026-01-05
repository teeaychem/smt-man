import z3

from smt_man.language import *
from smt_man.types import *
from smt_man.maze import maze_t
import smt_man


class path4_t:
    def __init__(self):
        self.z3_return: tuple[z3_datatype_sort_t, list[z3_fn_t]] = z3.EnumSort("path_e", ("o", "a", "b", "x"))
        self.z3_t: z3_datatype_sort_t = self.z3_return[0]
        self.z3e: list[z3_fn_t] = self.z3_return[1]

        self.z3e_o = self.z3e[0]
        self.z3e_a = self.z3e[1]
        self.z3e_b = self.z3e[2]
        self.z3e_x = self.z3e[3]

        self.z3f_v: z3_fn_t = z3.Function("path_type_v", z3s_bv8_t, z3s_bv8_t, self.z3_t)
        self.z3f_h: z3_fn_t = z3.Function("path_type_h", z3s_bv8_t, z3s_bv8_t, self.z3_t)

    def print_path(self, maze: maze_t, model: z3_model_t):
        for row in range(0, maze.height):
            for col in range(0, maze.width):
                bvc, bvr = z3s_bv8.cast(col), z3s_bv8.cast(row)
                if model.eval(self.z3f_h(bvc, bvr) != self.z3e_x) or model.eval(self.z3f_v(bvc, bvr) != self.z3e_x):
                    print("x", end="")
                else:
                    print(" ", end="")
            print("")

    def direct_h(self, tile: z3_tile_t) -> z3_bool_t:
        return z3.And([self.z3f_v(tile) == self.z3e_x, self.z3f_h(tile) == self.z3e_a])

    def direct_v(self, tile: z3_tile_t) -> z3_bool_t:
        return z3.And([self.z3f_v(tile) == self.z3e_a, self.z3f_h(tile) == self.z3e_x])

    # # Assertions, constant

    def assert_empty_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        for col, row in maze.tiles():
            tile_x = z3_tile.X(col, row)

            if maze.is_path(col, row):
                optimizer.add_soft(self.z3f_h(tile_x) == self.z3e_x, weight=1)
                optimizer.add_soft(self.z3f_v(tile_x) == self.z3e_x, weight=1)
            else:
                optimizer.add(self.z3f_h(tile_x) == self.z3e_x)
                optimizer.add(self.z3f_v(tile_x) == self.z3e_x)

    def assert_anima_location(self, optimizer: z3_optimizer_t, anima: z3_expr_t, col: int, row: int) -> None:
        optimizer.add(z3f_anima_location_c(anima) == z3s_bv8.cast(col))
        optimizer.add(z3f_anima_location_r(anima) == z3s_bv8.cast(row))

    def assert_tile_constraint_n(self, optimizer: z3_optimizer_t, maze: maze_t, col: int, row: int) -> None:
        if row <= 0:
            return

        tile_x = z3_tile.X(col, row)
        tile_n = z3_tile.N(col, row)

        up_tile_req: list[z3_bool_t] = [self.z3f_h(tile_n) == self.z3e_o]

        if col < maze.width - 1 and 0 < row and maze.is_path(col + 1, row - 1):
            up_tile_req.append(self.z3f_h(tile_n) == self.z3e_a)
        if 0 < col and 0 < row and maze.is_path(col - 1, row - 1):
            up_tile_req.append(self.z3f_h(tile_n) == self.z3e_b)

        consequent: list[z3_bool_t] = [z3.And([self.z3f_v(tile_n) == self.z3e_b, z3.Or(up_tile_req)])]

        if 0 < row - 1 and maze.is_path(col, row - 2):
            consequent.append(self.direct_v(tile_n))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_v(tile_x) == self.z3e_a, consequent))
        optimizer.add(z3.Implies(self.direct_v(tile_x), consequent))

    def assert_tile_constraint_s(self, optimizer: z3_optimizer_t, maze: maze_t, col: int, row: int) -> None:
        if row >= maze.height - 1:
            return

        tile_x = z3_tile.X(col, row)
        tile_s = z3_tile.S(col, row)

        dn_tile_req: list[z3_bool_t] = [self.z3f_h(tile_s) == self.z3e_o]

        if row < maze.height - 1 and col < maze.width - 1 and maze.is_path(col + 1, row + 1):
            dn_tile_req.append(self.z3f_h(tile_s) == self.z3e_a)
        if row < maze.height - 1 and 0 < col and maze.is_path(col - 1, row + 1):
            dn_tile_req.append(self.z3f_h(tile_s) == self.z3e_b)

        consequent: list[z3_bool_t] = [z3.And([self.z3f_v(tile_s) == self.z3e_a, z3.Or(dn_tile_req)])]

        if row + 1 < maze.height - 1 and maze.is_path(col, row + 2):
            consequent.append(self.direct_v(tile_s))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_v(tile_x) == self.z3e_b, consequent))
        optimizer.add(z3.Implies(self.direct_v(tile_x), consequent))

    def assert_tile_constraint_e(self, optimizer: z3_optimizer_t, maze: maze_t, col: int, row: int) -> None:
        if col >= maze.width - 1:
            return

        tile_x = z3_tile.X(col, row)
        tile_e = z3_tile.E(col, row)

        rt_tile_req: list[z3_bool_t] = [self.z3f_v(tile_e) == self.z3e_o]

        if row < maze.height - 1 and col < maze.width - 1 and maze.is_path(col + 1, row + 1):
            rt_tile_req.append(self.z3f_v(tile_e) == self.z3e_b)
        if 0 < row and col < maze.width - 1 and maze.is_path(col + 1, row - 1):
            rt_tile_req.append(self.z3f_v(tile_e) == self.z3e_a)
        rt_tile_or = z3.Or(rt_tile_req)

        consequent: list[z3_bool_t] = [z3.And([self.z3f_h(tile_e) == self.z3e_b, rt_tile_or])]

        if col + 1 < maze.width - 1 and maze.is_path(col + 2, row):
            consequent.append(self.direct_h(tile_e))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_h(tile_x) == self.z3e_a, consequent))
        optimizer.add(z3.Implies(self.direct_h(tile_x), consequent))

    def assert_tile_constraint_w(self, optimizer: z3_optimizer_t, maze: maze_t, col: int, row: int) -> None:
        if col <= 0:
            return

        tile_x = z3_tile.X(col, row)
        tile_w = z3_tile.W(col, row)

        lt_tile_req: list[z3_bool_t] = [self.z3f_v(tile_w) == self.z3e_o]

        if 0 < col and 0 < row and maze.is_path(col - 1, row - 1):
            lt_tile_req.append(self.z3f_v(tile_w) == self.z3e_a)
        if 0 < col and row < maze.height - 1 and maze.is_path(col - 1, row + 1):
            lt_tile_req.append(self.z3f_v(tile_w) == self.z3e_b)

        consequent: list[z3_bool_t] = [z3.And([self.z3f_h(tile_w) == self.z3e_a, z3.Or(lt_tile_req)])]

        if 0 < col - 1 and maze.is_path(col - 2, row):
            consequent.append(self.direct_h(tile_w))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.z3f_h(tile_x) == self.z3e_b, consequent))
        optimizer.add(z3.Implies(self.direct_h(tile_x), consequent))

    def assert_tile_constraint_origin(self, optimizer: z3_optimizer_t, maze: maze_t, col: int, row: int) -> None:
        tile_x: z3_tile_t = z3_tile.X(col, row)

        # Origin v disjunction
        og_v_tile_req: list[z3_bool_t] = []

        if col < maze.width - 1:
            og_v_tile_req.append(self.z3f_h(z3_tile.E(col, row)) == self.z3e_b)
        if 0 < col:
            og_v_tile_req.append(self.z3f_h(z3_tile.W(col, row)) == self.z3e_a)

        origin_h_or: z3_bool_t = z3.Or(og_v_tile_req)
        optimizer.add(z3.Implies(self.z3f_v(tile_x) == self.z3e_o, origin_h_or))

        # Origin h disjunction
        og_h_tile_req: list[z3_bool_t] = []

        if 0 < row:
            og_h_tile_req.append(self.z3f_v(z3_tile.N(col, row)) == self.z3e_b)
        if row < maze.height - 1:
            og_h_tile_req.append(self.z3f_v(z3_tile.S(col, row)) == self.z3e_a)

        origin_v_or: z3_bool_t = z3.Or(og_h_tile_req)
        optimizer.add(z3.Implies(self.z3f_h(tile_x) == self.z3e_o, origin_v_or))

    def assert_general_tile_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        # Assert tile constraints which hold for any solve.
        for col, row in maze.tiles():
            if not maze.is_path(col, row):
                continue

            self.assert_tile_constraint_n(optimizer, maze, col, row)
            self.assert_tile_constraint_s(optimizer, maze, col, row)
            self.assert_tile_constraint_e(optimizer, maze, col, row)
            self.assert_tile_constraint_w(optimizer, maze, col, row)
            self.assert_tile_constraint_origin(optimizer, maze, col, row)

    # # Assertions, variable

    def assert_anima_is_origin(self, optimizer: z3_optimizer_t, anima: z3_expr_t) -> None:
        # Assert the location of `anima` is an origin tile.
        anima_location: z3_tile_t = (z3f_anima_location_c(anima), z3f_anima_location_r(anima))
        optimizer.add(
            z3.Or(
                [
                    z3.And([self.z3f_h(anima_location) == self.z3e_o, self.z3f_v(anima_location) != self.z3e_o]),
                    z3.And([self.z3f_h(anima_location) != self.z3e_o, self.z3f_v(anima_location) == self.z3e_o]),
                ]
            )
        )

    def assert_hints(self, optimizer: z3_optimizer_t, maze: maze_t, locations: list[location_t]) -> None:
        for col, row in maze.tiles():
            tile_x = z3_tile.X(col, row)
            skip = False

            for idx in range(len(locations)):
                if locations[idx][0] == col and locations[idx][1] == row:
                    skip = True

            if not skip:
                h_d: z3_bool_t = z3.Or(
                    [
                        self.z3f_h(tile_x) == self.z3e_a,
                        self.z3f_h(tile_x) == self.z3e_b,
                        self.z3f_h(tile_x) == self.z3e_x,
                    ]
                )
                v_d: z3_bool_t = z3.Or(
                    [
                        self.z3f_v(tile_x) == self.z3e_a,
                        self.z3f_v(tile_x) == self.z3e_b,
                        self.z3f_v(tile_x) == self.z3e_x,
                    ]
                )

                optimizer.add(h_d)
                optimizer.add(v_d)
