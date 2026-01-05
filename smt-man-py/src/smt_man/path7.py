from smt_man import maze_t
import z3

from smt_man.language import *


class path7_t:
    def __init__(self):
        self.z3_return: tuple[z3_datatype_sort_t, list[z3_fn_t]] = z3.EnumSort(
            "path7_e",
            ("O", "NS", "EW", "NE", "SE", "SW", "NW", "X"),
        )
        self.z3e_path_t = self.z3_return[0]
        self.z3e_path = self.z3_return[1]

        self.OX = self.z3e_path[0]

        self.NS = self.z3e_path[1]
        self.EW = self.z3e_path[2]

        self.NE = self.z3e_path[3]
        self.SE = self.z3e_path[4]
        self.SW = self.z3e_path[5]
        self.NW = self.z3e_path[6]
        self.EX = self.z3e_path[7]

        self.z3_path_v = z3.Function("path7_type", z3s_bv8_t, z3s_bv8_t, self.z3e_path_t)

    def print_path(self, maze: maze_t, model: z3_model_t):
        for r in range(0, maze.height):
            bvr = z3s_bv8.cast(r)
            for c in range(0, maze.width):
                bvc = z3s_bv8.cast(c)
                if model.eval(self.z3_path_v(bvc, bvr) != self.EX):
                    print("x", end="")
                else:
                    print(" ", end="")
            print("")

    ## General assertion fns

    def assert_empty_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        for col, row in maze.tiles():
            if maze.is_path(col, row):
                optimizer.add_soft(self.z3_path_v(z3s_bv8.cast(col), z3s_bv8.cast(row)) == self.EX, weight=1)
            else:
                optimizer.add(self.z3_path_v(z3s_bv8.cast(col), z3s_bv8.cast(row)) == self.EX)

    def assert_variable_anima_location(self, optimizer: z3_optimizer_t, anima: z3_expr_t, col: int, row: int) -> None:
        optimizer.add(z3f_anima_location_c(anima) == z3s_bv8.cast(col))
        optimizer.add(z3f_anima_location_r(anima) == z3s_bv8.cast(row))

    def assert_constant_tile_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        for row in range(0, maze.height):
            bvr = z3s_bv8.cast(row)
            for col in range(0, maze.width):
                bvc = z3s_bv8.cast(col)

                if maze.is_path(col, row):
                    tile_x = z3_tile.X(col, row)
                    tile_n = z3_tile.N(col, row)
                    tile_e = z3_tile.E(col, row)
                    tile_s = z3_tile.S(col, row)
                    tile_w = z3_tile.W(col, row)

                    # Up disjunction
                    if row > 0:
                        up_tile_req = [self.z3_path_v(tile_n) == self.OX]
                        if 0 < row - 1 and maze.is_path(col, row - 2):
                            up_tile_req.append(self.z3_path_v(tile_n) == self.NS)
                        if col < maze.width - 1 and 0 < row and maze.is_path(col + 1, row - 1):
                            up_tile_req.append(self.z3_path_v(tile_n) == self.SE)
                        if 0 < col and 0 < row and maze.is_path(col - 1, row - 1):
                            up_tile_req.append(self.z3_path_v(tile_n) == self.SW)
                        up_tile_or = z3.Or(up_tile_req)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NS, up_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NE, up_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NW, up_tile_or))

                    # Right disjunction
                    if col < maze.width - 1:
                        rt_tile_req = [self.z3_path_v(tile_e) == self.OX]
                        if col + 1 < maze.width - 1 and maze.is_path(col + 2, row):
                            rt_tile_req.append(self.z3_path_v(tile_e) == self.EW)
                        if row < maze.height - 1 and col < maze.width - 1 and maze.is_path(col + 1, row + 1):
                            rt_tile_req.append(self.z3_path_v(tile_e) == self.SW)
                        if 0 < row and col < maze.width - 1 and maze.is_path(col + 1, row - 1):
                            rt_tile_req.append(self.z3_path_v(tile_e) == self.NW)
                        rt_tile_or = z3.Or(rt_tile_req)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.EW, rt_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NE, rt_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SE, rt_tile_or))

                    # Down disjunction
                    if row < maze.height - 1:
                        dn_tile_req = [self.z3_path_v(tile_s) == self.OX]
                        if row + 1 < maze.height - 1 and maze.is_path(col, row + 2):
                            dn_tile_req.append(self.z3_path_v(tile_s) == self.NS)
                        if row < maze.height - 1 and col < maze.width - 1 and maze.is_path(col + 1, row + 1):
                            dn_tile_req.append(self.z3_path_v(tile_s) == self.NE)
                        if row < maze.height - 1 and 0 < col and maze.is_path(col - 1, row + 1):
                            dn_tile_req.append(self.z3_path_v(tile_s) == self.NW)
                        dn_tile_or = z3.Or(dn_tile_req)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NS, dn_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SE, dn_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SW, dn_tile_or))

                    # Left disjunction
                    if col > 0:
                        lt_tile_req = [self.z3_path_v(tile_w) == self.OX]
                        if 0 < col - 1 and maze.is_path(col - 2, row):
                            lt_tile_req.append(self.z3_path_v(tile_w) == self.EW)
                        if 0 < col and 0 < row and maze.is_path(col - 1, row - 1):
                            lt_tile_req.append(self.z3_path_v(tile_w) == self.NE)
                        if 0 < col and row < maze.height - 1 and maze.is_path(col - 1, row + 1):
                            lt_tile_req.append(self.z3_path_v(tile_w) == self.SE)
                        lt_tile_or = z3.Or(lt_tile_req)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.EW, lt_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NW, lt_tile_or))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SW, lt_tile_or))

                    # Origin disjunction
                    og_tile_req = []
                    if row > 0:
                        og_tile_req.append(self.z3_path_v(tile_n) == self.OX)
                        og_tile_req.append(self.z3_path_v(tile_n) == self.SE)
                        og_tile_req.append(self.z3_path_v(tile_n) == self.SW)
                        og_tile_req.append(self.z3_path_v(tile_n) == self.NS)
                    if col < maze.width - 1:
                        og_tile_req.append(self.z3_path_v(tile_e) == self.OX)
                        og_tile_req.append(self.z3_path_v(tile_e) == self.NW)
                        og_tile_req.append(self.z3_path_v(tile_e) == self.SW)
                        og_tile_req.append(self.z3_path_v(tile_e) == self.EW)
                    if row < maze.height - 1:
                        og_tile_req.append(self.z3_path_v(tile_s) == self.OX)
                        og_tile_req.append(self.z3_path_v(tile_s) == self.NW)
                        og_tile_req.append(self.z3_path_v(tile_s) == self.NE)
                        og_tile_req.append(self.z3_path_v(tile_s) == self.NS)
                    if col > 0:
                        og_tile_req.append(self.z3_path_v(tile_w) == self.OX)
                        og_tile_req.append(self.z3_path_v(tile_w) == self.NE)
                        og_tile_req.append(self.z3_path_v(tile_w) == self.SE)
                        og_tile_req.append(self.z3_path_v(tile_w) == self.EW)
                    origin_or = z3.Or(og_tile_req)
                    optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.OX, origin_or))

    ## Specific assertion fns

    def assert_anima_is_origin(self, optimizer: z3_optimizer_t, anima: z3_expr_t) -> None:
        optimizer.add(self.z3_path_v(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == self.OX)

    def assert_variable_hints(self, optimizer: z3_optimizer_t, maze: maze_t, locations: list[location_t]) -> None:
        for col, row in maze.tiles():
            tile_x = z3_tile.X(col, row)
            skip = False

            for idx in range(0, len(locations)):
                if locations[idx][0] == col and locations[idx][1] == row:
                    skip = True

            if not skip:
                optimizer.add(
                    z3.Or(
                        [
                            self.z3_path_v(tile_x) == self.NS,
                            self.z3_path_v(tile_x) == self.EW,
                            self.z3_path_v(tile_x) == self.NE,
                            self.z3_path_v(tile_x) == self.SE,
                            self.z3_path_v(tile_x) == self.SW,
                            self.z3_path_v(tile_x) == self.NW,
                            self.z3_path_v(tile_x) == self.EX,
                        ]
                    )
                )
