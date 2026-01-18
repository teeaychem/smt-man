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

        self.z3_path_v = z3.Function("path7_type", z3s_bv_t, z3s_bv_t, self.z3e_path_t)

    def print_path(self, maze: maze_t, model: z3_model_t):
        for r in range(0, maze.y):
            bvr = z3s_bv8.cast(r)
            for c in range(0, maze.x):
                bvc = z3s_bv8.cast(c)
                if model.eval(self.z3_path_v(bvc, bvr) != self.EX):
                    print("x", end="")
                else:
                    print(" ", end="")
            print("")

    ## General assertion fns

    def assert_empty_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        for row, col in maze.tiles():
            if maze.is_path(row, col):
                optimizer.add_soft(self.z3_path_v(z3s_bv8.cast(row), z3s_bv8.cast(col)) == self.EX, weight=1)
            else:
                optimizer.add(self.z3_path_v(z3s_bv8.cast(row), z3s_bv8.cast(col)) == self.EX)

    def assert_variable_anima_location(self, optimizer: z3_optimizer_t, anima: z3_expr_t, row: int, col: int) -> None:
        optimizer.add(z3f_anima_location_r(anima) == z3s_bv8.cast(row))
        optimizer.add(z3f_anima_location_c(anima) == z3s_bv8.cast(col))

    def assert_constant_tile_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        for row in range(0, maze.y):
            bvr = z3s_bv8.cast(row)
            for col in range(0, maze.x):
                bvc = z3s_bv8.cast(col)

                if maze.is_path(row, col):
                    tile_x = z3_tile.X(row, col)
                    tile_n = z3_tile.N(row, col)
                    tile_e = z3_tile.E(row, col)
                    tile_s = z3_tile.S(row, col)
                    tile_w = z3_tile.W(row, col)

                    # Up disjunction
                    if row > 0:
                        tile_req_n = [self.z3_path_v(tile_n) == self.OX]
                        if 0 < row - 1 and maze.is_path(row - 2, col):
                            tile_req_n.append(self.z3_path_v(tile_n) == self.NS)
                        if col < maze.x - 1 and 0 < row and maze.is_path(row - 1, col + 1):
                            tile_req_n.append(self.z3_path_v(tile_n) == self.SE)
                        if 0 < col and 0 < row and maze.is_path(row - 1, col - 1):
                            tile_req_n.append(self.z3_path_v(tile_n) == self.SW)
                        tile_or_n = z3.Or(tile_req_n)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NS, tile_or_n))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NE, tile_or_n))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NW, tile_or_n))

                    # Right disjunction
                    if col < maze.x - 1:
                        tile_req_e = [self.z3_path_v(tile_e) == self.OX]
                        if col + 1 < maze.x - 1 and maze.is_path(row, col + 2):
                            tile_req_e.append(self.z3_path_v(tile_e) == self.EW)
                        if row < maze.y - 1 and col < maze.x - 1 and maze.is_path(row + 1, col + 1):
                            tile_req_e.append(self.z3_path_v(tile_e) == self.SW)
                        if 0 < row and col < maze.x - 1 and maze.is_path(row - 1, col + 1):
                            tile_req_e.append(self.z3_path_v(tile_e) == self.NW)
                        tile_or_e = z3.Or(tile_req_e)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.EW, tile_or_e))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NE, tile_or_e))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SE, tile_or_e))

                    # Down disjunction
                    if row < maze.y - 1:
                        tile_req_s = [self.z3_path_v(tile_s) == self.OX]
                        if row + 1 < maze.y - 1 and maze.is_path(row + 2, col):
                            tile_req_s.append(self.z3_path_v(tile_s) == self.NS)
                        if row < maze.y - 1 and col < maze.x - 1 and maze.is_path(row + 1, col + 1):
                            tile_req_s.append(self.z3_path_v(tile_s) == self.NE)
                        if row < maze.y - 1 and 0 < col and maze.is_path(row + 1, col - 1):
                            tile_req_s.append(self.z3_path_v(tile_s) == self.NW)
                        tile_or_s = z3.Or(tile_req_s)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NS, tile_or_s))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SE, tile_or_s))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SW, tile_or_s))

                    # Left disjunction
                    if col > 0:
                        tile_req_w = [self.z3_path_v(tile_w) == self.OX]
                        if 0 < col - 1 and maze.is_path(row, col - 2):
                            tile_req_w.append(self.z3_path_v(tile_w) == self.EW)
                        if 0 < col and 0 < row and maze.is_path(row - 1, col - 1):
                            tile_req_w.append(self.z3_path_v(tile_w) == self.NE)
                        if 0 < col and row < maze.y - 1 and maze.is_path(row + 1, col - 1):
                            tile_req_w.append(self.z3_path_v(tile_w) == self.SE)
                        tile_or_w = z3.Or(tile_req_w)
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.EW, tile_or_w))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.NW, tile_or_w))
                        optimizer.add(z3.Implies(self.z3_path_v(tile_x) == self.SW, tile_or_w))

                    # Origin disjunction
                    og_tile_req = []
                    if row > 0:
                        og_tile_req.append(self.z3_path_v(tile_n) == self.OX)
                        og_tile_req.append(self.z3_path_v(tile_n) == self.SE)
                        og_tile_req.append(self.z3_path_v(tile_n) == self.SW)
                        og_tile_req.append(self.z3_path_v(tile_n) == self.NS)
                    if col < maze.x - 1:
                        og_tile_req.append(self.z3_path_v(tile_e) == self.OX)
                        og_tile_req.append(self.z3_path_v(tile_e) == self.NW)
                        og_tile_req.append(self.z3_path_v(tile_e) == self.SW)
                        og_tile_req.append(self.z3_path_v(tile_e) == self.EW)
                    if row < maze.y - 1:
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
        for row, col in maze.tiles():
            tile_x = z3_tile.X(row, col)
            skip = False

            for idx in range(0, len(locations)):
                if locations[idx][0] == row and locations[idx][1] == col:
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
