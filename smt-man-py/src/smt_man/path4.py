import z3

from smt_man.language import *
from smt_man.types import *
from smt_man.maze import maze_t
import smt_man


class path4_t:
    def __init__(self) -> None:
        self.z3_return: tuple[z3_datatype_sort_t, list[z3_fn_t]] = z3.EnumSort(
            "path4_e",
            (
                "o",
                "a",
                "b",
                "x",
            ),
        )
        self.z3_t: z3_datatype_sort_t = self.z3_return[0]
        self.z3e: list[z3_fn_t] = self.z3_return[1]

        self.z3e_o: z3_fn_t = self.z3e[0]
        self.z3e_a: z3_fn_t = self.z3e[1]
        self.z3e_b: z3_fn_t = self.z3e[2]
        self.z3e_x: z3_fn_t = self.z3e[3]

        self.z3f_v: z3_fn_t = z3.Function("path4_type_v", z3s_bv_t, z3s_bv_t, self.z3_t)
        self.z3f_h: z3_fn_t = z3.Function("path4_type_h", z3s_bv_t, z3s_bv_t, self.z3_t)

        self.penalty: str = "path_penatly"

    def to_string(self, maze: maze_t, model: z3_model_t) -> str:
        path_string = ""

        for row in range(0, maze.rows):
            for col in range(0, maze.cols):
                tile_x: z3_tile_t = z3_tile.X(row, col)

                path_h: z3_expr_t = model.eval(self.tile_h_is_not(tile_x, self.z3e_x))
                path_v: z3_expr_t = model.eval(self.tile_v_is_not(tile_x, self.z3e_x))

                if path_h or path_v:
                    path_string += "x"
                else:
                    path_string += " "
            path_string += f"| {row}\n"

        return path_string

    def direct_h(self, tile: z3_tile_t) -> z3_bool_t:
        return z3.And([self.tile_v_is(tile, self.z3e_x), self.tile_h_is(tile, self.z3e_a)])

    def direct_v(self, tile: z3_tile_t) -> z3_bool_t:
        return z3.And([self.tile_v_is(tile, self.z3e_a), self.tile_h_is(tile, self.z3e_x)])

    def tile_h_is(self, tile: z3_tile_t, enum: z3_fn_t) -> z3_bool_t:
        return self.z3f_h(tile) == enum

    def tile_h_is_not(self, tile: z3_tile_t, enum: z3_fn_t) -> z3_bool_t:
        # return z3.Or([self.z3f_h(tile) == e for e in self.z3e if e is not enum])
        return self.z3f_h(tile) != enum

    def tile_v_is(self, tile: z3_tile_t, enum: z3_fn_t) -> z3_bool_t:
        return self.z3f_v(tile) == enum

    def tile_v_is_not(self, tile: z3_tile_t, enum: z3_fn_t) -> z3_bool_t:
        # return z3.Or([self.z3f_v(tile) == e for e in self.z3e if e is not enum])
        return self.z3f_v(tile) != enum

    # # Assertions, constant

    def assert_empty_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        for row, col in maze.tiles():
            tile_x: z3_tile_t = z3_tile.X(row, col)

            if maze.is_path(row, col):
                optimizer.add_soft(z3.And([self.tile_h_is(tile_x, self.z3e_x), self.tile_v_is(tile_x, self.z3e_x)]), weight=1, id=self.penalty)
            else:
                optimizer.add(self.tile_h_is(tile_x, self.z3e_x))
                optimizer.add(self.tile_v_is(tile_x, self.z3e_x))

    def assert_variable_anima_location(self, optimizer: z3_optimizer_t, anima: z3_expr_t, row: int, col: int) -> None:
        optimizer.add(z3f_anima_location_r(anima) == z3s_bv8.cast(row))
        optimizer.add(z3f_anima_location_c(anima) == z3s_bv8.cast(col))

    def assert_variable_persona_location(self, optimizer: z3_optimizer_t, persona: z3_expr_t, row: int, col: int) -> None:
        optimizer.add(z3f_persona_location_r(persona) == z3s_bv8.cast(row))
        optimizer.add(z3f_persona_location_c(persona) == z3s_bv8.cast(col))

    def assert_tile_constraint_n(self, optimizer: z3_optimizer_t, maze: maze_t, row: int, col: int) -> None:
        if not 0 < row:
            return

        tile_x: z3_tile_t = z3_tile.X(row, col)
        tile_n: z3_tile_t = z3_tile.N(row, col)

        options: list[z3_bool_t] = [self.tile_h_is(tile_n, self.z3e_o)]

        if maze.is_path(row - 1, col + 1):
            options.append(self.tile_h_is(tile_n, self.z3e_a))
        if maze.is_path(row - 1, col - 1):
            options.append(self.tile_h_is(tile_n, self.z3e_b))

        consequent: list[z3_bool_t] = [z3.And([self.tile_v_is(tile_n, self.z3e_b), z3.Or(options)])]

        if maze.is_path(row - 2, col):
            consequent.append(self.direct_v(tile_n))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.tile_v_is(tile_x, self.z3e_a), consequent))
        optimizer.add(z3.Implies(self.direct_v(tile_x), consequent))

    def assert_tile_constraint_s(self, optimizer: z3_optimizer_t, maze: maze_t, row: int, col: int) -> None:
        if not row + 1 < maze.rows:
            return

        tile_x: z3_tile_t = z3_tile.X(row, col)
        tile_s: z3_tile_t = z3_tile.S(row, col)

        options: list[z3_bool_t] = [self.tile_h_is(tile_s, self.z3e_o)]

        if maze.is_path(row + 1, col + 1):
            options.append(self.tile_h_is(tile_s, self.z3e_a))
        if maze.is_path(row + 1, col - 1):
            options.append(self.tile_h_is(tile_s, self.z3e_b))

        consequent: list[z3_bool_t] = [z3.And([self.tile_v_is(tile_s, self.z3e_a), z3.Or(options)])]

        if maze.is_path(row + 2, col):
            consequent.append(self.direct_v(tile_s))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.tile_v_is(tile_x, self.z3e_b), consequent))
        optimizer.add(z3.Implies(self.direct_v(tile_x), consequent))

    def assert_tile_constraint_e(self, optimizer: z3_optimizer_t, maze: maze_t, row: int, col: int) -> None:
        if not col + 1 < maze.cols:
            return

        tile_x: z3_tile_t = z3_tile.X(row, col)
        tile_e: z3_tile_t = z3_tile.E(row, col)

        options: list[z3_bool_t] = [self.tile_v_is(tile_e, self.z3e_o)]

        if maze.is_path(row - 1, col + 1):
            options.append(self.tile_v_is(tile_e, self.z3e_a))
        if maze.is_path(row + 1, col + 1):
            options.append(self.tile_v_is(tile_e, self.z3e_b))

        consequent: list[z3_bool_t] = [z3.And([self.tile_h_is(tile_e, self.z3e_b), z3.Or(options)])]

        if maze.is_path(row, col + 2):
            consequent.append(self.direct_h(tile_e))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.tile_h_is(tile_x, self.z3e_a), consequent))
        optimizer.add(z3.Implies(self.direct_h(tile_x), consequent))

    def assert_tile_constraint_w(self, optimizer: z3_optimizer_t, maze: maze_t, row: int, col: int) -> None:
        if not 0 < col:
            return

        tile_x: z3_tile_t = z3_tile.X(row, col)
        tile_w: z3_tile_t = z3_tile.W(row, col)

        options: list[z3_bool_t] = [self.tile_v_is(tile_w, self.z3e_o)]

        if maze.is_path(row - 1, col - 1):
            options.append(self.tile_v_is(tile_w, self.z3e_a))
        if maze.is_path(row + 1, col - 1):
            options.append(self.tile_v_is(tile_w, self.z3e_b))

        consequent: list[z3_bool_t] = [z3.And([self.tile_h_is(tile_w, self.z3e_a), z3.Or(options)])]

        if maze.is_path(row, col - 2):
            consequent.append(self.direct_h(tile_w))

        consequent: z3_bool_t = z3.Or(consequent)

        optimizer.add(z3.Implies(self.tile_h_is(tile_x, self.z3e_b), consequent))
        optimizer.add(z3.Implies(self.direct_h(tile_x), consequent))

    def assert_tile_constraint_o(self, optimizer: z3_optimizer_t, maze: maze_t, row: int, col: int) -> None:
        tile_x: z3_tile_t = z3_tile.X(row, col)

        # Origin v disjunction
        og_v_tile_req: list[z3_bool_t] = []

        if maze.is_path(row, col + 1):
            og_v_tile_req.append(self.tile_h_is(z3_tile.E(row, col), self.z3e_b))
        if maze.is_path(row, col + 2):
            og_v_tile_req.append(self.direct_h(z3_tile.E(row, col)))
        if maze.is_path(row, col - 1):
            og_v_tile_req.append(self.tile_h_is(z3_tile.W(row, col), self.z3e_a))
        if maze.is_path(row, col - 2):
            og_v_tile_req.append(self.direct_h(z3_tile.W(row, col)))

        optimizer.add(z3.Implies(self.tile_v_is(tile_x, self.z3e_o), z3.Or(og_v_tile_req)))

        del og_v_tile_req

        # Origin h disjunction
        og_h_tile_req: list[z3_bool_t] = []

        if maze.is_path(row - 1, col):
            og_h_tile_req.append(self.tile_v_is(z3_tile.N(row, col), self.z3e_b))
        if maze.is_path(row - 2, col):
            og_h_tile_req.append(self.direct_v(z3_tile.N(row, col)))
        if maze.is_path(row + 1, col):
            og_h_tile_req.append(self.tile_v_is(z3_tile.S(row, col), self.z3e_a))
        if maze.is_path(row + 2, col):
            og_h_tile_req.append(self.direct_v(z3_tile.S(row, col)))

        optimizer.add(z3.Implies(self.tile_h_is(tile_x, self.z3e_o), z3.Or(og_h_tile_req)))

        del og_h_tile_req

    def assert_constant_tile_constraints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        # Assert tile constraints which hold for any solve.
        for row, col in maze.tiles():
            if not maze.is_path(row, col):
                continue

            self.assert_tile_constraint_n(optimizer, maze, row, col)
            self.assert_tile_constraint_s(optimizer, maze, row, col)
            self.assert_tile_constraint_e(optimizer, maze, row, col)
            self.assert_tile_constraint_w(optimizer, maze, row, col)
            self.assert_tile_constraint_o(optimizer, maze, row, col)

    # # Assertions, variable

    def assert_anima_is_origin(self, optimizer: z3_optimizer_t, anima: z3_expr_t) -> None:
        # Assert the location of `anima` is an origin tile.
        anima_location: z3_tile_t = (z3f_anima_location_r(anima), z3f_anima_location_c(anima))
        optimizer.add(
            z3.Or(
                [
                    z3.And(
                        [
                            self.tile_h_is(anima_location, self.z3e_o),
                            self.tile_v_is_not(anima_location, self.z3e_o),
                        ]
                    ),
                    z3.And(
                        [
                            self.tile_h_is_not(anima_location, self.z3e_o),
                            self.tile_v_is(anima_location, self.z3e_o),
                        ]
                    ),
                ]
            )
        )

    def assert_persona_is_origin(self, optimizer: z3_optimizer_t, persona: z3_expr_t) -> None:
        # Assert the location of `persona` is an origin tile.
        persona_location: z3_tile_t = (z3f_persona_location_r(persona), z3f_persona_location_c(persona))
        optimizer.add(
            z3.Or(
                [
                    z3.And(
                        [
                            self.tile_h_is(persona_location, self.z3e_o),
                            self.tile_v_is_not(persona_location, self.z3e_o),
                        ]
                    ),
                    z3.And(
                        [
                            self.tile_h_is_not(persona_location, self.z3e_o),
                            self.tile_v_is(persona_location, self.z3e_o),
                        ]
                    ),
                ]
            )
        )

    def assert_variable_hints(self, optimizer: z3_optimizer_t, maze: maze_t, locations: list[location_t]) -> None:
        for row, col in maze.tiles():
            tile_x: z3_tile_t = z3_tile.X(row, col)
            skip = False

            for idx in range(len(locations)):
                if locations[idx][0] == row and locations[idx][1] == col:
                    skip = True

            if not skip:
                h_d: z3_bool_t = z3.Or(
                    [
                        self.tile_h_is(tile_x, self.z3e_a),
                        self.tile_h_is(tile_x, self.z3e_b),
                        self.tile_h_is(tile_x, self.z3e_x),
                    ]
                )
                v_d: z3_bool_t = z3.Or(
                    [
                        self.tile_v_is(tile_x, self.z3e_a),
                        self.tile_v_is(tile_x, self.z3e_b),
                        self.tile_v_is(tile_x, self.z3e_x),
                    ]
                )

                optimizer.add(h_d)
                optimizer.add(v_d)

    # Redundant, though a significant boost to (some) solves
    def assert_constant_hints(self, optimizer: z3_optimizer_t, maze: maze_t) -> None:
        for row, col in maze.tiles():
            tile_x: z3_tile_t = z3_tile.X(row, col)

            disjuncts_h: z3_bool_t = z3.Or(
                [
                    self.tile_h_is(tile_x, self.z3e_a),
                    self.tile_h_is(tile_x, self.z3e_b),
                    self.tile_h_is(tile_x, self.z3e_x),
                ]
            )
            optimizer.add(z3.Implies(self.tile_h_is_not(tile_x, self.z3e_o), disjuncts_h))

            del disjuncts_h

            disjuncts_v: z3_bool_t = z3.Or(
                [
                    self.tile_v_is(tile_x, self.z3e_a),
                    self.tile_v_is(tile_x, self.z3e_b),
                    self.tile_v_is(tile_x, self.z3e_x),
                ]
            )
            optimizer.add(z3.Implies(self.tile_v_is_not(tile_x, self.z3e_o), disjuncts_v))

            del disjuncts_v

    def assert_constant_origin_is_anima_or_persona(self, optimizer: z3_optimizer_t, maze: maze_t, animas: list[z3_expr_t], persona: z3_expr_t) -> None:
        for row, col in maze.tiles():
            tile_x: z3_tile_t = z3_tile.X(row, col)

            disjuncts: list[z3_bool_t] = [z3.And([z3f_persona_location_c(persona) == col, z3f_persona_location_r(persona) == row])]
            for anima in animas:
                disjuncts.append(z3.And([z3f_anima_location_r(anima) == row, z3f_anima_location_c(anima) == col]))

            optimizer.add(z3.Implies(self.tile_h_is(tile_x, self.z3e_o), z3.Or(disjuncts)))
            optimizer.add(z3.Implies(self.tile_v_is(tile_x, self.z3e_o), z3.Or(disjuncts)))
