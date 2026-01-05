import z3
from smt_man.types import *

z3s_bv8_t: z3_sort_t = z3.BitVecSort(8)
z3_tile_t = tuple[z3_expr_t, z3_expr_t]


class z3s_bv8:
    def cast(val: int) -> z3_expr_t:
        return z3s_bv8_t.cast(val)

    def cast_location(location: location_t) -> z3_tile_t:
        return (z3s_bv8.cast(location[0]), z3s_bv8.cast(location[1]))


class z3_tile:
    def X(col: int, row: int) -> z3_tile_t:
        return z3s_bv8.cast_location((col, row))

    def N(col: int, row: int) -> z3_tile_t:
        return z3s_bv8.cast_location((col, row - 1))

    def E(col: int, row: int) -> z3_tile_t:
        return z3s_bv8.cast_location((col + 1, row))

    def S(col: int, row: int) -> z3_tile_t:
        return z3s_bv8.cast_location((col, row + 1))

    def W(col: int, row: int) -> z3_tile_t:
        return z3s_bv8.cast_location((col - 1, row))


# Anima

z3s_anima_t: z3_sort_t = z3.DeclareSort("Anima")
z3f_anima_location_r: z3_fn_t = z3.Function("anima_location_r", z3s_anima_t, z3s_bv8_t)
z3f_anima_location_c: z3_fn_t = z3.Function("anima_location_c", z3s_anima_t, z3s_bv8_t)

# Path
