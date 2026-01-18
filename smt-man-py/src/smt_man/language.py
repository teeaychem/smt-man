import z3

from smt_man.types import *

anima_id_t = int
location_t = tuple[int, int]
z3_tile_t = tuple[z3_expr_t, z3_expr_t]
z3s_bv_t: z3_sort_t = z3.BitVecSort(6)

# Anima

z3s_anima_t: z3_sort_t = z3.DeclareSort("anima_t")

z3f_anima_location_c: z3_fn_t = z3.Function("anima_c", z3s_anima_t, z3s_bv_t)
z3f_anima_location_r: z3_fn_t = z3.Function("anima_r", z3s_anima_t, z3s_bv_t)

# Persona

z3s_persona_t: z3_sort_t = z3.DeclareSort("persona_t")

z3f_persona_location_c: z3_fn_t = z3.Function("persona_c", z3s_persona_t, z3s_bv_t)
z3f_persona_location_r: z3_fn_t = z3.Function("persona_r", z3s_persona_t, z3s_bv_t)


# Interfaces


class z3s_bv8:
    def cast(val: int) -> z3_expr_t:
        return z3s_bv_t.cast(val)

    def cast_location(location: location_t) -> z3_tile_t:
        return (z3s_bv8.cast(location[0]), z3s_bv8.cast(location[1]))


class z3_tile:
    def X(row: int, col: int) -> z3_tile_t:
        return z3s_bv8.cast_location((row, col))

    def N(row: int, col: int) -> z3_tile_t:
        return z3s_bv8.cast_location((row - 1, col))

    def E(row: int, col: int) -> z3_tile_t:
        return z3s_bv8.cast_location((row, col + 1))

    def S(row: int, col: int) -> z3_tile_t:
        return z3s_bv8.cast_location((row + 1, col))

    def W(row: int, col: int) -> z3_tile_t:
        return z3s_bv8.cast_location((row, col - 1))
