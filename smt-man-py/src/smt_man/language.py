import z3
from smt_man.types import *

z3s_bv_t: z3_sort_t = z3.BitVecSort(8)

# Anima

z3s_anima_t: z3_sort_t = z3.DeclareSort("Anima")
z3f_anima_location_r: z3_fn_t = z3.Function("anima_location_r", z3s_anima_t, z3s_bv_t)
z3f_anima_location_c: z3_fn_t = z3.Function("anima_location_c", z3s_anima_t, z3s_bv_t)

# Path
