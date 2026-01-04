import typing
import z3
import smt_man
import smt_man.mind as mind

import time

from z3 import ExprRef as z3_expr_t
from z3 import SortRef as z3_sort_t
from z3 import DatatypeSortRef as z3_datatype_sort_t
from z3 import FuncDeclRef as z3_fn_t


location_t = tuple[int, int]


maze = smt_man.maze.Maze("./resources/maze/source.txt")
solver = z3.Optimize()
mind.solver_set_defaults(solver)


###

## Base types

BitVec: z3_sort_t = z3.BitVecSort(8)

## Anima

Anima: z3_sort_t = z3.DeclareSort("Anima")
z3f_anima_location_r: z3_fn_t = z3.Function("anima_location_r", Anima, BitVec)
z3f_anima_location_c: z3_fn_t = z3.Function("anima_location_c", Anima, BitVec)

anima_anima: z3_expr_t = z3.Const("anima", Anima)


animas: list[z3_expr_t] = [z3.Const("gottlob", Anima), z3.Const("smtman", Anima)]
anima_locations: list[location_t] = [
    (1, 4),
    (11, 26),
]


## Path

z3_path_enum_return: tuple[z3_datatype_sort_t, list[z3_fn_t]] = z3.EnumSort(
    "path_e",
    ("o", "a", "b", "x"),
    #      0    1    2    3
)
PathEnum: z3_datatype_sort_t = z3_path_enum_return[0]
path_enums: list[z3_fn_t] = z3_path_enum_return[1]

oo: z3_fn_t = path_enums[0]
aa: z3_fn_t = path_enums[1]
bb: z3_fn_t = path_enums[2]
xx: z3_fn_t = path_enums[3]


z3_path_v: z3_fn_t = z3.Function("path_type_v", BitVec, BitVec, PathEnum)
z3_path_h: z3_fn_t = z3.Function("path_type_h", BitVec, BitVec, PathEnum)

## General assertion fns


def assert_path_empty_constraints(maze: smt_man.Maze):
    for r in range(0, maze.height):
        for c in range(0, maze.width):
            this_tile = [BitVec.cast(c), BitVec.cast(r)]
            if maze.is_path(c, r):
                solver.add_soft(z3_path_h(this_tile) == xx, weight=1)
                solver.add_soft(z3_path_v(this_tile) == xx, weight=1)
            else:
                solver.add(z3_path_h(this_tile) == xx)
                solver.add(z3_path_v(this_tile) == xx)


def assert_tile_constraints():
    for r in range(0, maze.height):
        bvr = BitVec.cast(r)
        for c in range(0, maze.width):
            bvc = BitVec.cast(c)

            if maze.is_path(c, r):
                this_tile = [BitVec.cast(c), BitVec.cast(r)]

                up_tile = [BitVec.cast(c), BitVec.cast(r - 1)]
                rt_tile = [BitVec.cast(c + 1), BitVec.cast(r)]
                dn_tile = [BitVec.cast(c), BitVec.cast(r + 1)]
                lt_tile = [BitVec.cast(c - 1), BitVec.cast(r)]

                # Up disjunction
                if r > 0:
                    up_tile_req = [z3_path_h(up_tile) == oo]
                    if c < maze.width - 1 and 0 < r and maze.is_path(c + 1, r - 1):
                        up_tile_req.append(z3_path_h(up_tile) == aa)
                    if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                        up_tile_req.append(z3_path_h(up_tile) == bb)
                    up_tile_or = z3.Or(up_tile_req)
                    consequent = [z3.And([z3_path_v(up_tile) == bb, up_tile_or])]
                    if 0 < r - 1 and maze.is_path(c, r - 2):
                        consequent.append(z3.And([z3_path_h(up_tile) == xx, z3_path_v(up_tile) == aa]))
                    consequent = z3.Or(consequent)
                    solver.add(z3.Implies(z3_path_v(this_tile) == aa, consequent))
                    solver.add(z3.Implies(z3.And([z3_path_v(this_tile) == aa, z3_path_h(this_tile) == xx]), consequent))

                # Down disjunction
                if r < maze.height - 1:
                    dn_tile_req = [z3_path_h(dn_tile) == oo]
                    if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                        dn_tile_req.append(z3_path_h(dn_tile) == aa)
                    if r < maze.height - 1 and 0 < c and maze.is_path(c - 1, r + 1):
                        dn_tile_req.append(z3_path_h(dn_tile) == bb)
                    dn_tile_or = z3.Or(dn_tile_req)
                    consequent = [z3.And([z3_path_v(dn_tile) == aa, dn_tile_or])]
                    if r + 1 < maze.height - 1 and maze.is_path(c, r + 2):
                        consequent.append(z3.And([z3_path_h(dn_tile) == xx, z3_path_v(dn_tile) == aa]))
                    consequent = z3.Or(consequent)
                    solver.add(z3.Implies(z3_path_v(this_tile) == bb, consequent))
                    solver.add(z3.Implies(z3.And([z3_path_v(this_tile) == aa, z3_path_h(this_tile) == xx]), consequent))

                # Right disjunction
                if c < maze.width - 1:
                    rt_tile_req = [z3_path_v(rt_tile) == oo]
                    if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                        rt_tile_req.append(z3_path_v(rt_tile) == bb)
                    if 0 < r and c < maze.width - 1 and maze.is_path(c + 1, r - 1):
                        rt_tile_req.append(z3_path_v(rt_tile) == aa)
                    rt_tile_or = z3.Or(rt_tile_req)
                    consequent = [z3.And([z3_path_h(rt_tile) == bb, rt_tile_or])]
                    if c + 1 < maze.width - 1 and maze.is_path(c + 2, r):
                        consequent.append(z3.And([z3_path_v(rt_tile) == xx, z3_path_h(rt_tile) == aa]))
                    consequent = z3.Or(consequent)
                    solver.add(z3.Implies(z3_path_h(this_tile) == aa, consequent))
                    solver.add(z3.Implies(z3.And([z3_path_h(this_tile) == aa, z3_path_v(this_tile) == xx]), consequent))

                # Left disjunction
                if c > 0:
                    lt_tile_req = [z3_path_v(lt_tile) == oo]
                    if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                        lt_tile_req.append(z3_path_v(lt_tile) == aa)
                    if 0 < c and r < maze.height - 1 and maze.is_path(c - 1, r + 1):
                        lt_tile_req.append(z3_path_v(lt_tile) == bb)
                    lt_tile_or = z3.Or(lt_tile_req)
                    consequent = [z3.And([z3_path_h(lt_tile) == aa, lt_tile_or])]
                    if 0 < c - 1 and maze.is_path(c - 2, r):
                        consequent.append(z3.And([z3_path_v(lt_tile) == xx, z3_path_h(lt_tile) == aa]))
                    consequent = z3.Or(consequent)
                    solver.add(z3.Implies(z3_path_h(this_tile) == bb, consequent))
                    solver.add(z3.Implies(z3.And([z3_path_h(this_tile) == aa, z3_path_v(this_tile) == xx]), consequent))

                # Origin v disjunction
                og_v_tile_req = []
                if c < maze.width - 1:
                    og_v_tile_req.append(z3_path_h(rt_tile) == bb)
                if 0 < c:
                    og_v_tile_req.append(z3_path_h(lt_tile) == aa)
                origin_h_or = z3.Or(og_v_tile_req)
                solver.add(z3.Implies(z3_path_v(this_tile) == oo, origin_h_or))

                # Origin h disjunction
                og_h_tile_req = []
                if 0 < r:
                    og_h_tile_req.append(z3_path_v(up_tile) == bb)
                if r < maze.height - 1:
                    og_h_tile_req.append(z3_path_v(dn_tile) == aa)
                origin_v_or = z3.Or(og_h_tile_req)
                solver.add(z3.Implies(z3_path_h(this_tile) == oo, origin_v_or))


## Specific assertion fns


def anima_is_origin(anima: z3_expr_t):
    anima_location = [z3f_anima_location_c(anima), z3f_anima_location_r(anima)]
    solver.add(
        z3.Or(
            [
                z3.And([z3_path_h(anima_location) == oo, z3_path_v(anima_location) != oo]),
                z3.And([z3_path_h(anima_location) != oo, z3_path_v(anima_location) == oo]),
            ]
        )
    )


def assert_path_hints():
    for r in range(0, maze.height):
        for c in range(0, maze.width):
            this_tile = [BitVec.cast(c), BitVec.cast(r)]
            skip = False

            for anima_id in range(len(animas)):
                if anima_locations[anima_id][0] == c and anima_locations[anima_id][1] == r:
                    skip = True

            if not skip:
                solver.add(z3.Or([z3_path_h(this_tile) == aa, z3_path_h(this_tile) == bb, z3_path_h(this_tile) == xx]))
                solver.add(z3.Or([z3_path_v(this_tile) == aa, z3_path_v(this_tile) == bb, z3_path_v(this_tile) == xx]))


def assert_anima_location(anima_id: int):
    solver.add(z3f_anima_location_c(animas[id]) == BitVec.cast(anima_locations[id][0]))
    solver.add(z3f_anima_location_r(animas[id]) == BitVec.cast(anima_locations[id][1]))


assert_path_empty_constraints(maze)
assert_tile_constraints()

for id in range(len(animas)):
    assert_anima_location(id)

for anima in animas:
    anima_is_origin(anima)
assert_path_hints()


time_solve_start = time.perf_counter()
time_solve_end = 0

result = solver.check()
time_solve_end = time.perf_counter()
print(f"Result: {result} in {time_solve_end - time_solve_start:0.4f} seconds")

if result == z3.sat:
    print(solver.statistics())

    model = solver.model()

    for r in range(0, maze.height):
        bvr = BitVec.cast(r)
        for c in range(0, maze.width):
            bvc = BitVec.cast(c)
            if model.eval(z3_path_h(bvc, bvr) != xx) or model.eval(z3_path_v(bvc, bvr) != xx):
                print("x", end="")
            else:
                print(" ", end="")
        print("")

    print(model)


# print(solver.help())
