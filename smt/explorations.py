import time

import z3

import smt_man
import smt_man.mind as mind
from smt_man.types import *
from smt_man.language import *

anima_locations = {
    "gottlob": [1, 1],
    "smtman": [10, 26],
}


maze = smt_man.maze.Maze("./resources/maze/source.txt")


# print(z3.tactics())
# for tactic in z3.tactics():
#     print(f"{tactic}:\n\t{z3.tactic_description(tactic)}")
# print(z3.main_ctx().param_descrs())

# solver = Solver()

optimizer = z3.Optimize()
mind.set_defaults(optimizer)

optimizer.set("incremental", True)
optimizer.set("maxsat_engine", "wmax")

# solver.set("priority", "box")

# solver.set("enable_lns", True)
# solver.set("enable_sat", False)
# solver.set("enable_sls", True)
# solver.set("optsmt_engine", "symba")
# solver.set("pb.compile_equality", True)


# solver.set("ctrl_c", False)
# solver.set("pb.compile_equality", True)
# solver.set("maxres.maximize_assignment", True)

# solver.set("maxsat_engine", "maxres")
# solver.set("maxsat_engine", "pd-maxres")
# solver.set("maxsat_engine", "rc2")
# solver.set("maxsat_engine", "maxres-bin")


###


animas = (z3.Const("gottlob", z3s_anima_t), z3.Const("smtman", z3s_anima_t))
anima_gottlob = animas[0]
anima_smtman = animas[1]

## Path

PathEnum, path_enums = z3.EnumSort(
    "path_e",
    ("og", "ud", "rl", "ur", "rd", "dl", "lu", "xx"),
    # 0     1     2     3     4     5     6     7
)

o_g = path_enums[0]

u_d = path_enums[1]
r_l = path_enums[2]

r_u = path_enums[3]
r_d = path_enums[4]
l_d = path_enums[5]
l_u = path_enums[6]
x_x = path_enums[7]

z3_path_v = z3.Function("path_type", z3s_bv8_t, z3s_bv8_t, PathEnum)

## General assertion fns


def assert_path_empty_constraints():
    for r in range(0, maze.height):
        for c in range(0, maze.width):
            if maze.is_path(c, r):
                optimizer.add_soft(z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == x_x, weight=1)
            else:
                optimizer.add(z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == x_x)


def assert_anima_locations():
    optimizer.add(z3f_anima_location_c(anima_gottlob) == z3s_bv8_t.cast(anima_locations["gottlob"][0]))
    optimizer.add(z3f_anima_location_r(anima_gottlob) == z3s_bv8_t.cast(anima_locations["gottlob"][1]))

    optimizer.add(z3f_anima_location_c(anima_smtman) == z3s_bv8_t.cast(anima_locations["smtman"][0]))
    optimizer.add(z3f_anima_location_r(anima_smtman) == z3s_bv8_t.cast(anima_locations["smtman"][1]))


def assert_tile_constraints():
    for r in range(0, maze.height):
        bvr = z3s_bv8_t.cast(r)
        for c in range(0, maze.width):
            bvc = z3s_bv8_t.cast(c)

            if maze.is_path(c, r):
                this_tile = [z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)]
                up_tile = [z3s_bv8_t.cast(c), z3s_bv8_t.cast(r - 1)]
                rt_tile = [z3s_bv8_t.cast(c + 1), z3s_bv8_t.cast(r)]
                dn_tile = [z3s_bv8_t.cast(c), z3s_bv8_t.cast(r + 1)]
                lt_tile = [z3s_bv8_t.cast(c - 1), z3s_bv8_t.cast(r)]

                # Up disjunction
                if r > 0:
                    up_tile_req = [z3_path_v(up_tile) == o_g]
                    if 0 < r - 1 and maze.is_path(c, r - 2):
                        up_tile_req.append(z3_path_v(up_tile) == u_d)
                    if c < maze.width - 1 and 0 < r and maze.is_path(c + 1, r - 1):
                        up_tile_req.append(z3_path_v(up_tile) == r_d)
                    if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                        up_tile_req.append(z3_path_v(up_tile) == l_d)
                    up_tile_or = z3.Or(up_tile_req)
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == u_d, up_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == r_u, up_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == l_u, up_tile_or))

                # Right disjunction
                if c < maze.width - 1:
                    rt_tile_req = [z3_path_v(rt_tile) == o_g]
                    if c + 1 < maze.width - 1 and maze.is_path(c + 2, r):
                        rt_tile_req.append(z3_path_v(rt_tile) == r_l)
                    if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                        rt_tile_req.append(z3_path_v(rt_tile) == l_d)
                    if 0 < r and c < maze.width - 1 and maze.is_path(c + 1, r - 1):
                        rt_tile_req.append(z3_path_v(rt_tile) == l_u)
                    rt_tile_or = z3.Or(rt_tile_req)
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == r_l, rt_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == r_u, rt_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == r_d, rt_tile_or))

                # Down disjunction
                if r < maze.height - 1:
                    dn_tile_req = [z3_path_v(dn_tile) == o_g]
                    if r + 1 < maze.height - 1 and maze.is_path(c, r + 2):
                        dn_tile_req.append(z3_path_v(dn_tile) == u_d)
                    if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                        dn_tile_req.append(z3_path_v(dn_tile) == r_u)
                    if r < maze.height - 1 and 0 < c and maze.is_path(c - 1, r + 1):
                        dn_tile_req.append(z3_path_v(dn_tile) == l_u)
                    dn_tile_or = z3.Or(dn_tile_req)
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == u_d, dn_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == r_d, dn_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == l_d, dn_tile_or))

                # Left disjunction
                if c > 0:
                    lt_tile_req = [z3_path_v(lt_tile) == o_g]
                    if 0 < c - 1 and maze.is_path(c - 2, r):
                        lt_tile_req.append(z3_path_v(lt_tile) == r_l)
                    if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                        lt_tile_req.append(z3_path_v(lt_tile) == r_u)
                    if 0 < c and r < maze.height - 1 and maze.is_path(c - 1, r + 1):
                        lt_tile_req.append(z3_path_v(lt_tile) == r_d)
                    lt_tile_or = z3.Or(lt_tile_req)
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == r_l, lt_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == l_u, lt_tile_or))
                    optimizer.add(z3.Implies(z3_path_v(this_tile) == l_d, lt_tile_or))

                # Origin disjunction
                og_tile_req = []
                if r > 0:
                    og_tile_req.append(z3_path_v(up_tile) == o_g)
                    og_tile_req.append(z3_path_v(up_tile) == r_d)
                    og_tile_req.append(z3_path_v(up_tile) == l_d)
                    og_tile_req.append(z3_path_v(up_tile) == u_d)
                if c < maze.width - 1:
                    og_tile_req.append(z3_path_v(rt_tile) == o_g)
                    og_tile_req.append(z3_path_v(rt_tile) == l_u)
                    og_tile_req.append(z3_path_v(rt_tile) == l_d)
                    og_tile_req.append(z3_path_v(rt_tile) == r_l)
                if r < maze.height - 1:
                    og_tile_req.append(z3_path_v(dn_tile) == o_g)
                    og_tile_req.append(z3_path_v(dn_tile) == l_u)
                    og_tile_req.append(z3_path_v(dn_tile) == r_u)
                    og_tile_req.append(z3_path_v(dn_tile) == u_d)
                if c > 0:
                    og_tile_req.append(z3_path_v(lt_tile) == o_g)
                    og_tile_req.append(z3_path_v(lt_tile) == r_u)
                    og_tile_req.append(z3_path_v(lt_tile) == r_d)
                    og_tile_req.append(z3_path_v(lt_tile) == r_l)
                origin_or = z3.Or(og_tile_req)
                optimizer.add(z3.Implies(z3_path_v(this_tile) == o_g, origin_or))


## Specific assertion fns


def anima_is_origin():
    for anima in animas:
        optimizer.add(z3_path_v(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_g)


def assert_path_hints():
    for r in range(0, maze.height):
        for c in range(0, maze.width):
            skip = False

            for anima in anima_locations.keys():
                if anima_locations[anima][0] == c and anima_locations[anima][1] == r:
                    skip = True

            if not skip:
                optimizer.add(
                    z3.Or(
                        [
                            z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == u_d,
                            z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == r_l,
                            z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == r_u,
                            z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == r_d,
                            z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == l_d,
                            z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == l_u,
                            z3_path_v(z3s_bv8_t.cast(c), z3s_bv8_t.cast(r)) == x_x,
                        ]
                    )
                )


assert_path_empty_constraints()
assert_anima_locations()
assert_tile_constraints()

anima_is_origin()
assert_path_hints()


def print_path(maze: maze_t, model: z3_model_t):
    for r in range(0, maze.height):
        bvr = z3s_bv8_t.cast(r)
        for c in range(0, maze.width):
            bvc = z3s_bv8_t.cast(c)
            if model.eval(z3_path_v(bvc, bvr) != x_x):
                print("x", end="")
            else:
                print(" ", end="")
        print("")


model = mind.timed_solve(optimizer, print_stats=True)
if type(model) == z3_model_t:
    print_path(maze, model)  # ty:ignore[invalid-argument-type]
