import time

from z3 import *

anima_locations = {
    "gottlob": [1, 1],
    "smtman": [10, 26],
}


maze_chars = []
width = 0
height = 0


# print(z3.tactics())
# for tactic in z3.tactics():
#     print(f"{tactic}:\n\t{z3.tactic_description(tactic)}")
# print(z3.main_ctx().param_descrs())


# Character representation of the maze
with open("./resources/maze/source.txt", "r") as file:
    for line in file.readlines():
        if 0 < len(line):
            match line[0]:
                case "m":
                    maze_chars.append(list(line[1:-1]))
                case "w":
                    width = int(line[1:])
                case "h":
                    height = int(line[1:])


width_less_one = width - 1
height_less_one = height - 1

# solver = Solver()

solver = Optimize()

solver.set("incremental", True)

# solver.set("maxres.wmax", True)

# solver.set("priority", "box")

# solver.set("enable_lns", True)
# solver.set("enable_sat", False)
# solver.set("enable_sls", True)
# solver.set("optsmt_engine", "symba")
# solver.set("pb.compile_equality", True)

# solver.set("maxsat_engine", "wmax")
# solver.set("ctrl_c", False)
# solver.set("pb.compile_equality", True)
# solver.set("maxres.maximize_assignment", True)

# solver.set("maxsat_engine", "maxres")
# solver.set("maxsat_engine", "pd-maxres")
# solver.set("maxsat_engine", "rc2")
# solver.set("maxsat_engine", "maxres-bin")

# solver.set("priority", "pareto")

bit_vec_sort = BitVecSort(8)


bv8_0 = bit_vec_sort.cast(0)
bv8_1 = bit_vec_sort.cast(1)

PathEnum, path_enums = z3.EnumSort(
    "path_e",
    ["ou", "or", "od", "ol", "ud", "rl", "ur", "rd", "dl", "lu", "xx"],
    # 0     1     2     3     4     5     6     7     8     9     10
)

o_u = path_enums[0]
o_r = path_enums[1]
o_d = path_enums[2]
o_l = path_enums[3]

u_d = path_enums[4]
r_l = path_enums[5]

r_u = path_enums[6]
r_d = path_enums[7]
l_d = path_enums[8]
l_u = path_enums[9]
x_x = path_enums[10]

z3_path_e = Function("path_type", bit_vec_sort, bit_vec_sort, PathEnum)

AnimaSort = z3.DeclareSort("Anima")
z3f_anima_location_r = Function("anima_location_r", AnimaSort, bit_vec_sort)
z3f_anima_location_c = Function("anima_location_c", AnimaSort, bit_vec_sort)


for r in range(0, height):
    for c in range(0, width):
        if maze_chars[r][c] != " ":
            solver.add_soft(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == x_x, weight=1)
            continue
        else:
            solver.add(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == x_x)

# Animas

anima_anima = z3.Const("anima", AnimaSort)
animas = (z3.Const("gottlob", AnimaSort), z3.Const("smtman", AnimaSort))
anima_gottlob = animas[0]
anima_smtman = animas[1]


solver.add(z3f_anima_location_c(anima_gottlob) == bit_vec_sort.cast(anima_locations["gottlob"][0]))
solver.add(z3f_anima_location_r(anima_gottlob) == bit_vec_sort.cast(anima_locations["gottlob"][0]))

solver.add(z3f_anima_location_c(anima_smtman) == bit_vec_sort.cast(anima_locations["smtman"][0]))
solver.add(z3f_anima_location_r(anima_smtman) == bit_vec_sort.cast(anima_locations["smtman"][1]))


for r in range(0, height):
    bvr = bit_vec_sort.cast(r)
    for c in range(0, width):
        bvc = bit_vec_sort.cast(c)

        if maze_chars[r][c] != " ":
            up_tile = [bit_vec_sort.cast(c), bit_vec_sort.cast(r - 1)] if r > 0 else None
            rt_tile = [bit_vec_sort.cast(c + 1), bit_vec_sort.cast(r)] if c < width_less_one else None
            dn_tile = [bit_vec_sort.cast(c), bit_vec_sort.cast(r + 1)] if r < height_less_one else None
            lt_tile = [bit_vec_sort.cast(c - 1), bit_vec_sort.cast(r)] if c > 0 else None

            up_tile_req = (
                None
                if up_tile == None
                else [
                    z3_path_e(up_tile) == o_d,
                    z3_path_e(up_tile) == u_d if 0 < r - 1 and maze_chars[r - 2][c] == "#" else None,
                    z3_path_e(up_tile) == r_d if c < width_less_one and 0 < r and maze_chars[r - 1][c + 1] == "#" else None,
                    z3_path_e(up_tile) == l_d if 0 < c and 0 < r and maze_chars[r - 1][c - 1] == "#" else None,
                ]
            )
            if up_tile_req != None:
                up_tile_req = [req for req in up_tile_req if req != None]

            rt_tile_req = (
                None
                if rt_tile == None
                else [
                    z3_path_e(rt_tile) == o_l,
                    z3_path_e(rt_tile) == r_l if c + 1 < width_less_one and maze_chars[r][c + 2] == "#" else None,
                    z3_path_e(rt_tile) == l_d if r < height_less_one and c < width_less_one and maze_chars[r + 1][c + 1] == "#" else None,
                    z3_path_e(rt_tile) == l_u if 0 < r and c < width_less_one and maze_chars[r - 1][c + 1] == "#" else None,
                ]
            )
            if rt_tile_req != None:
                rt_tile_req = [req for req in rt_tile_req if req != None]

            dn_tile_req = (
                None
                if dn_tile == None
                else [
                    z3_path_e(dn_tile) == o_u,
                    z3_path_e(dn_tile) == u_d if r + 1 < height_less_one and maze_chars[r + 2][c] == "#" else None,
                    z3_path_e(dn_tile) == r_u if r < height_less_one and c < width_less_one and maze_chars[r + 1][c + 1] == "#" else None,
                    z3_path_e(dn_tile) == l_u if r < height_less_one and 0 < c and maze_chars[r + 1][c - 1] == "#" else None,
                ]
            )
            if dn_tile_req != None:
                dn_tile_req = [req for req in dn_tile_req if req != None]

            lt_tile_req = (
                None
                if lt_tile == None
                else [
                    z3_path_e(lt_tile) == o_r,
                    z3_path_e(lt_tile) == r_l if 0 < c - 1 and maze_chars[r][c - 2] == "#" else None,
                    z3_path_e(lt_tile) == r_u if 0 < c and 0 < r and maze_chars[r - 1][c - 1] == "#" else None,
                    z3_path_e(lt_tile) == r_d if 0 < c and r < height_less_one and maze_chars[r + 1][c - 1] == "#" else None,
                ]
            )
            if lt_tile_req != None:
                lt_tile_req = [req for req in lt_tile_req if req != None]

            up_tile_or = z3.Or(up_tile_req) if up_tile_req != None else None
            rt_tile_or = z3.Or(rt_tile_req) if rt_tile_req != None else None
            dn_tile_or = z3.Or(dn_tile_req) if dn_tile_req != None else None
            lt_tile_or = z3.Or(lt_tile_req) if lt_tile_req != None else None

            if up_tile_req != None:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_u, up_tile_or))

            if rt_tile_req != None:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_r, rt_tile_or))

            if dn_tile_req != None:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_d, dn_tile_or))

            if lt_tile_req != None:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_l, lt_tile_or))

            u_d_constraint = [c for c in [up_tile_or, dn_tile_or] if c != None]
            if len(u_d_constraint) > 0:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == u_d, z3.And(u_d_constraint)))

            r_l_constraint = [c for c in [lt_tile_or, rt_tile_or] if c != None]
            if len(r_l_constraint) > 0:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_l, z3.And(r_l_constraint)))

            r_u_constraint = [c for c in [up_tile_or, rt_tile_or] if c != None]
            if len(r_u_constraint) > 0:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_u, z3.And(r_u_constraint)))

            r_d_constraint = [c for c in [dn_tile_or, rt_tile_or] if c != None]
            if len(r_d_constraint) > 0:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_d, z3.And(r_d_constraint)))

            l_d_constraint = [c for c in [dn_tile_or, lt_tile_or] if c != None]
            if len(l_d_constraint) > 0:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == l_d, z3.And(l_d_constraint)))

            l_u_constraint = [c for c in [up_tile_or, lt_tile_or] if c != None]
            if len(l_u_constraint) > 0:
                solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == l_u, z3.And(l_u_constraint)))


for r in range(0, height):
    for c in range(0, width):
        skip = False

        for anima in anima_locations.keys():
            if anima_locations[anima][0] == c and anima_locations[anima][1] == r:
                skip = True

        if not skip:
            # solver.add(
            #     z3.And(
            #         [
            #             z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) != o_u,
            #             z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) != o_r,
            #             z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) != o_d,
            #             z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) != o_l,
            #         ]
            #     )
            # )

            solver.add(
                z3.Or(
                    [
                        z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == u_d,
                        z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_l,
                        z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_u,
                        z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_d,
                        z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == l_d,
                        z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == l_u,
                        z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == x_x,
                    ]
                )
            )


# for r in range(0, height):
#     bvr = bit_vec_sort.cast(r)
#     for c in range(0, width):
#         bvc = bit_vec_sort.cast(c)

#         some_anima_location = z3.Or(
#             z3.And(z3f_anima_location_c(anima_gottlob) == bvc, z3f_anima_location_r(anima_gottlob) == bvr),
#             z3.And(z3f_anima_location_c(anima_smtman) == bvc, z3f_anima_location_r(anima_smtman) == bvr),
#         )

#         solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_u, some_anima_location))
#         solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_r, some_anima_location))
#         solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_d, some_anima_location))
#         solver.add(z3.Implies(z3_path_e(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == o_l, some_anima_location))


for anima in animas:
    solver.add(
        z3.Or(
            [
                z3_path_e(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_u,
                z3_path_e(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_r,
                z3_path_e(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_d,
                z3_path_e(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_l,
            ]
        )
    )


# x = z3u8Pair.u8Pair(128, 0)
# print(x)
# print(f"{x} = ({simplify(z3u8Pair.row(x))}, {simplify(z3u8Pair.col(x))})")

time_solve_start = 0
time_model_found = 0
time_solve_end = 0


def on_model(m):
    print(solver.statistics())
    time_model_found = time.perf_counter()
    print(f"Time to model: {time_model_found - time_solve_start:0.4f} seconds")


# solver.set_on_model(on_model)

# for _ in range(0,5):
#     solver.push()
#     solver.check()
#     solver.pop()

# input("Awaiting on input to solve...")
time_solve_start = time.perf_counter()

result = solver.check()
time_solve_end = time.perf_counter()
print(f"Result: {result} in {time_solve_end - time_solve_start:0.4f} seconds")


if result == sat:
    print(solver.statistics())

    model = solver.model()

    time_model_found = time.perf_counter()
    print(f"Time to model: {time_model_found - time_solve_start:0.4f} seconds")

    path_tiles = []

    # print(f"{model}")
    # print(model.eval(z3f_anima_facing(anima_gottlob)))
    # print(model.eval(z3f_anima_location(anima_gottlob)))
    # print(model.eval(z3_path_e(z3f_anima_location(anima_gottlob))))
    for r in range(0, height):
        bvr = bit_vec_sort.cast(r)
        for c in range(0, width):
            bvc = bit_vec_sort.cast(c)
            if model.eval(z3_path_e(bvc, bvr) != path_enums[10]):
                path_tiles.append((c, r, model.eval(z3_path_e(bvc, bvr))))
                print("x", end="")
                # print(f"{c},{r} = {model.eval(z3f_path_type(z3u8Pair.u8Pair(bvr, bvc)))}")
            else:
                print(" ", end="")
        print("")
    print(path_tiles)
    # print(model.eval(z3u8Pair.row(z3f_anima_location(anima_gottlob))))
    # for r in range(0, height):
    #     for c in range(0, width):
    #         print(f"({r}, {c}) = {model.eval(z3f_path_type(r, c))}")


# print(solver.help())
