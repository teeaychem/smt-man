import z3

import time


anima_locations = {
    "gottlob": [1, 1],
    "smtman": [10, 26],
}


class Maze:
    def __init__(self, path):
        self.width = 0
        self.height = 0
        # Character representation of the maze
        self.chars = []
        self.from_path(path)

    def from_path(self, path):
        with open(path, "r") as file:
            for line in file.readlines():
                if 0 < len(line):
                    match line[0]:
                        case "m":
                            self.chars.append(list(line[1:-1]))
                        case "w":
                            self.width = int(line[1:])
                        case "h":
                            self.height = int(line[1:])

    def print(self):
        for row in range(0, self.height):
            for col in range(0, self.width):
                print(f"{self.chars[row][col]}", end="")
            print("")

    def is_path(self, col, row):
        return (self.chars[row][col] == " ") or (self.chars[row][col] == "-") or (self.chars[row][col] == "+")


maze = Maze("./resources/maze/source.txt")
maze.print()

# print(z3.tactics())
# for tactic in z3.tactics():
#     print(f"{tactic}:\n\t{z3.tactic_description(tactic)}")
# print(z3.main_ctx().param_descrs())


# solver = Solver()

solver = z3.Optimize()

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

bit_vec_sort = z3.BitVecSort(8)

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

z3_path_v = z3.Function("path_type", bit_vec_sort, bit_vec_sort, PathEnum)

AnimaSort = z3.DeclareSort("Anima")
z3f_anima_location_r = z3.Function("anima_location_r", AnimaSort, bit_vec_sort)
z3f_anima_location_c = z3.Function("anima_location_c", AnimaSort, bit_vec_sort)


for r in range(0, maze.height):
    for c in range(0, maze.width):
        if maze.is_path(c, r):
            solver.add_soft(z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == x_x, weight=1)
        else:
            solver.add(z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == x_x)

# Animas

anima_anima = z3.Const("anima", AnimaSort)
animas = (z3.Const("gottlob", AnimaSort), z3.Const("smtman", AnimaSort))
anima_gottlob = animas[0]
anima_smtman = animas[1]


solver.add(z3f_anima_location_c(anima_gottlob) == bit_vec_sort.cast(anima_locations["gottlob"][0]))
solver.add(z3f_anima_location_r(anima_gottlob) == bit_vec_sort.cast(anima_locations["gottlob"][0]))

solver.add(z3f_anima_location_c(anima_smtman) == bit_vec_sort.cast(anima_locations["smtman"][0]))
solver.add(z3f_anima_location_r(anima_smtman) == bit_vec_sort.cast(anima_locations["smtman"][1]))


for r in range(0, maze.height):
    bvr = bit_vec_sort.cast(r)
    for c in range(0, maze.width):
        bvc = bit_vec_sort.cast(c)

        if maze.is_path(c, r):
            this_tile = [bit_vec_sort.cast(c), bit_vec_sort.cast(r)]
            up_tile = [bit_vec_sort.cast(c), bit_vec_sort.cast(r - 1)]
            rt_tile = [bit_vec_sort.cast(c + 1), bit_vec_sort.cast(r)]
            dn_tile = [bit_vec_sort.cast(c), bit_vec_sort.cast(r + 1)]
            lt_tile = [bit_vec_sort.cast(c - 1), bit_vec_sort.cast(r)]

            # Up disjunction
            if r > 0:
                up_tile_req = [z3_path_v(up_tile) == o_d]
                if 0 < r - 1 and maze.is_path(c, r - 2):
                    up_tile_req.append(z3_path_v(up_tile) == u_d)
                if c < maze.width - 1 and 0 < r and maze.is_path(c + 1, r - 1):
                    up_tile_req.append(z3_path_v(up_tile) == r_d)
                if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                    up_tile_req.append(z3_path_v(up_tile) == l_d)
                up_tile_or = z3.Or(up_tile_req)
                solver.add(z3.Implies(z3_path_v(this_tile) == o_u, up_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == u_d, up_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == r_u, up_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == l_u, up_tile_or))

            # Right disjunction
            if c < maze.width - 1:
                rt_tile_req = [z3_path_v(rt_tile) == o_l]
                if c + 1 < maze.width - 1 and maze.is_path(c + 2, r):
                    rt_tile_req.append(z3_path_v(rt_tile) == r_l)
                if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                    rt_tile_req.append(z3_path_v(rt_tile) == l_d)
                if 0 < r and c < maze.width - 1 and maze.is_path(c + 1, r - 1):
                    rt_tile_req.append(z3_path_v(rt_tile) == l_u)
                rt_tile_or = z3.Or(rt_tile_req)
                solver.add(z3.Implies(z3_path_v(this_tile) == o_r, rt_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == r_l, rt_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == r_u, rt_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == r_d, rt_tile_or))

            # Down disjunction
            if r < maze.height - 1:
                dn_tile_req = [z3_path_v(dn_tile) == o_u]
                if r + 1 < maze.height - 1 and maze.is_path(c, r + 2):
                    dn_tile_req.append(z3_path_v(dn_tile) == u_d)
                if r < maze.height - 1 and c < maze.width - 1 and maze.is_path(c + 1, r + 1):
                    dn_tile_req.append(z3_path_v(dn_tile) == r_u)
                if r < maze.height - 1 and 0 < c and maze.is_path(c - 1, r + 1):
                    dn_tile_req.append(z3_path_v(dn_tile) == l_u)
                dn_tile_or = z3.Or(dn_tile_req)
                solver.add(z3.Implies(z3_path_v(this_tile) == o_d, dn_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == u_d, dn_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == r_d, dn_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == l_d, dn_tile_or))

            # Left disjunction
            if c > 0:
                lt_tile_req = [z3_path_v(lt_tile) == o_r]
                if 0 < c - 1 and maze.is_path(c - 2, r):
                    lt_tile_req.append(z3_path_v(lt_tile) == r_l)
                if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                    lt_tile_req.append(z3_path_v(lt_tile) == r_u)
                if 0 < c and r < maze.height - 1 and maze.is_path(c - 1, r + 1):
                    lt_tile_req.append(z3_path_v(lt_tile) == r_d)
                lt_tile_or = z3.Or(lt_tile_req)
                solver.add(z3.Implies(z3_path_v(this_tile) == o_l, lt_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == r_l, lt_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == l_u, lt_tile_or))
                solver.add(z3.Implies(z3_path_v(this_tile) == l_d, lt_tile_or))

            # Origin disjunction
            og_tile_req = []
            if r > 0:
                og_tile_req.append(z3_path_v(up_tile) == o_d)
                og_tile_req.append(z3_path_v(up_tile) == r_d)
                og_tile_req.append(z3_path_v(up_tile) == l_d)
                og_tile_req.append(z3_path_v(lt_tile) == u_d)
            if c < maze.width - 1:
                og_tile_req.append(z3_path_v(rt_tile) == o_l)
                og_tile_req.append(z3_path_v(rt_tile) == l_u)
                og_tile_req.append(z3_path_v(rt_tile) == l_d)
                og_tile_req.append(z3_path_v(lt_tile) == r_l)
            if r < maze.height - 1:
                og_tile_req.append(z3_path_v(dn_tile) == o_u)
                og_tile_req.append(z3_path_v(dn_tile) == l_u)
                og_tile_req.append(z3_path_v(dn_tile) == r_u)
                og_tile_req.append(z3_path_v(lt_tile) == u_d)
            if c > 0:
                og_tile_req.append(z3_path_v(lt_tile) == o_r)
                og_tile_req.append(z3_path_v(lt_tile) == r_u)
                og_tile_req.append(z3_path_v(lt_tile) == r_d)
                og_tile_req.append(z3_path_v(lt_tile) == r_l)
            origin_or = z3.Or(og_tile_req)
            solver.add(z3.Implies(z3_path_v(this_tile) == o_l, origin_or))


def path_hints():
    for r in range(0, maze.height):
        for c in range(0, maze.width):
            skip = False

            for anima in anima_locations.keys():
                if anima_locations[anima][0] == c and anima_locations[anima][1] == r:
                    skip = True

            if not skip:
                solver.add(
                    z3.Or(
                        [
                            z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == u_d,
                            z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_l,
                            z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_u,
                            z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == r_d,
                            z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == l_d,
                            z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == l_u,
                            z3_path_v(bit_vec_sort.cast(c), bit_vec_sort.cast(r)) == x_x,
                        ]
                    )
                )


def anima_is_origin():
    for anima in animas:
        solver.add(
            z3.Or(
                [
                    z3_path_v(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_u,
                    z3_path_v(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_r,
                    z3_path_v(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_d,
                    z3_path_v(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_l,
                ]
            )
        )


anima_is_origin()
path_hints()

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

# input("Awaiting on input to solve...")
time_solve_start = time.perf_counter()

result = solver.check()
time_solve_end = time.perf_counter()
print(f"Result: {result} in {time_solve_end - time_solve_start:0.4f} seconds")

if result == z3.sat:
    print(solver.statistics())

    model = solver.model()

    time_model_found = time.perf_counter()
    print(f"Time to model: {time_model_found - time_solve_start:0.4f} seconds")

    path_tiles = []

    # print(f"{model}")
    # print(model.eval(z3f_anima_facing(anima_gottlob)))
    # print(model.eval(z3f_anima_location(anima_gottlob)))
    # print(model.eval(z3_path_e(z3f_anima_location(anima_gottlob))))
    for r in range(0, maze.height):
        bvr = bit_vec_sort.cast(r)
        for c in range(0, maze.width):
            bvc = bit_vec_sort.cast(c)
            if model.eval(z3_path_v(bvc, bvr) != path_enums[10]):
                path_tiles.append((c, r, model.eval(z3_path_v(bvc, bvr))))
                print("x", end="")
                # print(f"{c},{r} = {model.eval(z3f_path_type(z3u8Pair.u8Pair(bvr, bvc)))}")
            else:
                print(" ", end="")
        print("")
    print(path_tiles)

    print(model)

    # for r in range(0, height):
    #     for c in range(0, maze.width):
    #         print(f"({r}, {c}) = {model.eval(z3f_path_type(r, c))}")


# print(solver.help())
