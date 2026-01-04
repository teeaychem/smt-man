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
# maze.print()

# print(z3.tactics())
# for tactic in z3.tactics():
#     print(f"{tactic}:\n\t{z3.tactic_description(tactic)}")
# print(z3.main_ctx().param_descrs())

# solver = Solver()

solver = z3.Optimize()

solver.set("incremental", True)
solver.set("maxsat_engine", "wmax")

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

## Base types

BitVec = z3.BitVecSort(8)

## Anima

Anima = z3.DeclareSort("Anima")
z3f_anima_location_r = z3.Function("anima_location_r", Anima, BitVec)
z3f_anima_location_c = z3.Function("anima_location_c", Anima, BitVec)

anima_anima = z3.Const("anima", Anima)
animas = (z3.Const("gottlob", Anima), z3.Const("smtman", Anima))
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

z3_path_v = z3.Function("path_type", BitVec, BitVec, PathEnum)

## General assertion fns


def assert_path_empty_constraints():
    for r in range(0, maze.height):
        for c in range(0, maze.width):
            if maze.is_path(c, r):
                solver.add_soft(z3_path_v(BitVec.cast(c), BitVec.cast(r)) == x_x, weight=1)
            else:
                solver.add(z3_path_v(BitVec.cast(c), BitVec.cast(r)) == x_x)


def assert_anima_locations():
    solver.add(z3f_anima_location_c(anima_gottlob) == BitVec.cast(anima_locations["gottlob"][0]))
    solver.add(z3f_anima_location_r(anima_gottlob) == BitVec.cast(anima_locations["gottlob"][0]))

    solver.add(z3f_anima_location_c(anima_smtman) == BitVec.cast(anima_locations["smtman"][0]))
    solver.add(z3f_anima_location_r(anima_smtman) == BitVec.cast(anima_locations["smtman"][1]))


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
                    up_tile_req = [z3_path_v(up_tile) == o_g]
                    if 0 < r - 1 and maze.is_path(c, r - 2):
                        up_tile_req.append(z3_path_v(up_tile) == u_d)
                    if c < maze.width - 1 and 0 < r and maze.is_path(c + 1, r - 1):
                        up_tile_req.append(z3_path_v(up_tile) == r_d)
                    if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                        up_tile_req.append(z3_path_v(up_tile) == l_d)
                    up_tile_or = z3.Or(up_tile_req)
                    solver.add(z3.Implies(z3_path_v(this_tile) == u_d, up_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == r_u, up_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == l_u, up_tile_or))

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
                    solver.add(z3.Implies(z3_path_v(this_tile) == r_l, rt_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == r_u, rt_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == r_d, rt_tile_or))

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
                    solver.add(z3.Implies(z3_path_v(this_tile) == u_d, dn_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == r_d, dn_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == l_d, dn_tile_or))

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
                    solver.add(z3.Implies(z3_path_v(this_tile) == r_l, lt_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == l_u, lt_tile_or))
                    solver.add(z3.Implies(z3_path_v(this_tile) == l_d, lt_tile_or))

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
                solver.add(z3.Implies(z3_path_v(this_tile) == o_g, origin_or))


## Specific assertion fns


def anima_is_origin():
    for anima in animas:
        solver.add(z3_path_v(z3f_anima_location_c(anima), z3f_anima_location_r(anima)) == o_g)


def assert_path_hints():
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
                            z3_path_v(BitVec.cast(c), BitVec.cast(r)) == u_d,
                            z3_path_v(BitVec.cast(c), BitVec.cast(r)) == r_l,
                            z3_path_v(BitVec.cast(c), BitVec.cast(r)) == r_u,
                            z3_path_v(BitVec.cast(c), BitVec.cast(r)) == r_d,
                            z3_path_v(BitVec.cast(c), BitVec.cast(r)) == l_d,
                            z3_path_v(BitVec.cast(c), BitVec.cast(r)) == l_u,
                            z3_path_v(BitVec.cast(c), BitVec.cast(r)) == x_x,
                        ]
                    )
                )


assert_path_empty_constraints()
assert_anima_locations()
assert_tile_constraints()

anima_is_origin()
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
            if model.eval(z3_path_v(bvc, bvr) != x_x):
                print("x", end="")
            else:
                print(" ", end="")
        print("")

    print(model)


# print(solver.help())
