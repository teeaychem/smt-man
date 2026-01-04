import z3

import time


anima_locations = {
    "gottlob": [1, 4],
    "smtman": [11, 26],
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
    ("o", "a", "b", "x"),
    #      0    1    2    3
)

oo = path_enums[0]
aa = path_enums[1]
bb = path_enums[2]
xx = path_enums[3]


z3_path_v = z3.Function("path_type_v", BitVec, BitVec, PathEnum)
z3_path_h = z3.Function("path_type_h", BitVec, BitVec, PathEnum)

## General assertion fns


def assert_path_empty_constraints():
    for r in range(0, maze.height):
        for c in range(0, maze.width):
            this_tile = [BitVec.cast(c), BitVec.cast(r)]
            if maze.is_path(c, r):
                solver.add_soft(z3_path_h(this_tile) == xx, weight=1)
                solver.add_soft(z3_path_v(this_tile) == xx, weight=1)
            else:
                solver.add(z3_path_h(this_tile) == xx)
                solver.add(z3_path_v(this_tile) == xx)


def assert_anima_locations():
    solver.add(z3f_anima_location_c(anima_gottlob) == BitVec.cast(anima_locations["gottlob"][0]))
    solver.add(z3f_anima_location_r(anima_gottlob) == BitVec.cast(anima_locations["gottlob"][1]))

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
                    up_tile_req = [z3_path_h(up_tile) == oo]
                    if c < maze.width - 1 and 0 < r and maze.is_path(c + 1, r - 1):
                        up_tile_req.append(z3_path_h(up_tile) == aa)
                    if 0 < c and 0 < r and maze.is_path(c - 1, r - 1):
                        up_tile_req.append(z3_path_h(up_tile) == bb)
                    up_tile_or = z3.Or(up_tile_req)
                    consequent = [z3.And([z3_path_v(up_tile) == bb, up_tile_or])]
                    if 0 < r - 1 and maze.is_path(c, r - 2):
                        consequent.append(z3.And([z3_path_h(up_tile) == xx, z3.Or([z3_path_v(up_tile) == oo, z3_path_v(up_tile) == aa])]))
                    consequent = z3.Or(consequent)
                    solver.add(z3.Implies(z3_path_v(this_tile) == aa, consequent))
                    solver.add(z3.Implies(z3.And([z3_path_v(this_tile) == bb, z3_path_h(this_tile) == xx]), consequent))

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
                        consequent.append(z3.And([z3_path_h(dn_tile) == xx, z3.Or([z3_path_v(dn_tile) == oo, z3_path_v(dn_tile) == aa])]))
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
                        consequent.append(z3.And([z3_path_v(rt_tile) == xx, z3.Or([z3_path_h(rt_tile) == oo, z3_path_h(rt_tile) == aa])]))
                    consequent = z3.Or(consequent)
                    solver.add(z3.Implies(z3_path_h(this_tile) == aa, consequent))
                    solver.add(z3.Implies(z3.And([z3_path_h(this_tile) == bb, z3_path_v(this_tile) == xx]), consequent))

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
                        consequent.append(z3.And([z3_path_v(lt_tile) == xx, z3.Or([z3_path_h(lt_tile) == oo, z3_path_h(lt_tile) == aa])]))
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


def anima_is_origin():
    for anima in animas:
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

            for anima in anima_locations.keys():
                if anima_locations[anima][0] == c and anima_locations[anima][1] == r:
                    skip = True

            if not skip:
                solver.add(z3.Or([z3_path_h(this_tile) == aa, z3_path_h(this_tile) == bb, z3_path_h(this_tile) == xx]))
                solver.add(z3.Or([z3_path_v(this_tile) == aa, z3_path_v(this_tile) == bb, z3_path_v(this_tile) == xx]))


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
            if model.eval(z3_path_h(bvc, bvr) != xx) or model.eval(z3_path_v(bvc, bvr) != xx):
                print("x", end="")
            else:
                print(" ", end="")
        print("")

    print(model)


# print(solver.help())
