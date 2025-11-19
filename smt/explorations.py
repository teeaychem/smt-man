from z3 import *  # pyright: ignore[reportMissingTypeStubs, reportWildcardImportFromLibrary]

maze_chars = []
width = 0
height = 0


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


def surrounding(x, y):
    pairs = []
    if 0 < x:
        pairs.append((x - 1, y))
    if x < width_less_one:
        pairs.append((x + 1, y))
    if 0 < y:
        pairs.append((x, y - 1))
    if y < height_less_one:
        pairs.append((x, y + 1))
    return pairs


solver = Optimize()


bv8_0 = BitVecSort(8).cast(0)
bv8_1 = BitVecSort(8).cast(1)

bv8_u = z3.Const("u", BitVecSort(8))
bv8_v = z3.Const("v", BitVecSort(8))
bv8_w = z3.Const("w", BitVecSort(8))
bv8_x = z3.Const("x", BitVecSort(8))
bv8_y = z3.Const("y", BitVecSort(8))
bv8_z = z3.Const("z", BitVecSort(8))

z3f_path_end = Function("path", BitVecSort(8), BitVecSort(8), BoolSort())
z3f_path_segment = Function(
    "path", BitVecSort(8), BitVecSort(8), BitVecSort(8), BitVecSort(8), BoolSort()
)

# Pairs
maze_pairs = [[None for _ in range(0, width)] for _ in range(0, height)]

z3dt_u8_pair = z3.Datatype("u8_pair_t")
z3dt_u8_pair.declare("u8Pair", ("row", BitVecSort(8)), ("col", BitVecSort(8)))
z3u8Pair = z3dt_u8_pair.create()
v_u8p_xy = z3u8Pair.u8Pair(bv8_x, bv8_y)
v_u8p_uv = z3u8Pair.u8Pair(bv8_u, bv8_v)
v_u8p_cxy = z3.Const("xy", z3u8Pair)
v_u8p_cuv = z3.Const("uv", z3u8Pair)


for r in range(0, height):
    for c in range(0, width):
        maze_pairs[r][c] = z3u8Pair.u8Pair(c, r)
        # solver.add_soft(z3.Not(z3f_path_segment(r, c)), weight=2)
        # solver.add_soft(z3.Not(z3f_path_end(r, c)), weight=99)

solver.assert_exprs(z3.Distinct(sum(maze_pairs, [])))

# Animas
AnimaSort = z3.DeclareSort("Anima")
anima_anima = z3.Const("anima", AnimaSort)
animas = (z3.Const("gottlob", AnimaSort), z3.Const("smtman", AnimaSort))
anima_gottlob = animas[0]
anima_smtman = animas[1]


# z3f_anima_facing = Function("anima_facing", AnimaSort, DirectionEnum)
# solver.add(z3f_anima_facing(anima_gottlob) == direction_down)

z3f_anima_location = Function("anima_location", AnimaSort, z3u8Pair)
for anima in animas:
    solver.add(ULT(z3u8Pair.row(z3f_anima_location(anima)), height))
    solver.add(ULT(z3u8Pair.col(z3f_anima_location(anima)), width))


# for r in range(0, height):
#     for c in range(0, width):
#         solver.add(z3f_anima_location(anima_gottlob) != maze_pairs[r][c])

# solver.assert_exprs(
#     z3.Distinct(direction_up, direction_right, direction_down, direction_left)
# )


solver.add(z3f_anima_location(anima_gottlob) == maze_pairs[1][2])
solver.add(z3f_anima_location(anima_smtman) == maze_pairs[26][3])

PathEnum, path_enums = z3.EnumSort(
    "path_e",
    ["ou", "or", "od", "ol", "ud", "rl", "ur", "rd", "dl", "lu", "xx"],
    # 0     1     2     3     4     5     6     7     8     9     10
)

o_u = path_enums[0]
r_o = path_enums[1]
o_d = path_enums[2]
l_o = path_enums[3]

u_d = path_enums[4]
r_l = path_enums[5]

r_u = path_enums[6]
r_d = path_enums[7]
l_d = path_enums[8]
l_u = path_enums[9]
x_x = path_enums[10]

z3f_path_type = Function("path_type", z3u8Pair, PathEnum)

for r in range(0, height):
    bvr = BitVecSort(8).cast(r)
    for c in range(0, width):
        bvc = BitVecSort(8).cast(c)

        if maze_chars[r][c] == " ":
            solver.add(z3f_path_type(z3u8Pair.u8Pair(bvc, bvr)) == x_x)
        else:
            location = z3u8Pair.u8Pair(bvc, bvr)

            if (r == 1 and c == 2) or (r == 26 and c == 3):
                solver.add(
                    z3.Or(
                        z3f_path_type(location) == o_u,
                        z3f_path_type(location) == r_o,
                        z3f_path_type(location) == o_d,
                        z3f_path_type(location) == l_o,
                    )
                )
            else:
                solver.add(
                    z3.Or(
                        z3f_path_type(location) == x_x,
                        z3f_path_type(location) == u_d,
                        z3f_path_type(location) == r_l,
                        z3f_path_type(location) == r_u,
                        z3f_path_type(location) == r_d,
                        z3f_path_type(location) == l_d,
                        z3f_path_type(location) == l_u,
                    )
                )

            up_tile = z3u8Pair.u8Pair(bvc, bvr - bv8_1)
            right_tile = z3u8Pair.u8Pair(bvc + bv8_1, bvr)
            down_tile = z3u8Pair.u8Pair(bvc, bvr + bv8_1)
            left_tile = z3u8Pair.u8Pair(bvc - bv8_1, bvr)

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == o_u,
                    z3.Or(
                        [
                            z3f_path_type(up_tile) == o_d,
                            z3f_path_type(up_tile) == u_d,
                            z3f_path_type(up_tile) == r_d,
                            z3f_path_type(up_tile) == l_d,
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == r_o,
                    z3.Or(
                        [
                            z3f_path_type(right_tile) == l_o,
                            z3f_path_type(right_tile) == r_l,
                            z3f_path_type(right_tile) == l_d,
                            z3f_path_type(right_tile) == l_u,
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == o_d,
                    z3.Or(
                        [
                            z3f_path_type(down_tile) == o_u,
                            z3f_path_type(down_tile) == u_d,
                            z3f_path_type(down_tile) == r_u,
                            z3f_path_type(down_tile) == l_u,
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == l_o,
                    z3.Or(
                        [
                            z3f_path_type(left_tile) == r_o,
                            z3f_path_type(left_tile) == r_l,
                            z3f_path_type(left_tile) == r_u,
                            z3f_path_type(left_tile) == r_d,
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == u_d,
                    z3.And(
                        [
                            z3.Or(
                                [
                                    z3f_path_type(up_tile) == o_d,
                                    z3f_path_type(up_tile) == u_d,
                                    z3f_path_type(up_tile) == r_d,
                                    z3f_path_type(up_tile) == l_d,
                                ]
                            ),
                            z3.Or(
                                [
                                    z3f_path_type(down_tile) == o_u,
                                    z3f_path_type(down_tile) == u_d,
                                    z3f_path_type(down_tile) == r_u,
                                    z3f_path_type(down_tile) == l_u,
                                ]
                            ),
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == r_l,
                    z3.And(
                        [
                            z3.Or(
                                [
                                    z3f_path_type(left_tile) == r_o,
                                    z3f_path_type(left_tile) == r_l,
                                    z3f_path_type(left_tile) == r_u,
                                    z3f_path_type(left_tile) == r_d,
                                ]
                            ),
                            z3.Or(
                                [
                                    z3f_path_type(right_tile) == l_o,
                                    z3f_path_type(right_tile) == r_l,
                                    z3f_path_type(right_tile) == l_d,
                                    z3f_path_type(right_tile) == l_u,
                                ]
                            ),
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == r_u,
                    z3.And(
                        [
                            z3.Or(
                                [
                                    z3f_path_type(up_tile) == o_d,
                                    z3f_path_type(up_tile) == u_d,
                                    z3f_path_type(up_tile) == r_d,
                                    z3f_path_type(up_tile) == l_d,
                                ]
                            ),
                            z3.Or(
                                [
                                    z3f_path_type(right_tile) == l_o,
                                    z3f_path_type(right_tile) == r_l,
                                    z3f_path_type(right_tile) == l_d,
                                    z3f_path_type(right_tile) == l_u,
                                ]
                            ),
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == r_d,
                    z3.And(
                        [
                            z3.Or(
                                [
                                    z3f_path_type(down_tile) == o_u,
                                    z3f_path_type(down_tile) == u_d,
                                    z3f_path_type(down_tile) == r_u,
                                    z3f_path_type(down_tile) == l_u,
                                ]
                            ),
                            z3.Or(
                                [
                                    z3f_path_type(right_tile) == l_o,
                                    z3f_path_type(right_tile) == r_l,
                                    z3f_path_type(right_tile) == l_d,
                                    z3f_path_type(right_tile) == l_u,
                                ]
                            ),
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == l_d,
                    z3.And(
                        [
                            z3.Or(
                                [
                                    z3f_path_type(down_tile) == o_u,
                                    z3f_path_type(down_tile) == u_d,
                                    z3f_path_type(down_tile) == r_u,
                                    z3f_path_type(down_tile) == l_u,
                                ]
                            ),
                            z3.Or(
                                [
                                    z3f_path_type(left_tile) == r_o,
                                    z3f_path_type(left_tile) == r_l,
                                    z3f_path_type(left_tile) == r_u,
                                    z3f_path_type(left_tile) == r_d,
                                ]
                            ),
                        ]
                    ),
                )
            )

            solver.add(
                z3.Implies(
                    z3f_path_type(location) == l_u,
                    z3.And(
                        [
                            z3.Or(
                                [
                                    z3f_path_type(up_tile) == o_d,
                                    z3f_path_type(up_tile) == u_d,
                                    z3f_path_type(up_tile) == r_d,
                                    z3f_path_type(up_tile) == l_d,
                                ]
                            ),
                            z3.Or(
                                [
                                    z3f_path_type(left_tile) == r_o,
                                    z3f_path_type(left_tile) == r_l,
                                    z3f_path_type(left_tile) == r_u,
                                    z3f_path_type(left_tile) == r_d,
                                ]
                            ),
                        ]
                    ),
                )
            )

for anima in animas:
    solver.add(
        z3.Or(
            [
                z3f_path_type(z3f_anima_location(anima)) == o_u,
                z3f_path_type(z3f_anima_location(anima)) == r_o,
                z3f_path_type(z3f_anima_location(anima)) == o_d,
                z3f_path_type(z3f_anima_location(anima)) == l_o,
            ]
        )
    )


# x = z3u8Pair.u8Pair(128, 0)
# print(x)
# print(f"{x} = ({simplify(z3u8Pair.row(x))}, {simplify(z3u8Pair.col(x))})")

input("Awaiting on input to solve...")
result = solver.check()
print(f"Result: {result}")
if result == sat:
    model = solver.model()

    path_tiles = []

    # print(f"{model}")
    # print(model.eval(z3f_anima_facing(anima_gottlob)))
    print(model.eval(z3f_anima_location(anima_gottlob)))
    print(model.eval(z3f_path_type(z3f_anima_location(anima_gottlob))))
    for r in range(0, height):
        bvr = BitVecSort(8).cast(r)
        for c in range(0, width):
            bvc = BitVecSort(8).cast(c)
            location = z3u8Pair.u8Pair(bvc, bvr)
            if model.eval(z3f_path_type(location) != path_enums[10]):
                path_tiles.append((c, r, model.eval(z3f_path_type(location))))
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
