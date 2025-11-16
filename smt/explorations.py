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


solver = Solver()


bv8_0 = BitVecSort(8).cast(0)
bv8_1 = BitVecSort(8).cast(1)

bv8_u = z3.Const("u", BitVecSort(8))
bv8_v = z3.Const("v", BitVecSort(8))
bv8_w = z3.Const("w", BitVecSort(8))
bv8_x = z3.Const("x", BitVecSort(8))
bv8_y = z3.Const("y", BitVecSort(8))
bv8_z = z3.Const("z", BitVecSort(8))

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
        maze_pairs[r][c] = z3u8Pair.u8Pair(r, c)

solver.assert_exprs(z3.Distinct(sum(maze_pairs, [])))

z3_f_is_open = Function("is_open", z3u8Pair, BoolSort())

for r in range(0, height):
    for c in range(0, width):
        match maze_chars[r][c]:
            case " ":
                solver.add(z3.mk_not(z3_f_is_open(maze_pairs[r][c])))
            case _:
                solver.add(z3_f_is_open(maze_pairs[r][c]))


# Directions
DirectionSort = z3.DeclareSort("Direction")
direction_up = z3.Const("direction_up", DirectionSort)
direction_right = z3.Const("direction_right", DirectionSort)
direction_down = z3.Const("direction_down", DirectionSort)
direction_left = z3.Const("direction_left", DirectionSort)

# Animas
AnimaSort = z3.DeclareSort("Anima")
anima_anima = z3.Const("anima", AnimaSort)
anima_gottlob = z3.Const("gottlob", AnimaSort)
anima_smtman = z3.Const("smtman", AnimaSort)

z3f_anima_facing = Function("anima_facing", AnimaSort, DirectionSort)
solver.add(z3f_anima_facing(anima_gottlob) == direction_down)

z3f_anima_location = Function("anima_location", AnimaSort, z3u8Pair)
solver.add(
    z3.ForAll([anima_anima], ULT(z3u8Pair.row(z3f_anima_location(anima_anima)), height))
)
solver.add(
    z3.ForAll([anima_anima], ULT(z3u8Pair.col(z3f_anima_location(anima_anima)), width))
)

# for r in range(0, height):
#     for c in range(0, width):
#         solver.add(z3f_anima_location(anima_gottlob) != maze_pairs[r][c])

solver.assert_exprs(
    z3.Distinct(direction_up, direction_right, direction_down, direction_left)
)

solver.add(z3f_anima_location(anima_gottlob) == maze_pairs[1][2])
solver.add(z3f_anima_location(anima_smtman) == maze_pairs[10][1])

z3f_path = Function("path", BitVecSort(8), BitVecSort(8), BoolSort())


solver.add(
    z3.ForAll(
        [anima_anima],
        z3f_path(
            z3u8Pair.row(z3f_anima_location(anima_smtman)),
            z3u8Pair.col(z3f_anima_location(anima_smtman)),
        ),
    )
)


solver.add(
    z3.ForAll(
        [bv8_x, bv8_y],
        z3.Implies(
            z3f_path(bv8_x, bv8_y),
            z3.Or(
                z3f_path(bv8_x + bv8_1, bv8_y),
                z3f_path(bv8_x - bv8_1, bv8_y),
                z3f_path(bv8_x, bv8_y + bv8_1),
                z3f_path(bv8_x, bv8_y - bv8_1),
            ),
        ),
    )
)

solver.add(z3.Not(z3f_path(bv8_1, bv8_1)))


# x = z3u8Pair.u8Pair(128, 0)
# print(x)
# print(f"{x} = ({simplify(z3u8Pair.row(x))}, {simplify(z3u8Pair.col(x))})")

# input("Awaiting on input to solve...")
result = solver.check()
print(f"Result: {result}")
if result == sat:
    model = solver.model()
    # print(f"{model}")
    print(model.eval(z3f_anima_facing(anima_gottlob)))
    # print(model.eval(z3f_anima_location(anima_gottlob)))
    # print(model.eval(z3u8Pair.row(z3f_anima_location(anima_gottlob))))
    for r in range(0, height):
        for c in range(0, width):
            if model.eval(
                z3f_path(
                    z3u8Pair.row(maze_pairs[r][c]),
                    z3u8Pair.col(maze_pairs[r][c]),
                )
            ):
                print(f"({r}, {c})")
