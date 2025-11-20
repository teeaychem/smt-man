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

bit_vec_sort = BitVecSort(8)


bv8_0 = bit_vec_sort.cast(0)
bv8_1 = bit_vec_sort.cast(1)

bv8_u = z3.Const("u", bit_vec_sort)
bv8_v = z3.Const("v", bit_vec_sort)
bv8_w = z3.Const("w", bit_vec_sort)
bv8_x = z3.Const("x", bit_vec_sort)
bv8_y = z3.Const("y", bit_vec_sort)
bv8_z = z3.Const("z", bit_vec_sort)

z3dt_u8_pair = z3.Datatype("u8_pair_t")
z3dt_u8_pair.declare("u8Pair", ("row", bit_vec_sort), ("col", bit_vec_sort))
z3u8Pair = z3dt_u8_pair.create()
v_u8p_xy = z3u8Pair.u8Pair(bv8_x, bv8_y)
v_u8p_uv = z3u8Pair.u8Pair(bv8_u, bv8_v)
v_u8p_cxy = z3.Const("xy", z3u8Pair)
v_u8p_cuv = z3.Const("uv", z3u8Pair)

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

z3_path_e = Function("path_type", z3u8Pair, PathEnum)

AnimaSort = z3.DeclareSort("Anima")
z3f_anima_location = Function("anima_location", AnimaSort, z3u8Pair)


# Pairs
maze_pairs = [[None for _ in range(0, width)] for _ in range(0, height)]


for r in range(0, height):
    for c in range(0, width):
        loc = z3u8Pair.u8Pair(bit_vec_sort.cast(c), bit_vec_sort.cast(r))

        maze_pairs[r][c] = loc

        if maze_chars[r][c] != " ":
            solver.add_soft(z3_path_e(loc) == x_x, weight=1)
        else:
            solver.add(z3_path_e(loc) == x_x)

solver.assert_exprs(z3.Distinct(sum(maze_pairs, [])))

# Animas

anima_anima = z3.Const("anima", AnimaSort)
animas = (z3.Const("gottlob", AnimaSort), z3.Const("smtman", AnimaSort))
anima_gottlob = animas[0]
anima_smtman = animas[1]


solver.add(z3f_anima_location(anima_gottlob) == maze_pairs[1][2])
solver.add(z3f_anima_location(anima_smtman) == maze_pairs[26][15])


for r in range(0, height):
    bvr = bit_vec_sort.cast(r)
    for c in range(0, width):
        bvc = bit_vec_sort.cast(c)
        loc = z3u8Pair.u8Pair(bvc, bvr)

        if maze_chars[r][c] != " ":
            if (r == 1 and c == 2) or (r == 26 and c == 15):
                solver.add(
                    z3.Or(
                        z3_path_e(loc) == o_u,
                        z3_path_e(loc) == r_o,
                        z3_path_e(loc) == o_d,
                        z3_path_e(loc) == l_o,
                    )
                )
            else:
                solver.add(
                    z3.Or(
                        z3_path_e(loc) == x_x,
                        z3_path_e(loc) == u_d,
                        z3_path_e(loc) == r_l,
                        z3_path_e(loc) == r_u,
                        z3_path_e(loc) == r_d,
                        z3_path_e(loc) == l_d,
                        z3_path_e(loc) == l_u,
                    )
                )

            up_tile = maze_pairs[r - 1][c] if r > 0 else None
            rt_tile = maze_pairs[r][c + 1] if c < width_less_one else None
            dn_tile = maze_pairs[r + 1][c] if r < height_less_one else None
            lt_tile = maze_pairs[r][c - 1] if c > 0 else None

            up_tile_req = (
                [
                    z3_path_e(up_tile) == o_d,
                    z3_path_e(up_tile) == u_d,
                    z3_path_e(up_tile) == r_d,
                    z3_path_e(up_tile) == l_d,
                ]
                if up_tile != None
                else None
            )

            rt_tile_req = (
                [
                    z3_path_e(rt_tile) == l_o,
                    z3_path_e(rt_tile) == r_l,
                    z3_path_e(rt_tile) == l_d,
                    z3_path_e(rt_tile) == l_u,
                ]
                if rt_tile != None
                else None
            )

            dn_tile_req = (
                [
                    z3_path_e(dn_tile) == o_u,
                    z3_path_e(dn_tile) == u_d,
                    z3_path_e(dn_tile) == r_u,
                    z3_path_e(dn_tile) == l_u,
                ]
                if dn_tile != None
                else None
            )

            lt_tile_req = (
                [
                    z3_path_e(lt_tile) == r_o,
                    z3_path_e(lt_tile) == r_l,
                    z3_path_e(lt_tile) == r_u,
                    z3_path_e(lt_tile) == r_d,
                ]
                if lt_tile != None
                else None
            )

            if up_tile != None and up_tile_req != None:
                up_impl = z3.Implies(z3_path_e(loc) == o_u, z3.Or(up_tile_req))
                solver.add(up_impl)

            if rt_tile != None:
                rt_impl = z3.Implies(z3_path_e(loc) == r_o, z3.Or(rt_tile_req))
                solver.add(rt_impl)

            if dn_tile != None:
                dn_impl = z3.Implies(z3_path_e(loc) == o_d, z3.Or(dn_tile_req))
                solver.add(dn_impl)

            if lt_tile != None:
                lt_impl = z3.Implies(z3_path_e(loc) == l_o, z3.Or(lt_tile_req))
                solver.add(lt_impl)

            up_tile_or = z3.Or(up_tile_req) if up_tile_req != None else None
            rt_tile_or = z3.Or(rt_tile_req) if rt_tile_req != None else None
            dn_tile_or = z3.Or(dn_tile_req) if dn_tile_req != None else None
            lt_tile_or = z3.Or(lt_tile_req) if lt_tile_req != None else None

            u_d_constraint = [c for c in [up_tile_or, dn_tile_or] if c != None]
            if len(u_d_constraint) > 0:
                u_d_impl = z3.Implies(z3_path_e(loc) == u_d, z3.And(u_d_constraint))
                solver.add(u_d_impl)

            r_l_constraint = [c for c in [lt_tile_or, rt_tile_or] if c != None]
            if len(r_l_constraint) > 0:
                r_l_impl = z3.Implies(z3_path_e(loc) == r_l, z3.And(r_l_constraint))
                solver.add(r_l_impl)

            r_u_constraint = [c for c in [up_tile_or, rt_tile_or] if c != None]
            if len(r_u_constraint) > 0:
                r_u_impl = z3.Implies(z3_path_e(loc) == r_u, z3.And(r_u_constraint))
                solver.add(r_u_impl)

            r_d_constraint = [c for c in [dn_tile_or, rt_tile_or] if c != None]
            if len(r_d_constraint) > 0:
                r_d_impl = z3.Implies(z3_path_e(loc) == r_d, z3.And(r_d_constraint))
                solver.add(r_d_impl)

            l_d_constraint = [c for c in [dn_tile_or, lt_tile_or] if c != None]
            if len(l_d_constraint) > 0:
                l_d_impl = z3.Implies(z3_path_e(loc) == l_d, z3.And(l_d_constraint))
                solver.add(l_d_impl)

            l_u_constraint = [c for c in [up_tile_or, lt_tile_or] if c != None]
            if len(l_u_constraint) > 0:
                l_u_impl = z3.Implies(z3_path_e(loc) == l_u, z3.And(l_u_constraint))
                solver.add(l_u_impl)

for anima in animas:
    solver.add(
        z3.Or(
            [
                z3_path_e(z3f_anima_location(anima)) == o_u,
                z3_path_e(z3f_anima_location(anima)) == r_o,
                z3_path_e(z3f_anima_location(anima)) == o_d,
                z3_path_e(z3f_anima_location(anima)) == l_o,
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
    print(model.eval(z3_path_e(z3f_anima_location(anima_gottlob))))
    for r in range(0, height):
        bvr = bit_vec_sort.cast(r)
        for c in range(0, width):
            bvc = bit_vec_sort.cast(c)
            location = z3u8Pair.u8Pair(bvc, bvr)
            if model.eval(z3_path_e(location) != path_enums[10]):
                path_tiles.append((c, r, model.eval(z3_path_e(location))))
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
