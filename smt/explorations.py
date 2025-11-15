from z3 import *  # pyright: ignore[reportMissingTypeStubs, reportWildcardImportFromLibrary]

maze_chars = []
width = 0
height = 0

# Character representation of the maze
with open("../resources/maze/source.txt", "r") as file:
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

# Tiles
maze_tile_terms = [[None for _ in range(0, width)] for _ in range(0, height)]

TileSort, mk_tile, (row, col) = z3.TupleSort("Tile", [IntSort(), IntSort()])
tile_origin = mk_tile(0, 0)

for r in range(0, height):
    for c in range(0, width):
        maze_tile_terms[r][c] = mk_tile(r, c)

z3_f_is_open = Function("is_open", TileSort, BoolSort())

for r in range(0, height):
    for c in range(0, width):
        match maze_chars[r][c]:
            case " ":
                solver.add(z3.mk_not(z3_f_is_open(maze_tile_terms[r][c])))
            case _:
                solver.add(z3_f_is_open(maze_tile_terms[r][c]))

# Directions
DirectionSort = z3.DeclareSort("Direction")
direction_up = z3.Const("direction_up", DirectionSort)
direction_right = z3.Const("direction_right", DirectionSort)
direction_down = z3.Const("direction_down", DirectionSort)
direction_left = z3.Const("direction_left", DirectionSort)

# Animas
AnimaSort = z3.DeclareSort("Anima")
anima_a = z3.Const("a", AnimaSort)
anima_gottlob = z3.Const("gottlob", AnimaSort)

p_anima_facing = Function("anima_is_facing", AnimaSort, DirectionSort)
solver.add(p_anima_facing(anima_gottlob) == direction_down)

solver.assert_exprs(z3.Distinct(
    direction_up, direction_right, direction_down, direction_left
))


result = solver.check()
model = solver.model()
print(f"Result: {result}")
print(f"{model}")
print(model.eval(p_anima_facing(anima_gottlob)))
