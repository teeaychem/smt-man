from typing import TypeAlias
from smt_man.language import location_t


class Maze:
    def __init__(self, path):
        self.width = 0
        self.height = 0
        # Character representation of the maze
        self.chars = []
        self.from_path(path)

    def tile_n(self, col: int, row: int) -> location_t | None:
        if 0 < row:
            return (col, row - 1)
        else:
            return None

    def tile_e(self, col: int, row: int) -> location_t | None:
        if col + 1 < self.width:
            return (col + 1, row)
        else:
            return None

    def tile_s(self, col: int, row: int) -> location_t | None:
        if row + 1 < self.height:
            return (col, row + 1)
        else:
            return None

    def tile_e(self, col: int, row: int) -> location_t | None:
        if 0 < col:
            return (col - 1, row)
        else:
            return None

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

    def tiles(self):
        for row in range(0, self.height):
            for col in range(0, self.width):
                yield (col, row)


maze_t: TypeAlias = Maze
