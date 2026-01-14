import typing
from typing import TypeAlias
from smt_man.language import location_t


class Maze:
    def __init__(self, path):
        self.x: int = 0
        self.y: int = 0
        # Character representation of the maze
        self.chars: list[list[str]] = []
        self.from_path(path)

    def tile_n(self, col: int, row: int) -> location_t | None:
        if 0 < row:
            return (col, row - 1)
        else:
            return None

    def tile_e(self, col: int, row: int) -> location_t | None:
        if col + 1 < self.x:
            return (col + 1, row)
        else:
            return None

    def tile_s(self, col: int, row: int) -> location_t | None:
        if row + 1 < self.y:
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
                            self.x = int(line[1:])
                        case "h":
                            self.y = int(line[1:])

    def print(self):
        for row in range(0, self.y):
            for col in range(0, self.x):
                print(f"{self.chars[row][col]}", end="")
            print("")

    def is_path(self, col, row) -> bool:
        return (self.chars[row][col] == " ") or (self.chars[row][col] == "-") or (self.chars[row][col] == "+")

    def tiles(self) -> typing.Generator[location_t]:
        for row in range(0, self.y):
            for col in range(0, self.x):
                yield (col, row)


maze_t: TypeAlias = Maze
