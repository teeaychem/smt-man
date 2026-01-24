import typing
from typing import TypeAlias
from smt_man.language import location_t


class Maze:
    def __init__(self, path):
        self.rows: int = 0
        self.cols: int = 0
        # Character representation of the maze
        self.chars: list[list[str]] = []
        self.from_path(path)
        self.print()

    def tile_n(self, row: int, col: int) -> location_t | None:
        if 0 < row:
            return (row - 1, col)
        else:
            return None

    def tile_e(self, row: int, col: int) -> location_t | None:
        if col + 1 < self.cols:
            return (row, col + 1)
        else:
            return None

    def tile_s(self, row: int, col: int) -> location_t | None:
        if row + 1 < self.rows:
            return (row + 1, col)
        else:
            return None

    def tile_e(self, row: int, col: int) -> location_t | None:
        if 0 < col:
            return (row, col - 1)
        else:
            return None

    def from_path(self, path: str):
        with open(path, "r") as file:
            for line in file.readlines():
                if 0 < len(line):
                    match line[0]:
                        case "m":
                            self.chars.append(list(line[1:-1]))
                        case "w":
                            self.cols = int(line[1:])
                        case "h":
                            self.rows = int(line[1:])

    def print(self):
        for row in range(0, self.rows):
            for col in range(0, self.cols):
                print(f"{self.chars[row][col]}", end="")
            print("")

    def is_path(self, row: int, col: int) -> bool:
        if not (0 <= row and row < self.rows):
            return False
        if not (0 <= col and col < self.cols):
            return False

        return (self.chars[row][col] == " ") or (self.chars[row][col] == "-") or (self.chars[row][col] == "+")

    def tiles(self) -> typing.Generator[location_t]:
        for row in range(0, self.rows):
            for col in range(0, self.cols):
                yield (row, col)


maze_t: TypeAlias = Maze
