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

    def tiles(self):
        for row in range(0, self.height):
            for col in range(0, self.width):
                yield (col, row)
