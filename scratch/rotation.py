from math import sqrt


def next_left_offset(x: uint, y: uint, steps: uint, radius: uint, size: uint) -> (uint, uint):
    steps: uint = steps % (4 * (2 * radius - 1))

    low: uint = size // 2 - radius
    high: uint = size // 2 + radius - 1

    assert (((x == low) or (x == high)) and (low <= y and y <= high)) or (((y == low) or (y == high)) and (low <= x and x <= high))

    for i in range(0, 2):
        if steps == 0:
            continue

        if y == low:
            x_max = min(high - x, steps)
            x += x_max
            steps -= x_max
        if x == high:
            y_move = min(high - y, steps)
            y += y_move
            steps -= y_move
        if y == high:
            x_max = min(x - low, steps)
            x -= x_max
            steps -= x_max
        if x == low:
            y_max = min(y - low, steps)
            y -= y_max
            steps -= y_max

    return (x, y)


def square_offset(width: uint, x: uint, y: uint) -> uint:
    return (width * y) + x


def square_shuffle_left(square: [uint], size: uint):
    # steps: uint = steps % (4 * (2 * radius - 1))

    (x, y) = (0, 0)

    for radius in range(size // 2, 0, -1):
        arc = radius * 2

        point = size // 2 - radius

        for i in range(0, arc - 1):
            (x, y) = (point + i, point)
            temp = square[square_offset(size, x, y)]

            # (x, y) = next_left_offset(x, y, radius * 2 - 1, radius, size)

            for j in range(0, size - 1):
                (next_x, next_y) = next_left_offset(x, y, arc - 1, radius, size)
                square[square_offset(size, x, y)] = square[square_offset(size, next_x, next_y)]
                (x, y) = (next_x, next_y)
            square[square_offset(size, x, y)] = temp


def print_igrid(grid):
    size = int(sqrt(len(grid)))
    for row in range(0, size):
        for col in range(0, size):
            print(f"{grid[square_offset(size, col, row)]:2d}", end=" ")
        print("")
    print("")


def print_cgrid(grid):
    size = int(sqrt(len(grid)))
    for row in range(0, size):
        for col in range(0, size):
            print(f"{grid[square_offset(size, col, row)]}", end=" ")
        print("")
    print("")


### scratch


size = 4
square = [i for i in range(0, size**2)]

print_igrid(square)

square_shuffle_left(square, size)

print_igrid(square)

pac = "                     XXXXXX        XXXXXXXXXX     XXXXXXXXXXXX    XXXXXXXXXXXX   XXXXXXXXXX      XXXXXXX         XXXX            XXXX            XXXXXXX         XXXXXXXXXX       XXXXXXXXXXXX    XXXXXXXXXXXX     XXXXXXXXXX        XXXXXX                     "
cpac = list(pac)

print_cgrid(cpac)

square_shuffle_left(cpac, 16)

print_cgrid(cpac)
