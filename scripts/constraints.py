from smt_man.path4 import path4_t
import time
import argparse

import z3

import smt_man
from smt_man.maze import maze_t
from smt_man.mind import mind
from smt_man.types import *
from smt_man.language import *


parser = argparse.ArgumentParser(
    prog="explorations",
    description="tmp",
)

parser.add_argument("-a", "--anima", type=str, help="Anima name", required=True)
parser.add_argument("-m", "--maze", help="path to the maze", type=str, default="./resources/maze/source.txt")
parser.add_argument("-p", "--persona", type=str, help="Persona name", default="persona")
parser.add_argument("-t", "--test", help="Test paths", action=argparse.BooleanOptionalAction)
parser.add_argument("-f", "--file", help="File", type=str, required=True)

parsed_args = parser.parse_args()
print(parsed_args)

maze_path: str = parsed_args.maze
anima_name: str = parsed_args.anima
persona_name: str = parsed_args.persona


persona: z3_expr_t = z3.Const(persona_name, z3s_persona_t)

maze = smt_man.maze.Maze(maze_path)


optimizer = z3.Optimize()
mind.set_defaults(optimizer)


###

animas: list[z3_expr_t] = [
    z3.Const(anima_name, z3s_anima_t),
]
## Path

print(f"\nGenerating constraints for persona named '{persona_name}' and anima named '{anima_name}' ... ", end="")

path = path4_t()

path.assert_persona_is_origin(optimizer, persona)
path.assert_anima_is_origin(optimizer, animas[0])

path.assert_empty_constraints(optimizer, maze)
path.assert_constant_tile_constraints(optimizer, maze)
path.assert_constant_origin_is_anima_or_persona(optimizer, maze, animas, persona)
path.assert_constant_hints(optimizer, maze)

print("done!")

if parsed_args.file is not None:
    print(f"Writing constraints to {parsed_args.file} ... ", end="")
    mind.to_file(optimizer, parsed_args.file)
    print("done!")


