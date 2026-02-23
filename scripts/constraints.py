from email.policy import default
from smt_man.path4 import path4_t
import time
import argparse

import z3

import smt_man
from smt_man.maze import maze_t
from smt_man.mind import mind
from smt_man.types import *
from smt_man.language import *


def generate_constraints(anima_count: int, anima_id: int, out_file: str, maze_source: str):
    persona: z3_expr_t = z3.Const(persona_name, z3s_persona_t)

    maze = smt_man.maze.Maze(maze_source)

    optimizer = z3.Optimize()
    mind.set_defaults(optimizer)

    ###

    animas: list[z3_expr_t] = [z3.Const(f"anima_{idx}", z3s_anima_t) for idx in range(0, anima_count)]
    ## Path

    print(f"\nGenerating constraints for persona named '{persona_name}' and anima named '{anima_id}' ... ", end="")

    path = path4_t()

    path.assert_persona_is_origin(optimizer, persona)
    path.assert_anima_is_origin(optimizer, animas[anima_id])

    path.assert_empty_constraints(optimizer, maze)
    path.assert_constant_tile_constraints(optimizer, maze)
    path.assert_constant_origin_is_anima_or_persona(optimizer, maze, animas, persona)
    path.assert_constant_hints(optimizer, maze)

    print("done!")

    if parsed_args.file is not None:
        print(f"Writing constraints to {out_file} ... ", end="")
        mind.to_file(optimizer, out_file)
        print("done!")


# end: generate_constraints


parser = argparse.ArgumentParser(
    prog="explorations",
    description="tmp",
)

parser.add_argument("-a", "--anima", type=int, help="Anima ID", required=True)
parser.add_argument("-c", "--count", type=int, help="Anima count", default=4)
parser.add_argument("-m", "--maze", help="path to the maze", type=str, default="./resources/maze/source.txt")
parser.add_argument("-p", "--persona", type=str, help="Persona name", default="persona")
parser.add_argument("-t", "--test", help="Test paths", action=argparse.BooleanOptionalAction)
parser.add_argument("-f", "--file", help="File", type=str)

parsed_args = parser.parse_args()


anima_count: str = parsed_args.count
anima_id: str = parsed_args.anima

file = parsed_args.file if parsed_args.file else f"{anima_id}.smt2"

maze_path: str = parsed_args.maze

persona_name: str = parsed_args.persona


generate_constraints(anima_count=anima_count, anima_id=anima_id, out_file=file, maze_source=maze_path)
