import time

import z3

from smt_man.types import *
from smt_man.language import *


def set_defaults(solver: z3.Optimize):
    solver.set("incremental", True)
    solver.set("maxsat_engine", "wmax")


def timed_solve(optimizer: z3_optimizer_t, print_stats: bool = False) -> z3_model_t | None:
    time_solve_start: float = time.perf_counter()
    time_solve_end = 0

    result: z3_result_t = optimizer.check()
    time_solve_end: float = time.perf_counter()
    print(f"Result: {result} in {time_solve_end - time_solve_start:0.4f} seconds")

    if result == z3.sat:
        if print_stats:
            print(optimizer.statistics())
        model: z3_model_t = optimizer.model()
        return model
    else:
        return None
