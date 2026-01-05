import time

import z3

from smt_man.types import *
from smt_man.language import *


class mind:
    def set_defaults(solver: z3.Optimize):
        # solver.set("incremental", False)
        solver.set("maxsat_engine", "wmax")
        # solver.set("maxsat_engine", "maxres")
        # solver.set("maxsat_engine", "pd-maxres")
        # solver.set("maxsat_engine", "rc2")
        # solver.set("maxsat_engine", "maxres-bin")

        # solver.set("priority", "box")

        # solver.set("enable_lns", True)
        # solver.set("enable_sat", True)
        # solver.set("enable_sls", True)
        # solver.set("optsmt_engine", "symba")
        # solver.set("pb.compile_equality", True)

        # solver.set("ctrl_c", False)
        # solver.set("maxres.maximize_assignment", True)
        pass



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

    def to_file(optimizer: z3_optimizer_t, path):
        sexpr = optimizer.sexpr()
        sexprs = sexpr.split("\n")

        with open(path, "w") as file:
            for expr in sexprs:
                if 0 < len(expr) and expr[0] == ";":
                    continue
                if 4 < len(expr) and expr[1:4] == "set":
                    continue

                print(expr, file=file)
