from z3 import Z3_optimize_to_string_bytes
import time

import z3

from smt_man.types import *
from smt_man.language import *


class mind:
    def set_defaults(solver: z3.Optimize) -> None:
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

    def to_file(optimizer: z3_optimizer_t, path) -> None:
        sexpr: str = optimizer.sexpr()
        sexprs: list[str] = sexpr.split("\n")

        with open(path, "w") as file:
            expr_buffer: None | str = None
            for expr in sexprs:
                if len(expr) == 0:
                    continue

                match expr[0]:
                    case ";":
                        continue
                    case "(":
                        if expr[1:-1] in ["check-sat"]:
                            continue
                        if 4 < len(expr) and expr[1:4] == "set":
                            continue
                        else:
                            if expr_buffer is not None:
                                print(expr_buffer, file=file)
                            expr_buffer: str = expr
                    case " ":
                        assert expr_buffer is not None
                        expr_buffer += " " + expr.strip()

            if expr_buffer is not None:
                print(expr_buffer, file=file)
