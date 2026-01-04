import z3


def solver_set_defaults(solver: z3.Optimize):
    solver.set("incremental", True)
    solver.set("maxsat_engine", "wmax")
