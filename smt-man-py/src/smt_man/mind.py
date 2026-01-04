import z3
from smt_man.types import *
from smt_man.language import *


def solver_set_defaults(solver: z3.Optimize):
    solver.set("incremental", True)
    solver.set("maxsat_engine", "wmax")


