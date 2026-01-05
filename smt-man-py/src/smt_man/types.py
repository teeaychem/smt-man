# z3 types

from z3 import BoolRef as z3_bool_t
from z3 import DatatypeSortRef as z3_datatype_sort_t
from z3 import ExprRef as z3_expr_t
from z3 import FuncDeclRef as z3_fn_t
from z3 import ModelRef as z3_model_t
from z3 import Optimize as z3_optimizer_t
from z3 import SortRef as z3_sort_t

z3_location_t = tuple[z3_expr_t, z3_expr_t]

# module custom types

location_t = tuple[int, int]
anima_id_t = int

# module class types

from smt_man.maze import Maze as maze_t
