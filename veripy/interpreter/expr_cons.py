import ast
from enum import Enum
from typing import Dict

class AbstractExpr:
    pass

class AbstractCons:
    pass

class LinearExpr(AbstractExpr):
    def __init__(self, coeffs: Dict[str, float], offset: float):
        self.coeffs = coeffs
        self.offset = offset

    def scale(self, factor: float):
        return LinearExpr({k: v * factor for k, v in self.coeffs.items()}, self.offset * factor)

    @staticmethod
    def combine(lhs, rhs, op):
        coeffs = lhs.coeffs.copy()
        for k, v in rhs.coeffs.items():
            coeffs[k] = coeffs.get(k, 0) + (v if isinstance(op, (ast.Add,)) else -v)
        offset = lhs.offset + (rhs.offset if isinstance(op, (ast.Add,)) else -rhs.offset)
        return LinearExpr(coeffs, offset)

    def __repr__(self):
        terms = [f"{v}*{k}" for k, v in self.coeffs.items()]
        return " + ".join(terms + [str(self.offset)])


class Op(Enum):
    LE = "<="
    LT = "<"
    GE = ">="
    GT = ">"
    EQ = "=="
    NE = "!="

    @staticmethod
    def from_ast(op_node):
        mapping = {
            ast.Lt: Op.LT,
            ast.LtE: Op.LE,
            ast.Gt: Op.GT,
            ast.GtE: Op.GE,
            ast.Eq: Op.EQ,
            ast.NotEq: Op.NE
        }
        return mapping[type(op_node)]

    def negate(self):
        negation_map = {
            Op.LE: Op.GT,
            Op.LT: Op.GE,
            Op.GE: Op.LT,
            Op.GT: Op.LE,
            Op.EQ: Op.NE,
            Op.NE: Op.EQ
        }
        return negation_map[self]


class LinearConstraint(AbstractCons):
    def __init__(self, lhs: 'LinearExpr', op: Op, rhs: 'LinearExpr'):
        combined_coeffs = lhs.coeffs.copy()
        for k, v in rhs.coeffs.items():
            combined_coeffs[k] = combined_coeffs.get(k, 0) - v
        combined_offset = lhs.offset - rhs.offset

        self.expr = LinearExpr(combined_coeffs, combined_offset)
        self.op = op

    def negate(self):
        return LinearConstraint(self.expr, self.op.negate(), LinearExpr({}, 0))

    def __repr__(self):
        return f"{self.expr} {self.op.value} 0"
