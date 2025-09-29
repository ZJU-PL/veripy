import ast
from veripy.interpreter.expr_cons import LinearExpr, LinearConstraint, Op

def parse_expr(expr):
    def walk(node):
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, (ast.Add, ast.Sub)):
                l = walk(node.left)
                r = walk(node.right)
                return LinearExpr.combine(l, r, node.op)

            elif isinstance(node.op, ast.Mult):
                left_const = get_constant_value(node.left)
                right_const = get_constant_value(node.right)

                if left_const is not None:
                    r = walk(node.right)
                    return r.scale(left_const)
                elif right_const is not None:
                    l = walk(node.left)
                    return l.scale(right_const)
                else:
                    raise ValueError("Non-linear mult: both sides are variable")

        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            operand = walk(node.operand)
            return operand.scale(-1)

        elif isinstance(node, ast.Name):
            return LinearExpr({node.id: 1}, 0)

        elif isinstance(node, (ast.Constant, ast.Num)):
            return LinearExpr({}, node.n if hasattr(node, 'n') else node.value)

        raise ValueError(f"Unsupported expr: {ast.dump(node)}")

    def get_constant_value(node):
        """Returns numeric constant value if the node is a constant or -constant."""
        if isinstance(node, (ast.Constant, ast.Num)):
            return node.n if hasattr(node, 'n') else node.value
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            sub = get_constant_value(node.operand)
            if sub is not None:
                return -sub
        return None

    return walk(expr)

def parse_cons(node):
    if not isinstance(node, ast.Compare):
        raise ValueError(f"Expected comparison node, got: {type(node).__name__}")

    lhs = parse_expr(node.left)
    rhs = parse_expr(node.comparators[0])
    op = Op.from_ast(node.ops[0])

    return LinearConstraint(lhs, op, rhs)