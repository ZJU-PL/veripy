"""
Type checking and inference
"""
from typing import List
from veripy.parser.syntax import *
from veripy.typecheck import types as ty
from veripy.built_ins import FUNCTIONS
from veripy.log import log

def issubtype(actual, expected):
    # Any accepts anything
    if expected == ty.TANY:
        return True
    # Unknown cannot be assumed to be a subtype of a concrete type
    if actual == ty.TANY:
        return False
    # Exact match
    if actual == expected:
        return True
    # Arrays are covariant in element type for our purposes
    if isinstance(actual, ty.TARR) and isinstance(expected, ty.TARR):
        return issubtype(actual.ty, expected.ty)
    # Refinement types: {x: T | P1(x)} <: {x: T | P2(x)} if P1(x) ==> P2(x)
    if isinstance(actual, ty.TREFINED) and isinstance(expected, ty.TREFINED):
        if actual.base_type == expected.base_type:
            # For now, we'll be conservative and require exact predicate match
            # In a full implementation, we'd check if actual.predicate ==> expected.predicate
            return actual.predicate == expected.predicate
    # {x: T | P(x)} <: T (refinement is subtype of base type)
    if isinstance(actual, ty.TREFINED) and actual.base_type == expected:
        return True
    return False

def type_check_stmt(sigma : dict, func_sigma : dict, stmt : Stmt):
    if isinstance(stmt, Skip):
        return sigma
    if isinstance(stmt, Seq):
        return type_check_stmt(type_check_stmt(sigma, func_sigma, stmt.s1), func_sigma, stmt.s2)
    if isinstance(stmt, Assign):
        # Subscript updates are encoded as:
        #   Assign(Store(arr, idx, value), Literal(True))  # dummy rhs
        # so the "real" rhs lives inside stmt.var.val.
        if isinstance(stmt.var, Store):
            arr_expr: Expr = stmt.var.arr
            idx_expr: Expr = stmt.var.idx
            val_expr: Expr = stmt.var.val
            arr_ty = type_check_expr(sigma, func_sigma, ty.TANY, arr_expr)
            if not isinstance(arr_ty, ty.TARR):
                # Late binding: if unknown variable, establish as array type based on value
                if isinstance(arr_expr, Var) and sigma.get(arr_expr.name, ty.TANY) == ty.TANY:
                    elem_ty = type_infer_expr(sigma, func_sigma, val_expr)
                    sigma[arr_expr.name] = ty.TARR(elem_ty)
                    arr_ty = sigma[arr_expr.name]
                else:
                    raise TypeError(f'Assignment to subscript requires array type, got {arr_ty}')
            type_check_expr(sigma, func_sigma, ty.TINT, idx_expr)
            elem_ty = arr_ty.ty if isinstance(arr_ty, ty.TARR) else type_infer_expr(sigma, func_sigma, val_expr)
            type_check_expr(sigma, func_sigma, elem_ty, val_expr)
            return sigma

        inferred = type_infer_expr(sigma, func_sigma, stmt.expr)
        # Normalize variable name (LHS may be a raw string or a Var node)
        var_name = stmt.var if isinstance(stmt.var, str) else getattr(stmt.var, "name", None)
        if var_name is not None:
            if var_name not in sigma or sigma[var_name] == ty.TANY:
                sigma[var_name] = inferred
            elif not issubtype(inferred, sigma[var_name]):
                # Allow refinement compatibility
                if isinstance(sigma[var_name], ty.TREFINED) and issubtype(inferred, sigma[var_name].base_type):
                    pass
                else:
                    raise TypeError(f'Mutating Type of {var_name}!')
            return sigma

        # Unknown LHS shape: still ensure RHS is type-inferable
        return sigma
    if isinstance(stmt, FieldAssignStmt):
        type_infer_expr(sigma, func_sigma, stmt.value)
        return sigma
    if isinstance(stmt, AugAssign):
        # Conservative: treat augmented arithmetic as int operations.
        if isinstance(stmt.var, Var) and stmt.var.name not in sigma:
            sigma[stmt.var.name] = ty.TANY
        if isinstance(stmt.var, Var):
            type_check_expr(sigma, func_sigma, ty.TINT, stmt.var)
            type_check_expr(sigma, func_sigma, ty.TINT, stmt.expr)
            if sigma[stmt.var.name] == ty.TANY:
                sigma[stmt.var.name] = ty.TINT
            return sigma
        type_infer_expr(sigma, func_sigma, stmt.expr)
        return sigma
    if isinstance(stmt, ForLoop):
        if stmt.loop_var not in sigma:
            sigma[stmt.loop_var] = ty.TANY
        type_infer_expr(sigma, func_sigma, stmt.iterable)
        sigma = type_check_stmt(sigma, func_sigma, stmt.body)
        if stmt.orelse is not None:
            sigma = type_check_stmt(sigma, func_sigma, stmt.orelse)
        return sigma
    if isinstance(stmt, Break) or isinstance(stmt, Continue):
        return sigma
    if isinstance(stmt, Raise):
        if stmt.exc_expr is not None:
            type_infer_expr(sigma, func_sigma, stmt.exc_expr)
        if stmt.cause is not None:
            type_infer_expr(sigma, func_sigma, stmt.cause)
        return sigma
    if isinstance(stmt, If):
        type_check_expr(sigma, func_sigma, ty.TBOOL, stmt.cond)
        return type_check_stmt(type_check_stmt(sigma, func_sigma, stmt.lb), func_sigma, stmt.rb)
    if isinstance(stmt, Assert) or isinstance(stmt, Assume):
        type_check_expr(sigma, func_sigma, ty.TBOOL, stmt.e)
        return sigma
    if isinstance(stmt, While):
        type_check_expr(sigma, func_sigma, ty.TBOOL, stmt.cond)
        for i in stmt.invariants:
            type_check_expr(sigma, func_sigma, ty.TBOOL, i)
        return type_check_stmt(sigma, func_sigma, stmt.body)
    if isinstance(stmt, Havoc):
        return sigma
    
    # Be permissive for yet-unsupported statement forms: skipping type checking is
    # better than failing verification up-front (the verifier may still reject).
    return sigma

def type_check_expr(sigma: dict, func_sigma : dict, expected, expr: Expr):
    actual = type_infer_expr(sigma, func_sigma, expr)
    if actual == ty.TANY and isinstance(expr, Var):
        sigma[expr.name] = expected
        return expected
    if actual == expected or issubtype(actual, expected):
        return actual
    else:
        raise TypeError(f'{expr}: expected type {expected}, actual type {actual};\
                        issubtype({actual}, {expected})={issubtype(actual, expected)}')

###############################################
#               Type Inference                #
###############################################

def type_infer_Subscript(sigma, func_sigma, expr: Subscript):
    obj = expr.var
    obj_ty = type_infer_expr(sigma, func_sigma, obj)
    # index must be int
    type_check_expr(sigma, func_sigma, ty.TINT, expr.subscript)
    if isinstance(obj_ty, ty.TARR):
        return obj_ty.ty
    # Late binding: if unknown variable, assume it is an array of any, refined by context
    if isinstance(obj, Var) and sigma.get(obj.name, ty.TANY) == ty.TANY:
        sigma[obj.name] = ty.TARR(ty.TANY)
        return ty.TANY
    return ty.TANY

def type_infer_literal(sigma, func_sigma, expr: Literal):
    return {
        VBool: ty.TBOOL,
        VInt : ty.TINT,
    }.get(type(expr.value))

def type_infer_UnOp(sigma, func_sigma, expr: UnOp):
    if expr.op == BoolOps.Not:
        return type_check_expr(sigma, func_sigma, ty.TBOOL, expr.e)
    if expr.op == ArithOps.Neg:
        return type_check_expr(sigma, func_sigma, ty.TINT, expr.e)

def type_infer_BinOp(sigma, func_sigma, expr: BinOp):
    if isinstance(expr.op, ArithOps):
        type_check_expr(sigma, func_sigma, ty.TINT, expr.e1)
        return type_check_expr(sigma, func_sigma, ty.TINT, expr.e2)
    if isinstance(expr.op, CompOps):
        # Ordering comparisons are over ints
        if expr.op in (CompOps.Lt, CompOps.Le, CompOps.Gt, CompOps.Ge):
            type_check_expr(sigma, func_sigma, ty.TINT, expr.e1)
            type_check_expr(sigma, func_sigma, ty.TINT, expr.e2)
            return ty.TBOOL

        # Equality/inequality work for ints and bools (and generally any matching types)
        if expr.op in (CompOps.Eq, CompOps.Neq):
            l_ty = type_infer_expr(sigma, func_sigma, expr.e1)
            r_ty = type_infer_expr(sigma, func_sigma, expr.e2)
            # Late-bind unknowns to the other side
            if l_ty == ty.TANY and isinstance(expr.e1, Var):
                sigma[expr.e1.name] = r_ty
                l_ty = r_ty
            if r_ty == ty.TANY and isinstance(expr.e2, Var):
                sigma[expr.e2.name] = l_ty
                r_ty = l_ty
            if l_ty != ty.TANY and r_ty != ty.TANY and l_ty != r_ty:
                raise TypeError(f'Cannot compare {l_ty} to {r_ty}')
            return ty.TBOOL

        # Membership: x in container
        if expr.op in (CompOps.In, CompOps.NotIn):
            container_ty = type_infer_expr(sigma, func_sigma, expr.e2)
            elem_ty = None
            if isinstance(container_ty, ty.TARR):
                elem_ty = container_ty.ty
            elif isinstance(container_ty, ty.TSET):
                elem_ty = container_ty.elem_ty
            elif isinstance(container_ty, ty.TDICT):
                elem_ty = container_ty.key_ty
            else:
                # If unknown container, allow and infer later
                elem_ty = ty.TANY
            if elem_ty != ty.TANY:
                type_check_expr(sigma, func_sigma, elem_ty, expr.e1)
            else:
                # If element is a known int var, default to int membership
                if isinstance(expr.e1, Var) and sigma.get(expr.e1.name) == ty.TANY:
                    sigma[expr.e1.name] = ty.TINT
            return ty.TBOOL

        # Fallback: treat as boolean result
        return ty.TBOOL
    if isinstance(expr.op, BoolOps):
        type_check_expr(sigma, func_sigma, ty.TBOOL, expr.e1)
        return type_check_expr(sigma, func_sigma, ty.TBOOL, expr.e2)

def type_infer_Slice(sigma, func_sigma, expr: Slice):
    if expr.lower or expr.upper or expr.step:
        if expr.lower:
            type_check_expr(sigma, func_sigma, ty.TINT, expr.lower)
        if expr.upper:
            type_check_expr(sigma, func_sigma, ty.TINT, expr.upper)
        if expr.step:
            type_check_expr(sigma, func_sigma, ty.TINT, expr.step)
        return ty.TSLICE
    raise Exception('Slice must have at least one field that is not None')

def type_infer_FunctionCall(sigma, func_sigma: dict, expr: FunctionCall):
    if isinstance(expr.func_name, Var) and expr.func_name.name == 'len':
        if len(expr.args) != 1:
            raise TypeError('len expects exactly one argument')
        # The argument can be an array or sequence; we return int
        return ty.TINT
    if isinstance(expr.func_name, Var):
        fname = expr.func_name.name
        # Use provided function typing env if available
        if fname in func_sigma:
            fty = func_sigma[fname]['returns'] if isinstance(func_sigma[fname], dict) else func_sigma[fname]
            return fty
        # Default to int for unknown
        return ty.TINT
    raise NotImplementedError(f'Function call typing not supported: {expr}')

def type_infer_quantification(sigma, func_sigma, expr: Quantification):
    sigma[expr.var.name] = ty.TANY if expr.ty is None else expr.ty
    type_check_expr(sigma, func_sigma, ty.TBOOL, expr.expr)
    if sigma[expr.var.name] == ty.TANY:
        raise Exception(f'Cannot infer type for {expr.var} in {expr}')
    expr.ty = sigma[expr.var.name]
    sigma.pop(expr.var.name)
    return ty.TBOOL

def type_infer_expr(sigma: dict, func_sigma : dict, expr: Expr):
    if isinstance(expr, Literal):
        return type_infer_literal(sigma, func_sigma, expr)
    if isinstance(expr, Var):
        # Late-bind unknown vars to TANY to avoid assertion failures
        if expr.name not in sigma:
            sigma[expr.name] = ty.TANY
        return sigma[expr.name]
    if isinstance(expr, UnOp):
        return type_infer_UnOp(sigma, func_sigma, expr)
    if isinstance(expr, BinOp):
        return type_infer_BinOp(sigma, func_sigma, expr)
    if isinstance(expr, Slice):
        return type_infer_Slice(sigma, func_sigma, expr)
    if isinstance(expr, Quantification):
        return type_infer_quantification(sigma, func_sigma, expr)
    if isinstance(expr, Subscript):
        return type_infer_Subscript(sigma, func_sigma, expr)
    if isinstance(expr, Store):
        # store(a, i, v) has type Array(elemTy)
        arr_ty = type_infer_expr(sigma, func_sigma, expr.arr)
        type_check_expr(sigma, func_sigma, ty.TINT, expr.idx)
        val_ty = type_infer_expr(sigma, func_sigma, expr.val)
        if isinstance(arr_ty, ty.TARR):
            type_check_expr(sigma, func_sigma, arr_ty.ty, expr.val)
            return arr_ty
        # If not known, create array type with val_ty
        if isinstance(expr.arr, Var) and sigma.get(expr.arr.name, ty.TANY) == ty.TANY:
            sigma[expr.arr.name] = ty.TARR(val_ty)
            return sigma[expr.arr.name]
        return ty.TARR(val_ty)
    if isinstance(expr, FunctionCall):
        # Built-ins only for now: len, set, dict, card, mem, keys
        if isinstance(expr.func_name, Var) and expr.func_name.name in ('set', 'dict', 'card', 'mem', 'keys'):
            return ty.TANY
        return type_infer_FunctionCall(sigma, func_sigma, expr)
    if isinstance(expr, Old):
        return type_infer_expr(sigma, func_sigma, expr.expr)
    if isinstance(expr, RecordField):
        # Treat fields as ints/bools by default (conservative)
        return ty.TANY
    if isinstance(expr, SetLiteral):
        # If elements present, infer their type; else default to int
        elem_ty = ty.TINT if not expr.elements else type_infer_expr(sigma, func_sigma, expr.elements[0])
        return ty.TSET(elem_ty)
    if isinstance(expr, DictLiteral):
        # Infer key/value from first pair when available
        if expr.keys and expr.values:
            k_ty = type_infer_expr(sigma, func_sigma, expr.keys[0])
            v_ty = type_infer_expr(sigma, func_sigma, expr.values[0])
        else:
            k_ty, v_ty = ty.TINT, ty.TINT
        return ty.TDICT(k_ty, v_ty)
    if isinstance(expr, StringLiteral):
        return str
    if isinstance(expr, StringConcat):
        type_check_expr(sigma, func_sigma, str, expr.left)
        type_check_expr(sigma, func_sigma, str, expr.right)
        return str
    if isinstance(expr, StringLength):
        type_check_expr(sigma, func_sigma, str, expr.string_expr)
        return ty.TINT
    if isinstance(expr, StringIndex):
        type_check_expr(sigma, func_sigma, str, expr.string_expr)
        type_check_expr(sigma, func_sigma, ty.TINT, expr.index)
        return str
    if isinstance(expr, StringSubstring):
        type_check_expr(sigma, func_sigma, str, expr.string_expr)
        type_check_expr(sigma, func_sigma, ty.TINT, expr.start)
        if expr.end:
            type_check_expr(sigma, func_sigma, ty.TINT, expr.end)
        return str
    if isinstance(expr, StringContains):
        type_check_expr(sigma, func_sigma, str, expr.string_expr)
        type_check_expr(sigma, func_sigma, str, expr.substring)
        return ty.TBOOL
    if isinstance(expr, SetOp):
        # Set operations preserve element type for union/intersection/diff; membership returns bool
        l_ty = type_infer_expr(sigma, func_sigma, expr.left)
        r_ty = type_infer_expr(sigma, func_sigma, expr.right)
        if expr.op in (SetOps.Member, SetOps.Subset, SetOps.Superset):
            return ty.TBOOL
        # default to left set type when possible
        return l_ty if isinstance(l_ty, ty.TSET) else r_ty
    if isinstance(expr, SetCardinality):
        type_infer_expr(sigma, func_sigma, expr.set_expr)
        return ty.TINT
    if isinstance(expr, DictGet):
        d_ty = type_infer_expr(sigma, func_sigma, expr.dict_expr)
        k_ty = type_infer_expr(sigma, func_sigma, expr.key)
        if isinstance(d_ty, ty.TDICT):
            type_check_expr(sigma, func_sigma, d_ty.key_ty, expr.key)
            return d_ty.val_ty
        # If unknown, at least check key type compatibility with int
        type_check_expr(sigma, func_sigma, k_ty, expr.key)
        return ty.TANY
    if isinstance(expr, DictSet):
        d_ty = type_infer_expr(sigma, func_sigma, expr.dict_expr)
        k_ty = type_infer_expr(sigma, func_sigma, expr.key)
        v_ty = type_infer_expr(sigma, func_sigma, expr.value)
        if isinstance(d_ty, ty.TDICT):
            type_check_expr(sigma, func_sigma, d_ty.key_ty, expr.key)
            type_check_expr(sigma, func_sigma, d_ty.val_ty, expr.value)
            return d_ty
        return ty.TDICT(k_ty, v_ty)
    if isinstance(expr, DictKeys):
        return ty.TSET(ty.TANY)
    if isinstance(expr, DictValues):
        return ty.TSET(ty.TANY)
    if isinstance(expr, DictContains):
        d_ty = type_infer_expr(sigma, func_sigma, expr.dict_expr)
        if isinstance(d_ty, ty.TDICT):
            type_check_expr(sigma, func_sigma, d_ty.key_ty, expr.key)
        return ty.TBOOL
    if isinstance(expr, ListComprehension):
        # Element type from element_expr; default to inferred element if unknown
        elem_ty = type_infer_expr(sigma, func_sigma, expr.element_expr)
        return ty.TARR(elem_ty if elem_ty != ty.TANY else ty.TANY)
    if isinstance(expr, SetComprehension):
        elem_ty = type_infer_expr(sigma, func_sigma, expr.source)
        return ty.TSET(elem_ty if elem_ty != ty.TANY else ty.TANY)
    if isinstance(expr, FieldAccess):
        return ty.TANY
    if isinstance(expr, MethodCall):
        return ty.TANY

    raise NotImplementedError(f'Unknown expression: {expr}')

def check_refinement_predicate(sigma: dict, func_sigma: dict, var_name: str, refined_type: ty.TREFINED):
    """Check if a variable satisfies its refinement predicate"""
    # Create a temporary environment with the variable bound to its type
    temp_sigma = dict(sigma)
    temp_sigma[var_name] = refined_type.base_type
    
    # Type check the predicate with the variable in scope
    try:
        type_check_expr(temp_sigma, func_sigma, ty.TBOOL, refined_type.predicate)
        return True
    except TypeError as e:
        raise TypeError(f'Refinement predicate for {var_name} is not well-typed: {e}')
    except Exception as e:
        raise Exception(f'Error checking refinement predicate for {var_name}: {e}')
