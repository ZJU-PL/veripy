"""
Utility functions for transformer module.
"""

from veripy.parser.syntax import *


def raise_exception(msg: str):
    raise Exception(msg)


def subst(this: str, withThis: Expr, inThis: Expr) -> Expr:
    """
    Substitute a variable (`this`) with `withThis` in expression `inThis`.
    """
    if isinstance(inThis, Var):
        if inThis.name == this:
            return withThis
        else:
            return inThis
    if isinstance(inThis, BinOp):
        return BinOp(subst(this, withThis, inThis.e1), inThis.op, subst(this, withThis, inThis.e2))
    if isinstance(inThis, Literal):
        return inThis
    if isinstance(inThis, UnOp):
        return UnOp(inThis.op, subst(this, withThis, inThis.e))
    if isinstance(inThis, Quantification):
        if this != inThis.var.name and isinstance(inThis.expr, Expr):
            return Quantification(inThis.var, subst(this, withThis, inThis.expr), inThis.ty)
        return inThis
    if isinstance(inThis, FunctionCall):
        # Substitute within callee and args.
        fn = inThis.func_name
        if isinstance(fn, Expr):
            fn = subst(this, withThis, fn)
        return FunctionCall(
            fn,
            [subst(this, withThis, a) for a in inThis.args],
            native=getattr(inThis, "native", True),
        )
    if isinstance(inThis, Subscript):
        return Subscript(
            subst(this, withThis, inThis.var),
            subst(this, withThis, inThis.subscript)
        )
    if isinstance(inThis, Store):
        return Store(
            subst(this, withThis, inThis.arr),
            subst(this, withThis, inThis.idx),
            subst(this, withThis, inThis.val)
        )
    if isinstance(inThis, Old):
        return inThis
    if isinstance(inThis, SetLiteral):
        return SetLiteral([subst(this, withThis, e) for e in inThis.elements])
    if isinstance(inThis, DictLiteral):
        return DictLiteral(
            [subst(this, withThis, k) for k in inThis.keys],
            [subst(this, withThis, v) for v in inThis.values]
        )
    if isinstance(inThis, SetOp):
        return SetOp(
            subst(this, withThis, inThis.left),
            inThis.op,
            subst(this, withThis, inThis.right)
        )
    if isinstance(inThis, FieldAccess):
        return FieldAccess(subst(this, withThis, inThis.obj), inThis.field)
    if isinstance(inThis, StringConcat):
        return StringConcat(
            subst(this, withThis, inThis.left),
            subst(this, withThis, inThis.right)
        )
    if isinstance(inThis, StringLength):
        return StringLength(subst(this, withThis, inThis.string_expr))
    if isinstance(inThis, StringIndex):
        return StringIndex(
            subst(this, withThis, inThis.string_expr),
            subst(this, withThis, inThis.index)
        )
    if isinstance(inThis, StringSubstring):
        return StringSubstring(
            subst(this, withThis, inThis.string_expr),
            subst(this, withThis, inThis.start),
            subst(this, withThis, inThis.end) if inThis.end else None
        )
    if isinstance(inThis, StringContains):
        return StringContains(
            subst(this, withThis, inThis.substring),
            subst(this, withThis, inThis.string_expr)
        )
    if isinstance(inThis, Range):
        return Range(
            start=subst(this, withThis, inThis.start) if inThis.start else None,
            stop=subst(this, withThis, inThis.stop),
            step=subst(this, withThis, inThis.step) if inThis.step else None
        )
    if isinstance(inThis, Enumerate):
        return Enumerate(
            subst(this, withThis, inThis.iterable),
            subst(this, withThis, inThis.start) if inThis.start else None
        )
    if isinstance(inThis, Zip):
        return Zip([subst(this, withThis, e) for e in inThis.args])
    if isinstance(inThis, Map):
        return Map(subst(this, withThis, inThis.func), subst(this, withThis, inThis.iterable))
    if isinstance(inThis, Filter):
        return Filter(subst(this, withThis, inThis.func), subst(this, withThis, inThis.iterable))
    if isinstance(inThis, Reduce):
        return Reduce(
            subst(this, withThis, inThis.func),
            subst(this, withThis, inThis.iterable),
            subst(this, withThis, inThis.initial) if inThis.initial else None
        )
    if isinstance(inThis, ListComprehension):
        return ListComprehension(
            subst(this, withThis, inThis.element_expr),
            subst(this, withThis, inThis.source),
            subst(this, withThis, inThis.predicate) if inThis.predicate else None
        )
    if isinstance(inThis, SetComprehension):
        return SetComprehension(
            subst(this, withThis, inThis.element_var),
            subst(this, withThis, inThis.source),
            subst(this, withThis, inThis.predicate) if inThis.predicate else None
        )
    if isinstance(inThis, DictComprehension):
        return DictComprehension(
            subst(this, withThis, inThis.key_expr),
            subst(this, withThis, inThis.value_expr),
            inThis.element_var,
            subst(this, withThis, inThis.iterable),
            subst(this, withThis, inThis.predicate) if inThis.predicate else None,
        )
    if isinstance(inThis, DictGet):
        return DictGet(
            subst(this, withThis, inThis.dict_expr),
            subst(this, withThis, inThis.key),
            subst(this, withThis, inThis.default) if inThis.default else None
        )
    if isinstance(inThis, DictSet):
        return DictSet(
            subst(this, withThis, inThis.dict_expr),
            subst(this, withThis, inThis.key),
            subst(this, withThis, inThis.value)
        )
    if isinstance(inThis, DictKeys):
        return DictKeys(subst(this, withThis, inThis.dict_expr))
    if isinstance(inThis, DictValues):
        return DictValues(subst(this, withThis, inThis.dict_expr))
    if isinstance(inThis, DictContains):
        return DictContains(
            subst(this, withThis, inThis.dict_expr),
            subst(this, withThis, inThis.key)
        )
    if isinstance(inThis, SetCardinality):
        return SetCardinality(subst(this, withThis, inThis.set_expr))
    if isinstance(inThis, Comprehension):
        return Comprehension(
            inThis.kind,
            subst(this, withThis, inThis.element),
            [subst(this, withThis, g) for g in inThis.generators]
        )
    if isinstance(inThis, Generator):
        return Generator(
            subst(this, withThis, inThis.target),
            subst(this, withThis, inThis.iterable),
            subst(this, withThis, inThis.predicate) if inThis.predicate else None
        )
    if isinstance(inThis, Lambda):
        return Lambda(inThis.params, subst(this, withThis, inThis.body))
    
    raise NotImplementedError(f'Substitution not implemented for {type(inThis)}')
