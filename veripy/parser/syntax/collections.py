"""Collection types (sets, dictionaries, lists) for veripy syntax."""

from typing import List, Optional
from .expressions import Expr, Var
from .operations import SetOps


# ============================================================================
# Set Support
# ============================================================================

class SetLiteral(Expr):
    """Set literal: {1, 2, 3}"""
    def __init__(self, elements: List[Expr]):
        self.elements = elements
    
    def __repr__(self):
        return f'(SetLiteral {{{self.elements}}})'
    
    def variables(self):
        result = set()
        for elem in self.elements:
            if isinstance(elem, Expr):
                result.update(elem.variables())
        return result


class SetOp(Expr):
    """Set operation: union, intersection, difference, subset, etc."""
    def __init__(self, left: Expr, op: SetOps, right: Expr):
        self.left = left
        self.op = op
        self.right = right
    
    def __repr__(self):
        return f'(SetOp {self.left} {self.op.value} {self.right})'
    
    def variables(self):
        return self.left.variables().union(self.right.variables())


class SetCardinality(Expr):
    """Cardinality of a set: |s|"""
    def __init__(self, set_expr: Expr):
        self.set_expr = set_expr
    
    def __repr__(self):
        return f'(Cardinality {self.set_expr})'
    
    def variables(self):
        return self.set_expr.variables()


class SetComprehension(Expr):
    """Set comprehension: {x | x in range(n) if x > 0}"""
    def __init__(self, element_var: Var, source: Expr, predicate: Optional[Expr] = None):
        self.element_var = element_var
        self.source = source
        self.predicate = predicate
    
    def __repr__(self):
        pred_str = f' | {self.predicate}' if self.predicate else ''
        return f'(SetComprehension {{{self.element_var} | {self.source}{pred_str}}})'
    
    def variables(self):
        result = self.source.variables()
        if self.predicate:
            result.update(self.predicate.variables())
        result.discard(self.element_var.name)
        return result


# ============================================================================
# Dictionary/Map Support
# ============================================================================

class DictLiteral(Expr):
    """Dictionary literal: {'a': 1, 'b': 2}"""
    def __init__(self, keys: List[Expr], values: List[Expr]):
        self.keys = keys
        self.values = values
    
    def __repr__(self):
        pairs = [f'{k}: {v}' for k, v in zip(self.keys, self.values)]
        return f'(DictLiteral {{{", ".join(pairs)}}})'
    
    def variables(self):
        result = set()
        for k in self.keys:
            if isinstance(k, Expr):
                result.update(k.variables())
        for v in self.values:
            if isinstance(v, Expr):
                result.update(v.variables())
        return result


class DictComprehension(Expr):
    """Dictionary comprehension: {k: v for x in iter if cond}"""
    def __init__(self, key_expr: Expr, value_expr: Expr, element_var: Var,
                 iterable: Expr, predicate: Optional[Expr] = None):
        self.key_expr = key_expr
        self.value_expr = value_expr
        self.element_var = element_var
        self.iterable = iterable
        self.predicate = predicate

    def __repr__(self):
        pred_str = f' if {self.predicate}' if self.predicate else ''
        return f'(DictComprehension {{{self.key_expr}: {self.value_expr} for {self.element_var} in {self.iterable}{pred_str}}})'

    def variables(self):
        result = self.key_expr.variables().union(self.value_expr.variables())
        result.update(self.iterable.variables())
        if self.predicate:
            result.update(self.predicate.variables())
        result.discard(self.element_var.name)
        return result


class DictGet(Expr):
    """Get value from dict: d[key]"""
    def __init__(self, dict_expr: Expr, key: Expr, default: Optional[Expr] = None):
        self.dict_expr = dict_expr
        self.key = key
        self.default = default
    
    def __repr__(self):
        default_str = f', default={self.default}' if self.default else ''
        return f'(DictGet {self.dict_expr}[{self.key}]{default_str})'
    
    def variables(self):
        result = self.dict_expr.variables().union(self.key.variables())
        if self.default:
            result.update(self.default.variables())
        return result


class DictSet(Expr):
    """Create new dict with key set: d[key] = value (returns new dict)"""
    def __init__(self, dict_expr: Expr, key: Expr, value: Expr):
        self.dict_expr = dict_expr
        self.key = key
        self.value = value
    
    def __repr__(self):
        return f'(DictSet {self.dict_expr}[{self.key}] = {self.value})'
    
    def variables(self):
        return self.dict_expr.variables().union(self.key.variables()).union(self.value.variables())


class DictKeys(Expr):
    """Get keys of dict: keys(d)"""
    def __init__(self, dict_expr: Expr):
        self.dict_expr = dict_expr
    
    def __repr__(self):
        return f'(DictKeys {self.dict_expr})'
    
    def variables(self):
        return self.dict_expr.variables()


class DictValues(Expr):
    """Get values of dict: values(d)"""
    def __init__(self, dict_expr: Expr):
        self.dict_expr = dict_expr
    
    def __repr__(self):
        return f'(DictValues {self.dict_expr})'
    
    def variables(self):
        return self.dict_expr.variables()


class DictContains(Expr):
    """Check if key in dict: key in d"""
    def __init__(self, dict_expr: Expr, key: Expr):
        self.dict_expr = dict_expr
        self.key = key
    
    def __repr__(self):
        return f'(DictContains {self.key} in {self.dict_expr})'
    
    def variables(self):
        return self.dict_expr.variables().union(self.key.variables())


# ============================================================================
# List Comprehension Support
# ============================================================================

class ListComprehension(Expr):
    """List comprehension: [expr for x in iterable if cond]"""
    def __init__(self, element_expr: Expr, element_var: Var, 
                 iterable: Expr, predicate: Optional[Expr] = None):
        self.element_expr = element_expr
        self.element_var = element_var
        self.iterable = iterable
        self.predicate = predicate
    
    def __repr__(self):
        pred_str = f' if {self.predicate}' if self.predicate else ''
        return f'(ListComprehension [{self.element_expr} for {self.element_var} in {self.iterable}{pred_str}])'
    
    def variables(self):
        result = self.element_expr.variables()
        result.update(self.iterable.variables())
        if self.predicate:
            result.update(self.predicate.variables())
        result.discard(self.element_var.name)
        return result
