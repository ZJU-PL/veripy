"""
Extended syntax definitions for veripy.

This module adds support for:
- Classes/OOP (class definitions, methods, fields)
- Sets (union, intersection, membership, cardinality)
- Dictionaries (maps with get, set, keys)
- Strings (concat, length, substring, index)
- List comprehensions (transformed to loops)
"""

from enum import Enum
from typing import List, Optional


class Op: pass

class ArithOps(Op, Enum):
    Add = '+'
    Minus = '-'
    Mult = '*'
    IntDiv = '/'
    Neg = '-'
    Mod = '%'

class CompOps(Op, Enum):
    Eq = '='
    Neq = '!='
    Lt = '<'
    Le = '<='
    Gt = '>'
    Ge = '>='
    In = 'in'
    NotIn = 'not in'

class BoolOps(Op, Enum):
    And = 'and'
    Or = 'or'
    Not = 'not'
    Implies = '==>'
    Iff = '<==>'

class SetOps(Op, Enum):
    """Set operations."""
    Union = 'union'
    Intersection = 'intersection'
    Difference = 'difference'
    Member = 'in'
    Subset = 'subset'
    Superset = 'superset'

class DictOps(Op, Enum):
    """Dictionary/map operations."""
    Get = 'get'
    Keys = 'keys'
    Values = 'values'
    Contains = 'contains'


class Value:
    __slots__ = ['v']
    def __init__(self, v):
        self.v = v
    
    def __eq__(self, other):
        return type(self) is type(other) and self.v == other.v
    
    def __hash__(self):
        return hash((type(self), self.v))

class VInt(Value):
    def __init__(self, v):
        super().__init__(int(v))
    
    def __str__(self):
        return f'VInt {self.v}'
    
    def __repr__(self):
        return f'VInt {self.v}'

class VBool(Value):
    def __init__(self, v):
        super().__init__(v == 'True' or v == True)
    
    def __str__(self):
        return f'VBool {self.v}'
    
    def __repr__(self):
        return f'VBool {self.v}'

class VString(Value):
    """String literal value."""
    def __init__(self, v):
        super().__init__(str(v))
    
    def __str__(self):
        return f'VString {self.v}'
    
    def __repr__(self):
        return f'VString {self.v}'

class VSet(Value):
    """Set literal value."""
    def __init__(self, elements=None):
        super().__init__(set(elements) if elements else set())
    
    def __str__(self):
        return f'VSet {self.v}'
    
    def __repr__(self):
        return f'VSet {self.v}'

class VDict(Value):
    """Dictionary literal value."""
    def __init__(self, pairs=None):
        super().__init__(dict(pairs) if pairs else {})
    
    def __str__(self):
        return f'VDict {self.v}'
    
    def __repr__(self):
        return f'VDict {self.v}'

class VList(Value):
    """List literal value."""
    def __init__(self, elements=None):
        super().__init__(list(elements) if elements else [])
    
    def __str__(self):
        return f'VList {self.v}'
    
    def __repr__(self):
        return f'VList {self.v}'


class Expr:
    """Base class for all expression AST nodes.
    
    We provide structural equality so unit tests can compare freshly
    constructed nodes (e.g. Literal(VInt(5))) by value rather than identity.
    """
    def __eq__(self, other):
        if type(self) is not type(other):
            return False
        # Most nodes are simple Python objects storing fields in __dict__.
        # (Value uses __slots__ and is handled separately above.)
        return getattr(self, '__dict__', None) == getattr(other, '__dict__', None)
    
    def __ne__(self, other):
        return not self.__eq__(other)

class Var(Expr):
    def __init__(self, name):
        self.name = name
    
    def __repr__(self):
        return f'(Var {self.name})'
    
    def variables(self):
        return {self.name}

class Literal(Expr):
    def __init__(self, v: Value):
        self.value = v
    
    def __repr__(self):
        return f'(Literal {self.value})'
    
    def variables(self):
        return set()

class BinOp(Expr):
    def __init__(self, l: Expr, op: Op, r: Expr):
        self.e1 = l
        self.e2 = r
        self.op = op
    
    def __repr__(self):
        return f'(BinOp {self.e1} {self.op} {self.e2})'
    
    def variables(self):
        return {*self.e1.variables(), *self.e2.variables()}

class UnOp(Expr):
    def __init__(self, op: Op, expr: Expr):
        self.op = op
        self.e = expr
    
    def __repr__(self):
        return f'(UnOp {self.op} {self.e})'
    
    def variables(self):
        return {*self.e.variables()}

class Quantification(Expr):
    def __init__(self, var: Var, ty, expr: Expr):
        self.var = var
        self.ty = ty
        self.expr = expr
    
    def __repr__(self):
        return f'(∀{self.var} : {self.ty}. {self.expr})'
    
    def variables(self):
        return {self.var.name, *self.expr.variables()}

class Subscript(Expr):
    def __init__(self, var, subscript):
        self.var = var
        self.subscript = subscript
    
    def __repr__(self):
        return f'(Subscript {self.var} [{self.subscript}])'
    
    def variables(self):
        return self.var.variables().union(self.subscript.variables())

class Slice(Expr):
    """Represents a slice expression: a[lower:upper:step]"""
    def __init__(self, lower=None, upper=None, step=None):
        self.lower = lower
        self.upper = upper
        self.step = step
    
    def __repr__(self):
        lower_str = str(self.lower) if self.lower else ''
        upper_str = str(self.upper) if self.upper else ''
        step_str = f':{self.step}' if self.step else ''
        return f'(Slice {lower_str}:{upper_str}{step_str})'
    
    def variables(self):
        result = set()
        if self.lower and isinstance(self.lower, Expr):
            result.update(self.lower.variables())
        if self.upper and isinstance(self.upper, Expr):
            result.update(self.upper.variables())
        if self.step and isinstance(self.step, Expr):
            result.update(self.step.variables())
        return result

class Store(Expr):
    def __init__(self, arr, idx, val):
        self.arr = arr
        self.idx = idx
        self.val = val
    
    def __repr__(self):
        return f'(Store {self.arr} [{self.idx}] = {self.val})'
    
    def variables(self):
        return self.arr.variables().union(self.idx.variables()).union(self.val.variables())

class FunctionCall(Expr):
    def __init__(self, func_name, args, native=True):
        self.func_name = func_name
        self.args = args
        self.native = native
    
    def __repr__(self):
        return f'(Call {self.func_name} with ({self.args}))'
    
    def variables(self):
        result = set()
        for arg in self.args:
            if isinstance(arg, Expr):
                result.update(arg.variables())
        return result

class Old(Expr):
    """Represents old(expr) for referring to pre-state values in postconditions"""
    def __init__(self, expr: Expr):
        self.expr = expr
    
    def __repr__(self):
        return f'(Old {self.expr})'
    
    def variables(self):
        return self.expr.variables()

class RecordField(Expr):
    """Represents a record/struct field access"""
    def __init__(self, record: Expr, field: str):
        self.record = record
        self.field = field
    
    def __repr__(self):
        return f'(RecordField {self.record}.{self.field})'
    
    def variables(self):
        return self.record.variables()


# ============================================================================
# OOP Support (Classes)
# ============================================================================

class FieldAccess(Expr):
    """Access to an object's field: obj.field"""
    def __init__(self, obj: Expr, field: str):
        self.obj = obj
        self.field = field
    
    def __repr__(self):
        return f'(FieldAccess {self.obj}.{self.field})'
    
    def variables(self):
        return self.obj.variables()

class FieldAssign(Expr):
    """Assignment to an object's field: obj.field = value"""
    def __init__(self, obj: Expr, field: str, value: Expr):
        self.obj = obj
        self.field = field
        self.value = value
    
    def __repr__(self):
        return f'(FieldAssign {self.obj}.{self.field} = {self.value})'
    
    def variables(self):
        return self.obj.variables().union(self.value.variables())


class ClassInvariant:
    """Class invariant assertion."""
    def __init__(self, class_name: str, expr: Expr):
        self.class_name = class_name
        self.expr = expr
    
    def __repr__(self):
        return f'(Invariant {self.class_name} :: {self.expr})'
    
    def variables(self):
        return self.expr.variables()


class MethodCall(Expr):
    """Method call on an object: obj.method(args)"""
    def __init__(self, obj: Expr, method_name: str, args: List[Expr]):
        self.obj = obj
        self.method_name = method_name
        self.args = args
    
    def __repr__(self):
        return f'(MethodCall {self.obj}.{self.method_name}({self.args}))'
    
    def variables(self):
        result = self.obj.variables()
        for arg in self.args:
            if isinstance(arg, Expr):
                result.update(arg.variables())
        return result


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
# String Support
# ============================================================================

class StringLiteral(Expr):
    """String literal."""
    def __init__(self, value: str):
        self.value = value
    
    def __repr__(self):
        return f'(StringLiteral "{self.value}")'
    
    def variables(self):
        return set()

class StringConcat(Expr):
    """String concatenation: s1 + s2"""
    def __init__(self, left: Expr, right: Expr):
        self.left = left
        self.right = right
    
    def __repr__(self):
        return f'(StringConcat {self.left} + {self.right})'
    
    def variables(self):
        return self.left.variables().union(self.right.variables())

class StringLength(Expr):
    """String length: len(s)"""
    def __init__(self, string_expr: Expr):
        self.string_expr = string_expr
    
    def __repr__(self):
        return f'(StringLength len({self.string_expr}))'
    
    def variables(self):
        return self.string_expr.variables()

class StringIndex(Expr):
    """String indexing: s[i]"""
    def __init__(self, string_expr: Expr, index: Expr):
        self.string_expr = string_expr
        self.index = index
    
    def __repr__(self):
        return f'(StringIndex {self.string_expr}[{self.index}])'
    
    def variables(self):
        return self.string_expr.variables().union(self.index.variables())

class StringSubstring(Expr):
    """String substring: s[i:j]"""
    def __init__(self, string_expr: Expr, start: Expr, end: Optional[Expr] = None):
        self.string_expr = string_expr
        self.start = start
        self.end = end
    
    def __repr__(self):
        end_str = f':{self.end}' if self.end else ''
        return f'(StringSubstring {self.string_expr}[{self.start}{end_str}])'
    
    def variables(self):
        result = self.string_expr.variables().union(self.start.variables())
        if self.end:
            result.update(self.end.variables())
        return result

class StringContains(Expr):
    """Check if substring in string: sub in s"""
    def __init__(self, substring: Expr, string_expr: Expr):
        self.substring = substring
        self.string_expr = string_expr
    
    def __repr__(self):
        return f'(StringContains {self.substring} in {self.string_expr})'
    
    def variables(self):
        return self.substring.variables().union(self.string_expr.variables())


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


# ============================================================================
# Statement Types
# ============================================================================

class Stmt:
    """Base class for all statement AST nodes (structural equality)."""
    def __eq__(self, other):
        if type(self) is not type(other):
            return False
        return getattr(self, '__dict__', None) == getattr(other, '__dict__', None)
    
    def __ne__(self, other):
        return not self.__eq__(other)

class Skip(Stmt):
    def __repr__(self):
        return '(Skip)'
    
    def variables(self):
        return set()

class Assign(Stmt):
    def __init__(self, var, expr):
        self.var = var
        self.expr = expr
    
    def __repr__(self):
        return f'(Assign {self.var} = {self.expr})'
    
    def variables(self):
        v = set(self.expr.variables())
        if isinstance(self.var, str):
            v.add(self.var)
        elif isinstance(self.var, Var):
            v.add(self.var.name)
        return v

class FieldAssignStmt(Stmt):
    """Assignment to object field."""
    def __init__(self, obj: Expr, field: str, value: Expr):
        self.obj = obj
        self.field = field
        self.value = value
    
    def __repr__(self):
        return f'(FieldAssign {self.obj}.{self.field} = {self.value})'
    
    def variables(self):
        return self.obj.variables().union(self.value.variables())

class If(Stmt):
    def __init__(self, cond_expr: Expr, lb_stmt: Stmt, rb_stmt: Stmt = None):
        self.cond = cond_expr
        self.lb = lb_stmt if lb_stmt is not None else Skip()
        self.rb = rb_stmt if rb_stmt is not None else Skip()
    
    def __repr__(self):
        return f'(If {self.cond} then {self.lb} else {self.rb})'
    
    def variables(self):
        return {*self.cond.variables(), *self.lb.variables(), *self.rb.variables()}

class Seq(Stmt):
    def __init__(self, s1: Stmt, s2: Stmt):
        self.s1 = s1 if s1 is not None else Skip()
        self.s2 = s2 if s2 is not None else Skip()
    
    def __repr__(self):
        return f'(Seq {self.s1}; {self.s2})'
    
    def variables(self):
        return {*self.s1.variables(), *self.s2.variables()}

class Assume(Stmt):
    def __init__(self, e: Expr):
        self.e = e
    
    def __repr__(self):
        return f'(Assume {self.e})'
    
    def variables(self):
        return {*self.e.variables()}

class Assert(Stmt):
    def __init__(self, e: Expr):
        self.e = e
    
    def __repr__(self):
        return f'(Assert {self.e})'
    
    def variables(self):
        return {*self.e.variables()}

class While(Stmt):
    def __init__(self, invs: List[Expr], cond: Expr, body: Stmt):
        self.cond = cond
        self.invariants = invs
        self.body = body if body is not None else Skip()
    
    def __repr__(self):
        return f'(While {self.cond} {{invs: {self.invariants}}} {self.body})'
    
    def variables(self):
        return {*self.body.variables()}

class Havoc(Stmt):
    def __init__(self, var):
        self.var = var
    
    def __repr__(self):
        return f'(Havoc {self.var})'
    
    def variables(self):
        return set()


# ============================================================================
# Class Definition (for verification metadata)
# ============================================================================

class ClassDef:
    """Class definition for verification."""
    def __init__(self, name: str, fields: List[tuple], 
                 invariants: List[Expr] = None,
                 methods: List['MethodDef'] = None):
        self.name = name
        self.fields = fields  # List of (field_name, type)
        self.invariants = invariants or []
        self.methods = methods or []
    
    def __repr__(self):
        return f'(ClassDef {self.name} fields={self.fields} invariants={self.invariants})'


class MethodDef:
    """Method definition for verification."""
    def __init__(self, class_name: str, name: str, 
                 params: List[tuple], 
                 requires: List[Expr] = None,
                 ensures: List[Expr] = None,
                 body: Stmt = None):
        self.class_name = class_name
        self.name = name
        self.params = params  # List of (param_name, type)
        self.requires = requires or []
        self.ensures = ensures or []
        self.body = body
    
    def __repr__(self):
        return f'(MethodDef {self.class_name}.{self.name}({self.params}))'


# ============================================================================
# Additional Statement Types (Extended Python Features)
# ============================================================================

class Try(Stmt):
    """Try/except/finally statement for exception handling."""
    def __init__(self, body: Stmt, handlers: List['ExceptHandler'], 
                 orelse: Stmt = None, finalbody: Stmt = None):
        self.body = body
        self.handlers = handlers  # List of (exception_type, var_name, handler_body)
        self.orelse = orelse  # else clause
        self.finalbody = finalbody  # finally clause
    
    def __repr__(self):
        handlers_str = ', '.join(str(h) for h in self.handlers)
        return f'(Try body={self.body} handlers=[{handlers_str}] orelse={self.orelse} finalbody={self.finalbody})'
    
    def variables(self):
        result = self.body.variables()
        for handler in self.handlers:
            result.update(handler.body.variables())
        if self.orelse:
            result.update(self.orelse.variables())
        if self.finalbody:
            result.update(self.finalbody.variables())
        return result


class ExceptHandler:
    """Exception handler in try statement."""
    def __init__(self, exc_type: str, exc_var: str = None, body: Stmt = None):
        self.exc_type = exc_type  # Exception type name
        self.exc_var = exc_var  # Optional exception variable name
        self.body = body  # Handler body
    
    def __repr__(self):
        var_str = f' as {self.exc_var}' if self.exc_var else ''
        return f'(ExceptHandler {self.exc_type}{var_str} body={self.body})'


class With(Stmt):
    """With statement for context management."""
    def __init__(self, context_expr: Expr, item_var: str, body: Stmt):
        self.context_expr = context_expr
        self.item_var = item_var  # Variable bound to context manager result
        self.body = body
    
    def __repr__(self):
        return f'(With {self.item_var} = {self.context_expr} body={self.body})'
    
    def variables(self):
        return self.body.variables()


class ForLoop(Stmt):
    """For loop statement."""
    def __init__(self, loop_var: str, iterable: Expr, body: Stmt, 
                 orelse: Stmt = None):
        self.loop_var = loop_var
        self.iterable = iterable
        self.body = body
        self.orelse = orelse  # Optional else clause
    
    def __repr__(self):
        return f'(For {self.loop_var} in {self.iterable} body={self.body} orelse={self.orelse})'
    
    def variables(self):
        result = self.body.variables()
        if self.orelse:
            result.update(self.orelse.variables())
        result.add(self.loop_var)
        return result


class AugAssign(Stmt):
    """Augmented assignment (e.g., x += 1)."""
    def __init__(self, var: Expr, op: ArithOps, expr: Expr):
        self.var = var
        self.op = op
        self.expr = expr
    
    def __repr__(self):
        return f'(AugAssign {self.var} {self.op}= {self.expr})'
    
    def variables(self):
        return self.var.variables().union(self.expr.variables())


class Break(Stmt):
    """Break statement for loop termination."""
    def __repr__(self):
        return '(Break)'
    
    def variables(self):
        return set()


class Continue(Stmt):
    """Continue statement for loop iteration."""
    def __repr__(self):
        return '(Continue)'
    
    def variables(self):
        return set()


class Raise(Stmt):
    """Raise statement for exception throwing."""
    def __init__(self, exc_expr: Expr = None, cause: Expr = None):
        self.exc_expr = exc_expr  # Exception to raise
        self.cause = cause  # Optional cause
    
    def __repr__(self):
        if self.cause:
            return f'(Raise {self.exc_expr} from {self.cause})'
        return f'(Raise {self.exc_expr})'
    
    def variables(self):
        result = set()
        if self.exc_expr:
            result.update(self.exc_expr.variables())
        if self.cause:
            result.update(self.cause.variables())
        return result


class Global(Stmt):
    """Global variable declaration."""
    def __init__(self, names: List[str]):
        self.names = names
    
    def __repr__(self):
        return f'(Global {self.names})'
    
    def variables(self):
        return set(self.names)


class Nonlocal(Stmt):
    """Nonlocal variable declaration."""
    def __init__(self, names: List[str]):
        self.names = names
    
    def __repr__(self):
        return f'(Nonlocal {self.names})'
    
    def variables(self):
        return set(self.names)


class ImportStmt(Stmt):
    """Import statement."""
    def __init__(self, module: str, names: List[str] = None, alias: str = None):
        self.module = module  # Module to import
        self.names = names or []  # Specific names to import (None means import *)
        self.alias = alias  # Optional alias for the module
    
    def __repr__(self):
        if self.alias:
            return f'(Import {self.module} as {self.alias})'
        if self.names:
            return f'(Import {self.module}.{{{", ".join(self.names)}}})'
        return f'(Import {self.module})'
    
    def variables(self):
        return set()


class ImportFrom(Stmt):
    """From...import statement."""
    def __init__(self, module: str, names: List[str], alias: List[str] = None):
        self.module = module  # Module to import from
        self.names = names  # Names to import
        self.alias = alias or []  # Optional aliases
    
    def __repr__(self):
        result = f'(From {self.module} Import '
        if self.alias:
            pairs = [f'{n} as {a}' for n, a in zip(self.names, self.alias)]
            result += ', '.join(pairs)
        else:
            result += ', '.join(self.names)
        return result + ')'
    
    def variables(self):
        return set()


class Lambda(Expr):
    """Lambda expression."""
    def __init__(self, params: List[tuple], body: Expr):
        self.params = params  # List of (param_name, type)
        self.body = body
    
    def __repr__(self):
        params_str = ', '.join(p for p, _ in self.params)
        return f'(Lambda ({params_str}) => {self.body})'
    
    def variables(self):
        param_names = {name for name, _ in self.params}
        body_vars = self.body.variables()
        return body_vars - param_names


class Yield(Expr):
    """Yield expression for generators."""
    def __init__(self, value: Expr = None):
        self.value = value  # Value to yield (None for yield without value)
    
    def __repr__(self):
        if self.value:
            return f'(Yield {self.value})'
        return '(Yield)'
    
    def variables(self):
        return self.value.variables() if self.value else set()


class YieldFrom(Expr):
    """Yield from expression for generator delegation."""
    def __init__(self, iterable: Expr):
        self.iterable = iterable
    
    def __repr__(self):
        return f'(YieldFrom {self.iterable})'
    
    def variables(self):
        return self.iterable.variables()


class Await(Expr):
    """Await expression for async/await."""
    def __init__(self, value: Expr):
        self.value = value
    
    def __repr__(self):
        return f'(Await {self.value})'
    
    def variables(self):
        return self.value.variables()


class AsyncFunctionDef(Stmt):
    """Async function definition."""
    def __init__(self, name: str, params: List[tuple], 
                 requires: List[Expr] = None,
                 ensures: List[Expr] = None,
                 body: Stmt = None,
                 returns: 'Type' = None):
        self.name = name
        self.params = params
        self.requires = requires or []
        self.ensures = ensures or []
        self.body = body
        self.returns = returns
    
    def __repr__(self):
        return f'(AsyncFunctionDef {self.name}({self.params}) body={self.body})'
    
    def variables(self):
        return self.body.variables() if self.body else set()


class AsyncFor(Stmt):
    """Async for loop."""
    def __init__(self, loop_var: str, iterable: Expr, body: Stmt, 
                 orelse: Stmt = None):
        self.loop_var = loop_var
        self.iterable = iterable
        self.body = body
        self.orelse = orelse
    
    def __repr__(self):
        return f'(AsyncFor {self.loop_var} in {self.iterable} body={self.body})'
    
    def variables(self):
        result = self.body.variables()
        if self.orelse:
            result.update(self.orelse.variables())
        result.add(self.loop_var)
        return result


class AsyncWith(Stmt):
    """Async with statement."""
    def __init__(self, context_expr: Expr, item_var: str, body: Stmt):
        self.context_expr = context_expr
        self.item_var = item_var
        self.body = body
    
    def __repr__(self):
        return f'(AsyncWith {self.item_var} = {self.context_expr} body={self.body})'
    
    def variables(self):
        return self.body.variables()


class Match(Stmt):
    """Match statement (Python 3.10+)."""
    def __init__(self, subject: Expr, cases: List['MatchCase']):
        self.subject = subject
        self.cases = cases  # List of MatchCase
    
    def __repr__(self):
        cases_str = ', '.join(str(c) for c in self.cases)
        return f'(Match {self.subject} cases=[{cases_str}])'
    
    def variables(self):
        result = self.subject.variables()
        for case in self.cases:
            result.update(case.body.variables())
        return result


class MatchCase:
    """Single case in match statement."""
    def __init__(self, pattern: 'Pattern', guard: Expr = None, body: Stmt = None):
        self.pattern = pattern
        self.guard = guard  # Optional guard expression
        self.body = body  # Case body
    
    def __repr__(self):
        guard_str = f' if {self.guard}' if self.guard else ''
        return f'(Case {self.pattern}{guard_str} => {self.body})'


class Pattern:
    """Base class for match patterns."""
    pass


class PatternConstant(Pattern):
    """Constant pattern (literals)."""
    def __init__(self, value: Expr):
        self.value = value
    
    def __repr__(self):
        return f'(PatternConstant {self.value})'


class PatternCapture(Pattern):
    """Capture pattern (variable binding)."""
    def __init__(self, name: str):
        self.name = name
    
    def __repr__(self):
        return f'(PatternCapture {self.name})'


class PatternSequence(Pattern):
    """Sequence pattern (tuple/list)."""
    def __init__(self, patterns: List[Pattern]):
        self.patterns = patterns
    
    def __repr__(self):
        return f'(PatternSequence [{", ".join(str(p) for p in self.patterns)}])'


class PatternMapping(Pattern):
    """Mapping pattern (dict)."""
    def __init__(self, keys: List[Expr], patterns: List[Pattern], rest: str = None):
        self.keys = keys
        self.patterns = patterns
        self.rest = rest  # Optional **rest binding
    
    def __repr__(self):
        pairs = [f'{k}: {p}' for k, p in zip(self.keys, self.patterns)]
        if self.rest:
            pairs.append(f'**{self.rest}')
        return f'(PatternMapping {{{", ".join(pairs)}}})'


class PatternClass(Pattern):
    """Class pattern (object matching)."""
    def __init__(self, class_name: str, patterns: List[Pattern]):
        self.class_name = class_name
        self.patterns = patterns
    
    def __repr__(self):
        return f'(PatternClass {self.class_name}({", ".join(str(p) for p in self.patterns)}))'


class PatternLiteral(Pattern):
    """Literal pattern (constants)."""
    def __init__(self, value):
        self.value = value
    
    def __repr__(self):
        return f'(PatternLiteral {self.value})'


class PatternAs(Pattern):
    """As pattern (alias)."""
    def __init__(self, pattern: Pattern, name: str):
        self.pattern = pattern
        self.name = name
    
    def __repr__(self):
        return f'(PatternAs {self.pattern} as {self.name})'


class PatternOr(Pattern):
    """Or pattern (alternative)."""
    def __init__(self, patterns: List[Pattern]):
        self.patterns = patterns
    
    def __repr__(self):
        return f'(PatternOr {" | ".join(str(p) for p in self.patterns)})'


class Walrus(Expr):
    """Named expression (walrus operator :=)."""
    def __init__(self, name: str, value: Expr):
        self.name = name
        self.value = value
    
    def __repr__(self):
        return f'({self.name} := {self.value})'
    
    def variables(self):
        result = self.value.variables()
        result.add(self.name)
        return result


# ============================================================================
# Advanced Python Features (v0.2.0+)
# ============================================================================

class Property(Expr):
    """Property decorator expression for getter/setter."""
    def __init__(self, name: str, getter: bool = True, setter: bool = False):
        self.name = name
        self.is_getter = getter
        self.is_setter = setter
    
    def __repr__(self):
        if self.is_setter:
            return f'(Property {self.name}.setter)'
        return f'(Property {self.name})'
    
    def variables(self):
        return set()


class StaticMethod(Expr):
    """Static method decorator."""
    def __init__(self, func_name: str):
        self.func_name = func_name
    
    def __repr__(self):
        return f'(StaticMethod {self.func_name})'
    
    def variables(self):
        return set()


class ClassMethod(Expr):
    """Class method decorator."""
    def __init__(self, func_name: str):
        self.func_name = func_name
    
    def __repr__(self):
        return f'(ClassMethod {self.func_name})'
    
    def variables(self):
        return set()


class VarArgs(Expr):
    """Variable positional arguments (*args)."""
    def __init__(self, name: str):
        self.name = name
    
    def __repr__(self):
        return f'(VarArgs {self.name})'
    
    def variables(self):
        return {self.name}


class KwArgs(Expr):
    """Variable keyword arguments (**kwargs)."""
    def __init__(self, name: str):
        self.name = name
    
    def __repr__(self):
        return f'(KwArgs {self.name})'
    
    def variables(self):
        return {self.name}


class FString(Expr):
    """F-string expression (Python 3.6+)."""
    def __init__(self, parts: List[Expr], literal_parts: List[str]):
        self.parts = parts  # Expressions inside {}
        self.literal_parts = literal_parts  # Literal string parts
    
    def __repr__(self):
        return f'(FString {self.literal_parts} with {self.parts})'
    
    def variables(self):
        result = set()
        for part in self.parts:
            result.update(part.variables())
        return result


class Decorator(Expr):
    """Decorator expression."""
    def __init__(self, name: str, args: List[Expr] = None):
        self.name = name
        self.args = args or []  # Decorator arguments
    
    def __repr__(self):
        if self.args:
            args_str = ', '.join(str(a) for a in self.args)
            return f'(@{self.name}({args_str}))'
        return f'(@{self.name})'
    
    def variables(self):
        result = set()
        for arg in self.args:
            result.update(arg.variables())
        return result


class DecoratorChain(Expr):
    """Decorator chain (multiple decorators)."""
    def __init__(self, decorators: List[Decorator]):
        self.decorators = decorators
    
    def __repr__(self):
        dec_str = '\n'.join(str(d) for d in self.decorators)
        return f'(DecoratorChain\n{dec_str})'
    
    def variables(self):
        result = set()
        for dec in self.decorators:
            result.update(dec.variables())
        return result


class DataClass(Expr):
    """Data class decorator (@dataclass)."""
    def __init__(self, name: str, fields: List[tuple] = None, 
                 init: bool = True, repr: bool = True, eq: bool = True):
        self.name = name
        self.fields = fields or []  # (field_name, type, default)
        self.init = init
        self.repr = repr
        self.eq = eq
    
    def __repr__(self):
        fields_str = ', '.join(f'{name}: {ty}' for name, ty, _ in self.fields)
        return f'(DataClass {name} fields=[{fields_str}])'
    
    def variables(self):
        return set()


class TypeAlias(Expr):
    """Type alias definition."""
    def __init__(self, name: str, target: 'Type'):
        self.name = name
        self.target = target
    
    def __repr__(self):
        return f'(TypeAlias {self.name} = {self.target})'
    
    def variables(self):
        return set()


class Protocol(Expr):
    """Protocol definition (structural subtyping)."""
    def __init__(self, name: str, methods: List['MethodSignature'] = None,
                 attributes: List[tuple] = None):
        self.name = name
        self.methods = methods or []  # Method signatures
        self.attributes = attributes or []  # Attribute signatures
    
    def __repr__(self):
        return f'(Protocol {self.name})'
    
    def variables(self):
        return set()


class MethodSignature(Expr):
    """Method signature in protocol."""
    def __init__(self, name: str, params: List[tuple], returns: 'Type' = None):
        self.name = name
        self.params = params
        self.returns = returns
    
    def __repr__(self):
        return f'(MethodSignature {self.name})'
    
    def variables(self):
        return set()


class Iterator(Expr):
    """Iterator protocol (__iter__, __next__)."""
    def __init__(self, source: Expr):
        self.source = source  # Iterable source
    
    def __repr__(self):
        return f'(Iterator {self.source})'
    
    def variables(self):
        return self.source.variables()


class Range(Expr):
    """Range expression (for iteration)."""
    def __init__(self, start: Expr = None, stop: Expr = None, step: Expr = None):
        self.start = start or Literal(VInt(0))
        self.stop = stop
        self.step = step or Literal(VInt(1))
    
    def __repr__(self):
        if self.step.variables() == {Literal(VInt(1)).variables()}:
            return f'(Range {self.start}..{self.stop})'
        return f'(Range {self.start}..{self.stop}..{self.step})'
    
    def variables(self):
        result = self.start.variables()
        if self.stop:
            result.update(self.stop.variables())
        result.update(self.step.variables())
        return result


class Enumerate(Expr):
    """Enumerate expression (index, value pairs)."""
    def __init__(self, iterable: Expr, start: Expr = None):
        self.iterable = iterable
        self.start = start or Literal(VInt(0))
    
    def __repr__(self):
        return f'(Enumerate {self.iterable})'
    
    def variables(self):
        result = self.iterable.variables()
        result.update(self.start.variables())
        return result


class Zip(Expr):
    """Zip expression (multiple iterables)."""
    def __init__(self, iterables: List[Expr]):
        self.iterables = iterables
    
    def __repr__(self):
        return f'(Zip {self.iterables})'
    
    def variables(self):
        result = set()
        for it in self.iterables:
            result.update(it.variables())
        return result


class Map(Expr):
    """Map expression (function application)."""
    def __init__(self, func: Expr, iterable: Expr):
        self.func = func
        self.iterable = iterable
    
    def __repr__(self):
        return f'(Map {self.func} {self.iterable})'
    
    def variables(self):
        result = self.func.variables()
        result.update(self.iterable.variables())
        return result


class Filter(Expr):
    """Filter expression (conditional selection)."""
    def __init__(self, predicate: Expr, iterable: Expr):
        self.predicate = predicate
        self.iterable = iterable
    
    def __repr__(self):
        return f'(Filter {self.predicate} {self.iterable})'
    
    def variables(self):
        result = self.predicate.variables()
        result.update(self.iterable.variables())
        return result


class Reduce(Expr):
    """Reduce expression (fold operation)."""
    def __init__(self, func: Expr, iterable: Expr, initial: Expr = None):
        self.func = func
        self.iterable = iterable
        self.initial = initial
    
    def __repr__(self):
        return f'(Reduce {self.func} {self.iterable})'
    
    def variables(self):
        result = self.func.variables()
        result.update(self.iterable.variables())
        if self.initial:
            result.update(self.initial.variables())
        return result


class Comprehension(Expr):
    """Generic comprehension expression."""
    def __init__(self, kind: str, element: Expr, generators: List['Generator']):
        self.kind = kind  # 'list', 'set', 'dict', 'generator'
        self.element = element
        self.generators = generators
    
    def __repr__(self):
        return f'({self.kind} comprehension: {self.element} for {self.generators})'
    
    def variables(self):
        result = self.element.variables()
        for gen in self.generators:
            result.update(gen.iterable.variables())
            result.discard(gen.target.name)
            if gen.predicate:
                result.update(gen.predicate.variables())
        return result


class Generator(Expr):
    """Generator clause in comprehension."""
    def __init__(self, target: Var, iterable: Expr, predicate: Expr = None):
        self.target = target  # Loop variable
        self.iterable = iterable
        self.predicate = predicate  # Optional if condition
    
    def __repr__(self):
        if self.predicate:
            return f'(Generator {self.target} in {self.iterable} if {self.predicate})'
        return f'(Generator {self.target} in {self.iterable})'
    
    def variables(self):
        result = self.iterable.variables()
        if self.predicate:
            result.update(self.predicate.variables())
        result.discard(self.target.name)
        return result


class TypeVar(Expr):
    """Type variable for generics."""
    def __init__(self, name: str, bound: 'Type' = None, covariant: bool = False,
                 contravariant: bool = False):
        self.name = name
        self.bound = bound
        self.covariant = covariant
        self.contravariant = contravariant
    
    def __repr__(self):
        return f'(TypeVar {self.name})'
    
    def variables(self):
        return set()


class UnionType(Expr):
    """Union type (X | Y | Z)."""
    def __init__(self, types: List['Type']):
        self.types = types
    
    def __repr__(self):
        return f'({" | ".join(str(t) for t in self.types)})'
    
    def variables(self):
        return set()


class OptionalType(Expr):
    """Optional type (X | None)."""
    def __init__(self, type_expr: 'Type'):
        self.type_expr = type_expr
    
    def __repr__(self):
        return f'(Optional {self.type_expr})'
    
    def variables(self):
        return set()


class LiteralType(Expr):
    """Literal type (e.g., Literal[1, "a", True])."""
    def __init__(self, values: List[Expr]):
        self.values = values
    
    def __repr__(self):
        return f'(Literal [{" ".join(str(v) for v in self.values)}])'
    
    def variables(self):
        result = set()
        for v in self.values:
            result.update(v.variables())
        return result


class Final(Expr):
    """Final constant qualifier."""
    def __init__(self, name: str, value: Expr):
        self.name = name
        self.value = value
    
    def __repr__(self):
        return f'(Final {self.name} = {self.value})'
    
    def variables(self):
        return self.value.variables()


class TypeGuard(Expr):
    """Type guard assertion."""
    def __init__(self, expr: Expr, target_type: 'Type'):
        self.expr = expr
        self.target_type = target_type
    
    def __repr__(self):
        return f'(TypeGuard {self.expr} is {self.target_type})'
    
    def variables(self):
        return self.expr.variables()


# Type hints for forward references
from typing import TYPE_CHECKING
if TYPE_CHECKING:
    from veripy.typecheck.types import Type
