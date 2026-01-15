"""
Extended transformer for veripy.

This module adds support for:
- Classes/OOP (field access, method calls)
- Sets (union, intersection, membership, cardinality)
- Dictionaries (get, set, keys, values)
- Strings (concat, length, substring, index)
- List comprehensions (transformed to loops)
"""

import ast
import z3
from veripy.parser.syntax import *
from veripy.parser.parser import parse_assertion
from veripy.built_ins import BUILT_INS, FUNCTIONS
from veripy.typecheck.types import *
from functools import reduce
from typing import List, Dict, Set
import re


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
        if this != inThis.var.name:
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
    
    raise NotImplementedError(f'Substitution not implemented for {type(inThis)}')


class ExprTranslator:
    """Translator that converts Python AST to veripy AST."""

    def __init__(self):
        # Fresh names for list-literal base arrays so different literals do not alias.
        self._list_lit_idx = 0

    def _fresh_list_base(self) -> Var:
        self._list_lit_idx += 1
        return Var(f'__list_lit_base{self._list_lit_idx}')
    
    def fold_binops(self, op: Op, values: List[Expr]) -> Expr:
        result = BinOp(self.visit(values[0]), op, self.visit(values[1]))
        for e in values[2:]:
            result = BinOp(result, op, self.visit(e))
        return result
    
    def visit_Name(self, node):
        return Var(node.id)
    
    def visit_Num(self, node):
        return Literal(VInt(node.n))
    
    def visit_NameConstant(self, node):
        return Literal(VBool(node.value))
    
    def visit_Constant(self, node):
        """Handle Python 3.8+ Constant nodes."""
        if isinstance(node.value, bool):
            return Literal(VBool(node.value))
        elif isinstance(node.value, int):
            return Literal(VInt(node.value))
        elif isinstance(node.value, str):
            return StringLiteral(node.value)
        elif node.value is None:
            # Represent None as a symbolic variable to keep translation simple
            return Var('None')
        else:
            raise Exception(f'Unsupported constant: {node.value}')
    
    def visit_Str(self, node):
        """Handle string literals (Python 3.7 and earlier)."""
        return StringLiteral(node.s)
    
    def visit_Expr(self, node):
        return self.visit(node.value)
    
    def visit_BoolOp(self, node):
        op = {
            ast.And: BoolOps.And,
            ast.Or: BoolOps.Or,
        }.get(type(node.op))
        return self.fold_binops(op, node.values)
    
    def visit_Compare(self, node):
        lv = self.visit(node.left)
        rv = self.visit(node.comparators[0])
        op = node.ops[0]
        
        op_map = {
            ast.Lt: lambda: BinOp(lv, CompOps.Lt, rv),
            ast.LtE: lambda: BinOp(lv, CompOps.Le, rv),
            ast.Gt: lambda: BinOp(lv, CompOps.Gt, rv),
            ast.GtE: lambda: BinOp(lv, CompOps.Ge, rv),
            ast.Eq: lambda: BinOp(lv, CompOps.Eq, rv),
            ast.NotEq: lambda: BinOp(lv, CompOps.Neq, rv),
            ast.In: lambda: BinOp(lv, CompOps.In, rv),
        }
        return op_map.get(type(op), lambda: raise_exception(f'Not Supported: {op}'))()
    
    def visit_BinOp(self, node):
        lv = self.visit(node.left)
        rv = self.visit(node.right)
        
        op_map = {
            ast.Add: lambda: BinOp(lv, ArithOps.Add, rv),
            ast.Sub: lambda: BinOp(lv, ArithOps.Minus, rv),
            ast.Mult: lambda: BinOp(lv, ArithOps.Mult, rv),
            ast.Div: lambda: BinOp(lv, ArithOps.IntDiv, rv),
            ast.Mod: lambda: BinOp(lv, ArithOps.Mod, rv),
            ast.BitOr: lambda: BinOp(lv, BoolOps.Or, rv),  # used for union types
        }
        return op_map.get(type(node.op), lambda: raise_exception(f'Not Supported: {node.op}'))()
    
    def visit_UnaryOp(self, node):
        v = self.visit(node.operand)
        op_map = {
            ast.USub: lambda: UnOp(ArithOps.Neg, v),
            ast.Not: lambda: UnOp(BoolOps.Not, v),
        }
        return op_map.get(type(node.op), lambda: raise_exception(f'Not Supported {node.op}'))()
    
    def visit_Index(self, node):
        return self.visit(node.value)
    
    def visit_Call(self, node):
        # Support Name and Attribute (e.g., vp.invariant)
        if isinstance(node.func, ast.Name):
            func = node.func.id
        elif isinstance(node.func, ast.Attribute):
            func = node.func.attr
        else:
            func = None
        
        if func in BUILT_INS:
            if func == 'assume':
                return Assume(parse_assertion(node.args[0].s if hasattr(node.args[0], 's') else str(node.args[0].s)))
            if func == 'invariant':
                return parse_assertion(node.args[0].s if hasattr(node.args[0], 's') else str(node.args[0].s))
        
        if func is None:
            raise_exception(f'Unsupported call func: {ast.dump(node.func)}')
        
        # Advanced built-ins mapping
        if func == 'range':
            args = [self.visit(arg) for arg in node.args]
            if len(args) == 1:
                return Range(stop=args[0])
            if len(args) == 2:
                return Range(start=args[0], stop=args[1])
            if len(args) == 3:
                return Range(start=args[0], stop=args[1], step=args[2])
        if func == 'enumerate':
            args = [self.visit(arg) for arg in node.args]
            iterable = args[0] if args else Literal(VInt(0))
            start = args[1] if len(args) > 1 else None
            return Enumerate(iterable, start)
        if func == 'zip':
            args = [self.visit(arg) for arg in node.args]
            return Zip(args)
        if func == 'map':
            args = [self.visit(arg) for arg in node.args]
            if len(args) >= 2:
                return Map(args[0], args[1])
        if func == 'filter':
            args = [self.visit(arg) for arg in node.args]
            if len(args) >= 2:
                return Filter(args[0], args[1])
        if func == 'reduce':
            args = [self.visit(arg) for arg in node.args]
            initial = args[2] if len(args) > 2 else None
            if len(args) >= 2:
                return Reduce(args[0], args[1], initial)

        # Handle method calls (obj.method(args))
        if isinstance(node.func, ast.Attribute):
            obj = self.visit(node.func.value)
            method_name = node.func.attr
            args = [self.visit(arg) for arg in node.args]
            return MethodCall(obj, method_name, args)
        
        # Handle regular function calls
        args = [self.visit(arg) for arg in node.args]
        return FunctionCall(Var(func), args)
    
    def visit_Subscript(self, node):
        v = self.visit(node.value)
        # Handle Literal[...] specially
        if isinstance(node.value, ast.Name) and node.value.id == 'Literal':
            if isinstance(node.slice, ast.Tuple):
                values = [self.visit(elt) for elt in node.slice.elts]
            else:
                values = [self.visit(node.slice)]
            return LiteralType(values)
        # Generic slice handling
        if isinstance(node.slice, ast.Tuple):
            s = [self.visit(elt) for elt in node.slice.elts]
        else:
            s = self.visit(node.slice)
        return Subscript(v, s)
    
    def visit_Attribute(self, node):
        """Handle attribute access: obj.field"""
        value = self.visit(node.value)
        return FieldAccess(value, node.attr)
    
    def visit_ListComp(self, node):
        """Handle list comprehensions: [expr for x in iter if cond]"""
        if len(node.generators) != 1:
            raise_exception('Only single-generator comprehensions supported')
        
        gen = node.generators[0]
        element_var = Var(gen.target.id)
        iterable = self.visit(gen.iter)
        
        element_expr = self.visit(node.elt)
        
        # Combine all if conditions
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            if predicate is None:
                predicate = cond
            else:
                predicate = BinOp(predicate, BoolOps.And, cond)
        
        return ListComprehension(element_expr, element_var, iterable, predicate)
    
    def visit_SetComp(self, node):
        """Handle set comprehensions: {expr for x in iter if cond}"""
        if len(node.generators) != 1:
            raise_exception('Only single-generator comprehensions supported')
        
        gen = node.generators[0]
        element_var = Var(gen.target.id)
        iterable = self.visit(gen.iter)
        
        element_expr = self.visit(node.elt)
        
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            if predicate is None:
                predicate = cond
            else:
                predicate = BinOp(predicate, BoolOps.And, cond)
        
        # Convert set comprehension to set literal via comprehension
        # For Z3, we'll use a set comprehension expression
        return SetComprehension(element_var, iterable, predicate)
    
    def visit_DictComp(self, node):
        """Handle dict comprehensions: {k: v for x in iter if cond}"""
        if len(node.generators) != 1:
            raise_exception('Only single-generator comprehensions supported')
        
        gen = node.generators[0]
        element_var = Var(gen.target.id)
        iterable = self.visit(gen.iter)
        
        key_expr = self.visit(node.key)
        value_expr = self.visit(node.value)
        
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            if predicate is None:
                predicate = cond
            else:
                predicate = BinOp(predicate, BoolOps.And, cond)
        
        # For simplicity, we'll create a dict with placeholder and transform later
        # This is a limitation - full dict comprehension support requires more work
        return DictLiteral([key_expr], [value_expr])
    
    def visit_List(self, node):
        """Handle list literals: [1, 2, 3]"""
        # Starred list construction (e.g., [*a, *b]) is difficult to model
        # precisely in our current logic; return a conservative placeholder.
        if any(isinstance(e, ast.Starred) for e in node.elts):
            # Placeholder list comprehension standing for an unknown array value.
            return ListComprehension(Var('__elem__'), Var('__x__'), Var('__iter__'))
        # Model list literals as arrays with known values at concrete indices.
        # Unspecified indices remain unconstrained (sound over-approximation).
        base: Expr = self._fresh_list_base()
        for i, e in enumerate(node.elts):
            base = Store(base, Literal(VInt(i)), self.visit(e))
        return base
    
    def visit_Set(self, node):
        """Handle set literals: {1, 2, 3}"""
        elements = [self.visit(e) for e in node.elts]
        return SetLiteral(elements)
    
    def visit_Dict(self, node):
        """Handle dict literals: {'a': 1, 'b': 2}"""
        keys = [self.visit(k) for k in node.keys]
        values = [self.visit(v) for v in node.values]
        return DictLiteral(keys, values)
    
    def visit_Lambda(self, node):
        """Handle lambda expressions."""
        params = []
        for arg in node.args.args:
            if arg.arg != 'self':
                params.append((arg.arg, 'Any'))
        body = self.visit(node.body)
        return Lambda(params, body)
    
    def visit_Yield(self, node):
        """Handle yield expressions."""
        value = self.visit(node.value) if node.value else None
        return Yield(value)
    
    def visit_YieldFrom(self, node):
        """Handle yield from expressions."""
        iterable = self.visit(node.value)
        return YieldFrom(iterable)
    
    def visit_Await(self, node):
        """Handle await expressions."""
        value = self.visit(node.value)
        return Await(value)
    
    def visit_NamedExpr(self, node):
        """Handle named expressions (walrus operator :=)."""
        target = node.target.id if isinstance(node.target, ast.Name) else str(node.target)
        value = self.visit(node.value)
        return Walrus(target, value)
    
    def visit_FormattedValue(self, node):
        """Handle formatted values in f-strings."""
        return self.visit(node.value)
    
    def visit_JoinedStr(self, node):
        """Handle f-strings (joined string)."""
        parts = []
        literal_parts = []
        for element in node.values:
            if isinstance(element, ast.Constant) and isinstance(element.value, str):
                literal_parts.append(element.value)
            elif isinstance(element, ast.FormattedValue):
                parts.append(self.visit_FormattedValue(element))
        # Ensure literal_parts is always len(parts)+1
        while len(literal_parts) < len(parts) + 1:
            literal_parts.append('')
        return FString(parts, literal_parts)
    
    def visit_Starred(self, node):
        """Handle starred expressions (*x)."""
        return self.visit(node.value)

    def visit_GeneratorExp(self, node):
        """Handle generator expressions."""
        if len(node.generators) != 1:
            raise_exception('Only single-generator comprehensions supported')
        gen = node.generators[0]
        target = Var(gen.target.id)
        iterable = self.visit(gen.iter)
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            predicate = cond if predicate is None else BinOp(predicate, BoolOps.And, cond)
        generator = Generator(target, iterable, predicate)
        element = self.visit(node.elt)
        return Comprehension('generator', element, [generator])

    def visit_FunctionDef(self, node):
        """Handle decorated function definitions as expressions (decorators/properties)."""
        decorators = node.decorator_list
        dec_exprs = []
        for dec in decorators:
            if isinstance(dec, ast.Name) and dec.id == 'property':
                dec_exprs.append(Property(node.name, getter=True, setter=False))
            elif isinstance(dec, ast.Attribute) and dec.attr == 'setter':
                # @x.setter
                dec_exprs.append(Property(dec.value.id if isinstance(dec.value, ast.Name) else node.name,
                                          getter=False, setter=True))
            elif isinstance(dec, ast.Name) and dec.id == 'staticmethod':
                dec_exprs.append(StaticMethod(node.name))
            elif isinstance(dec, ast.Name) and dec.id == 'classmethod':
                dec_exprs.append(ClassMethod(node.name))
            elif isinstance(dec, ast.Call):
                dec_exprs.append(Decorator(dec.func.id if isinstance(dec.func, ast.Name) else str(dec.func),
                                           [self.visit(arg) for arg in dec.args]))
            elif isinstance(dec, ast.Name):
                dec_exprs.append(Decorator(dec.id))
        if len(dec_exprs) == 1:
            return dec_exprs[0]
        if len(dec_exprs) > 1:
            return DecoratorChain(dec_exprs)
        # Fallback: represent bare function as MethodDef-like placeholder
        return MethodDef(node.name, [], Skip())

    def visit_ClassDef(self, node):
        """Handle class definitions for dataclass / protocol."""
        decorator_names = [d.id if isinstance(d, ast.Name) else getattr(d, 'func', None) and getattr(d.func, 'id', None)
                           for d in node.decorator_list]
        if 'dataclass' in decorator_names:
            init_opt, eq_opt = True, True
            for d in node.decorator_list:
                if isinstance(d, ast.Call) and isinstance(d.func, ast.Name) and d.func.id == 'dataclass':
                    for kw in d.keywords:
                        if kw.arg == 'init':
                            init_opt = bool(getattr(kw.value, 'value', True))
                        if kw.arg == 'eq':
                            eq_opt = bool(getattr(kw.value, 'value', True))
            fields = []
            for stmt in node.body:
                if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                    fields.append((stmt.target.id, None, None))
            return DataClass(node.name, fields, init=init_opt, eq=eq_opt)
        # Protocol detection via base classes
        for base in node.bases:
            if isinstance(base, ast.Name) and base.id == 'Protocol':
                methods = []
                attrs = []
                for stmt in node.body:
                    if isinstance(stmt, ast.FunctionDef):
                        methods.append(MethodSignature(stmt.name, []))
                    if isinstance(stmt, ast.AnnAssign) and isinstance(stmt.target, ast.Name):
                        attrs.append((stmt.target.id, None))
                return Protocol(node.name, methods, attrs)
        # Otherwise treat as generic class def
        return ClassDef(node.name, [])

    def visit_Assign(self, node):
        """Handle simple assignments in expression context (type aliases/final)."""
        if len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            value_expr = self.visit(node.value)
            # Heuristically treat alias vs constant assignment
            if isinstance(value_expr, (Var, Subscript)):
                return TypeAlias(name, value_expr)
            return Assign(Var(name), value_expr)
        return Assign(Var('__assign__'), self.visit(node.value))
    
    def visit_ListComp(self, node):
        """Handle list comprehensions."""
        if len(node.generators) != 1:
            raise_exception('Only single-generator comprehensions supported')
        
        gen = node.generators[0]
        element_var = Var(gen.target.id)
        iterable = self.visit(gen.iter)
        
        element_expr = self.visit(node.elt)
        
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            if predicate is None:
                predicate = cond
            else:
                predicate = BinOp(predicate, BoolOps.And, cond)
        
        return ListComprehension(element_expr, element_var, iterable, predicate)
    
    def visit_DictComp(self, node):
        """Handle dict comprehensions."""
        if len(node.generators) != 1:
            raise_exception('Only single-generator comprehensions supported')
        
        gen = node.generators[0]
        key_expr = self.visit(node.key)
        value_expr = self.visit(node.value)
        
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            if predicate is None:
                predicate = cond
            else:
                predicate = BinOp(predicate, BoolOps.And, cond)
        
        return DictLiteral([key_expr], [value_expr])
    
    def visit_SetComp(self, node):
        """Handle set comprehensions."""
        if len(node.generators) != 1:
            raise_exception('Only single-generator comprehensions supported')
        
        gen = node.generators[0]
        element_expr = self.visit(node.elt)
        element_var = Var(gen.target.id)
        iterable = self.visit(gen.iter)
        
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            if predicate is None:
                predicate = cond
            else:
                predicate = BinOp(predicate, BoolOps.And, cond)
        
        return SetComprehension(element_var, iterable, predicate)
    
    def visit_GeneratorExp(self, node):
        """Handle generator expressions."""
        gen = node.generators[0]
        element_expr = self.visit(node.elt)
        element_var = Var(gen.target.id)
        iterable = self.visit(gen.iter)
        
        predicate = None
        for if_cond in gen.ifs:
            cond = self.visit(if_cond)
            if predicate is None:
                predicate = cond
            else:
                predicate = BinOp(predicate, BoolOps.And, cond)
        
        return Comprehension('generator', element_expr, [
            Generator(element_var, iterable, predicate)
        ])
    
    def visit_arguments(self, node):
        """Handle function arguments (Python 3.8+)."""
        args = []
        defaults = []
        
        # Handle regular arguments
        for arg in node.args:
            if arg.arg is not None:
                args.append((arg.arg, 'Any'))
        
        # Handle defaults
        if node.defaults:
            for default in node.defaults:
                defaults.append(self.visit(default))
        
        return args, defaults
    
    def visit_keyword(self, node):
        """Handle keyword arguments in calls."""
        if node.arg is None:
            return ('**kwargs', self.visit(node.value))
        return (node.arg, self.visit(node.value))
    
    def visit(self, node):
        """Main dispatch method."""
        handlers = {
            ast.Name: self.visit_Name,
            ast.Num: self.visit_Num,
            ast.Constant: self.visit_Constant,
            ast.Str: self.visit_Str,
            ast.NameConstant: self.visit_NameConstant,
            ast.Expr: self.visit_Expr,
            ast.BoolOp: self.visit_BoolOp,
            ast.Compare: self.visit_Compare,
            ast.BinOp: self.visit_BinOp,
            ast.UnaryOp: self.visit_UnaryOp,
            ast.Call: self.visit_Call,
            ast.Subscript: self.visit_Subscript,
            ast.Attribute: self.visit_Attribute,
            ast.Index: self.visit_Index,
            ast.ListComp: self.visit_ListComp,
            ast.SetComp: self.visit_SetComp,
            ast.DictComp: self.visit_DictComp,
            ast.List: self.visit_List,
            ast.Set: self.visit_Set,
            ast.Dict: self.visit_Dict,
            ast.Lambda: self.visit_Lambda,
            ast.Yield: self.visit_Yield,
            ast.YieldFrom: self.visit_YieldFrom,
            ast.Await: self.visit_Await,
            ast.NamedExpr: self.visit_NamedExpr,
            ast.FormattedValue: self.visit_FormattedValue,
            ast.JoinedStr: self.visit_JoinedStr,
            ast.Starred: self.visit_Starred,
            ast.GeneratorExp: self.visit_GeneratorExp,
            ast.FunctionDef: self.visit_FunctionDef,
            ast.ClassDef: self.visit_ClassDef,
            ast.Assign: self.visit_Assign,
        }
        
        handler = handlers.get(type(node))
        if handler:
            return handler(node)
        raise_exception(f'Unsupported AST node: {type(node).__name__}')


class StmtTranslator:
    """Translator that converts Python statement AST to veripy statement AST."""

    def __init__(self):
        # Counter for call-lifting temporaries
        self._tmp_idx = 0

    def _fresh_tmp(self, prefix: str = "__call_tmp") -> str:
        self._tmp_idx += 1
        return f"{prefix}{self._tmp_idx}"

    def _list_literal_expr(self, elts: List[ast.AST]) -> Expr:
        """
        Model a Python list literal as an array with Stores at concrete indices.
        Unspecified indices are unconstrained.
        """
        base: Expr = Var(self._fresh_tmp("__list_lit_base"))
        for i, e in enumerate(elts):
            base = Store(base, Literal(VInt(i)), self.visit(e))
        return base

    def _seq_from(self, stmts: List[Stmt]) -> Stmt:
        if not stmts:
            return Skip()
        s = stmts[0]
        for t in stmts[1:]:
            s = Seq(s, t)
        return s

    def _lift_calls_expr(self, e: Expr):
        """
        Lift nested function calls from an expression into temp assignments.

        Returns (stmts, new_expr) such that executing stmts then evaluating
        new_expr is equivalent (best-effort) to evaluating e directly.
        """
        # Leaf nodes
        if isinstance(e, (Var, Literal, StringLiteral)):
            return ([], e)

        if isinstance(e, FunctionCall):
            lifted = []
            new_args = []
            for a in e.args:
                s, a2 = self._lift_calls_expr(a)
                lifted.extend(s)
                new_args.append(a2)
            tmp = self._fresh_tmp()
            lifted.append(Assign(tmp, FunctionCall(e.func_name, new_args, native=getattr(e, "native", True))))
            return (lifted, Var(tmp))

        if isinstance(e, BinOp):
            s1, e1 = self._lift_calls_expr(e.e1)
            s2, e2 = self._lift_calls_expr(e.e2)
            return (s1 + s2, BinOp(e1, e.op, e2))

        if isinstance(e, UnOp):
            s, e1 = self._lift_calls_expr(e.e)
            return (s, UnOp(e.op, e1))

        if isinstance(e, Subscript):
            s1, v = self._lift_calls_expr(e.var)
            s2, i = self._lift_calls_expr(e.subscript)
            return (s1 + s2, Subscript(v, i))

        if isinstance(e, Store):
            s1, a = self._lift_calls_expr(e.arr)
            s2, i = self._lift_calls_expr(e.idx)
            s3, v = self._lift_calls_expr(e.val)
            return (s1 + s2 + s3, Store(a, i, v))

        if isinstance(e, FieldAccess):
            s, o = self._lift_calls_expr(e.obj)
            return (s, FieldAccess(o, e.field))

        # Fallback: no lifting
        return ([], e)
    
    def visit_Assign(self, node):
        # Support tuple unpacking (a, *b, c = ...)
        if isinstance(node.targets[0], ast.Tuple):
            # Represent unpacking explicitly so the verifier can fail closed
            # (silently dropping these updates would be unsound).
            def _tgt(t):
                if isinstance(t, ast.Starred):
                    inner = t.value.id if isinstance(t.value, ast.Name) else str(t.value)
                    return ('*', inner)
                if isinstance(t, ast.Name):
                    return t.id
                return str(t)
            unpack_target = tuple(_tgt(t) for t in node.targets[0].elts)
            expr = self.visit(node.value) if not isinstance(node.value, ast.List) else self._list_literal_expr(node.value.elts)
            return Assign(unpack_target, expr)
        else:
            target = self.visit(node.targets[0])
        # Translate RHS (list literals need special handling in statement context).
        if isinstance(node.value, ast.List):
            expr = self._list_literal_expr(node.value.elts)
        else:
            expr = self.visit(node.value)
        
        # Check for field assignment (obj.field = value)
        if isinstance(target, FieldAccess):
            return FieldAssignStmt(target.obj, target.field, expr)
        
        # Check if it's a subscript assignment (arr[i] = value)
        if isinstance(target, Subscript):
            # Model `a[i] = v` as `a = Store(a, i, v)` when possible, so WP can
            # substitute array updates correctly.
            base = target.var
            if isinstance(base, Var):
                return Assign(base.name, Store(base, target.subscript, expr))
            # Fail closed: skipping updates to complex bases is unsound.
            raise_exception('Unsupported subscript assignment base (must be a variable)')
        
        # Normalize simple assignments to use the variable name (string) as LHS.
        lhs = target.name if isinstance(target, Var) else target
        # Lift nested calls from RHS so function specs can be applied via Assign.
        lifted, expr2 = self._lift_calls_expr(expr)
        final = Assign(lhs, expr2)
        if lifted:
            return self._seq_from(lifted + [final])
        return final
    
    def visit_AnnAssign(self, node):
        """Handle annotated assignments: x: int = 5"""
        var = self.visit(node.target)
        expr = self.visit(node.value) if node.value else None
        return Assign(var, expr) if expr else Skip()
    
    def visit_If(self, node):
        cond = self.visit(node.test)
        lb = self.visit(node.body[0]) if node.body else Skip()
        rb = self.visit(node.orelse[0]) if node.orelse else Skip()
        return If(cond, lb, rb)
    
    def visit_While(self, node):
        # Extract loop invariants from comments or assert statements
        invariants = []
        def _is_invariant_call(stmt):
            if not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)):
                return False
            f = stmt.value.func
            return (isinstance(f, ast.Name) and f.id == 'invariant') or (isinstance(f, ast.Attribute) and f.attr == 'invariant')

        def _get_str_arg(call: ast.Call):
            if not call.args:
                return None
            a0 = call.args[0]
            if isinstance(a0, ast.Constant) and isinstance(a0.value, str):
                return a0.value
            if isinstance(a0, ast.Str):
                return a0.s
            try:
                return ast.unparse(a0)
            except Exception:
                return None

        for stmt in node.body:
            if _is_invariant_call(stmt):
                inv_text = _get_str_arg(stmt.value)
                if inv_text is not None:
                    invariants.append(parse_assertion(inv_text))
        
        cond = self.visit(node.test)
        # Translate the whole body, skipping invariant(...) annotation calls.
        body_stmts = [self.visit(s) for s in node.body if not _is_invariant_call(s)]
        body = self.visit_seq([])  # default Skip()
        if body_stmts:
            body = body_stmts[0]
            for s in body_stmts[1:]:
                body = Seq(body, s)
        else:
            body = Skip()
        return While(invariants, cond, body)
    
    def visit_For(self, node):
        """Handle for loops: for i in range(n): ... """
        # Extract invariants
        invariants = []
        for stmt in node.body:
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                if isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == 'invariant':
                    inv_text = stmt.value.args[0].value if isinstance(stmt.value.args[0], ast.Constant) else getattr(stmt.value.args[0], 's', None)
                    if isinstance(inv_text, str):
                        invariants.append(parse_assertion(inv_text))
        
        # Transform to while loop
        iter_var = node.target.id
        iterable = node.iter
        
        # Handle range(n)
        if isinstance(iterable, ast.Call):
            if isinstance(iterable.func, ast.Name) and iterable.func.id == 'range':
                start = 0
                stop = self.visit(iterable.args[0])
                step = 1
                if len(iterable.args) > 1:
                    start = self.visit(iterable.args[0])
                    stop = self.visit(iterable.args[1])
                if len(iterable.args) > 2:
                    step = self.visit(iterable.args[2])
                
                # Create: i = start; while i < stop: ...; i += step
                # This is a simplified transformation
                cond = BinOp(Var(iter_var), CompOps.Lt, stop)
                body_stmts = [self.visit(s) for s in node.body if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Name) and s.value.func.id == 'invariant')]
                body = body_stmts[0] if body_stmts else Skip()
                for s in body_stmts[1:]:
                    body = Seq(body, s)
                return While(invariants, cond, body)
        
        raise_exception(f'Unsupported for loop iterable: {ast.dump(iterable)}')
    
    def visit_Assert(self, node):
        expr = self.visit(node.test)
        return Assert(expr)
    
    def visit_Assume(self, node):
        # Handle assume(...) calls
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                if node.func.id == 'assume':
                    expr = self.visit(node.args[0])
                    return Assume(expr)
        return Skip()
    
    def visit_Pass(self, node):
        return Skip()
    
    def visit_Return(self, node):
        expr = self.visit(node.value) if node.value else None
        # Model a return by assigning to the implicit result variable `ans`
        if not expr:
            return Skip()
        lifted, expr2 = self._lift_calls_expr(expr)
        ret = Assign('ans', expr2)
        if lifted:
            return self._seq_from(lifted + [ret])
        return ret
    
    def visit_Expr(self, node):
        # Handle expression statements (including function calls)
        # Expression-statements are generally side-effecting calls which we do not
        # model in the core statement language (except assume(), which is a Stmt).
        if isinstance(node.value, ast.Call):
            # `assume(e)` is a real statement.
            if isinstance(node.value.func, ast.Name) and node.value.func.id == 'assume':
                return self.visit_Assume(node.value)
            # For other calls, fail closed by routing through Assign so that
            # preconditions/ensures are enforced via wp_assign_x.
            call_expr = self.visit(node.value)
            tmp = self._fresh_tmp("__expr_call")
            lifted, expr2 = self._lift_calls_expr(call_expr)
            final = Assign(tmp, expr2)
            if lifted:
                return self._seq_from(lifted + [final])
            return final
        return Skip()
    
    def visit_Module(self, node):
        """Handle module root by sequencing contained statements."""
        if not node.body:
            return Skip()
        stmts = [self.visit(stmt) for stmt in node.body]
        return reduce(lambda acc, s: Seq(acc, s), stmts[1:], stmts[0])
    
    def visit(self, node):
        """Main dispatch method."""
        handlers = {
            ast.Assign: self.visit_Assign,
            ast.AnnAssign: self.visit_AnnAssign,
            ast.AugAssign: self.visit_AugAssign,
            ast.If: self.visit_If,
            ast.While: self.visit_While,
            ast.For: self.visit_For,
            ast.Try: self.visit_Try,
            ast.With: self.visit_With,
            ast.AsyncWith: self.visit_AsyncWith,
            ast.AsyncFor: self.visit_AsyncFor,
            ast.Assert: self.visit_Assert,
            ast.Pass: self.visit_Pass,
            ast.Return: self.visit_Return,
            ast.Break: self.visit_Break,
            ast.Continue: self.visit_Continue,
            ast.Raise: self.visit_Raise,
            ast.Global: self.visit_Global,
            ast.Nonlocal: self.visit_Nonlocal,
            ast.Import: self.visit_Import,
            ast.ImportFrom: self.visit_ImportFrom,
            ast.FunctionDef: self.visit_FunctionDef,
            ast.AsyncFunctionDef: self.visit_AsyncFunctionDef,
            ast.ClassDef: self.visit_ClassDef,
            ast.Match: self.visit_Match,
            ast.Expr: self.visit_Expr,
            ast.Module: self.visit_Module,
            ast.Lambda: self.visit_Lambda,
            ast.Yield: self.visit_Yield,
            ast.YieldFrom: self.visit_YieldFrom,
            ast.Await: self.visit_Await,
            ast.NamedExpr: self.visit_NamedExpr,
            ast.List: self.visit_List,
            # Expression handlers for statement context
            ast.Name: self.visit_Name,
            ast.Attribute: self.visit_Attribute,
            ast.Subscript: self.visit_Subscript,
            ast.Constant: self.visit_Constant,
            ast.Num: self.visit_Num,
            ast.Str: self.visit_Str,
            ast.NameConstant: self.visit_NameConstant,
            ast.BoolOp: self.visit_BoolOp,
            ast.Compare: self.visit_Compare,
            ast.BinOp: self.visit_BinOp,
            ast.UnaryOp: self.visit_UnaryOp,
            ast.Call: self.visit_Call,
            ast.IfExp: self.visit_IfExp,
        }
        
        handler = handlers.get(type(node))
        if handler:
            return handler(node)
        raise_exception(f'Stmt not supported: {type(node).__name__}')

    def visit_Name(self, node):
        """Handle name references in statement context."""
        return Var(node.id)

    def visit_Attribute(self, node):
        """Handle attribute access in statement context."""
        value = self.visit(node.value)
        return FieldAccess(value, node.attr)

    def visit_Subscript(self, node):
        """Handle subscript access in statement context."""
        value = self.visit(node.value)
        subscript = self.visit(node.slice)
        return Subscript(value, subscript)
    
    def visit_Constant(self, node):
        """Handle constant literals."""
        from veripy.parser.syntax import VInt, VBool, VString, Literal
        if isinstance(node.value, bool):
            return Literal(VBool(node.value))
        elif isinstance(node.value, int):
            return Literal(VInt(node.value))
        elif isinstance(node.value, str):
            return StringLiteral(node.value)
        else:
            return Literal(VInt(0))  # Fallback
    
    def visit_Num(self, node):
        """Handle numeric literals (Python 3.7 and earlier)."""
        return Literal(VInt(node.n))
    
    def visit_Str(self, node):
        """Handle string literals (Python 3.7 and earlier)."""
        return StringLiteral(node.s)
    
    def visit_NameConstant(self, node):
        """Handle name constants (True, False, None)."""
        from veripy.parser.syntax import VBool, Literal
        return Literal(VBool(node.value))

    def visit_List(self, node):
        """Handle list literals in statement context."""
        if any(isinstance(e, ast.Starred) for e in node.elts):
            return ListComprehension(Var('__elem__'), Var('__x__'), Var('__iter__'))
        return self._list_literal_expr(node.elts)
    
    def visit_BoolOp(self, node):
        """Handle boolean operations."""
        from veripy.parser.syntax import BoolOps
        values = [self.visit(v) for v in node.values]
        op = BoolOps.And if isinstance(node.op, ast.And) else BoolOps.Or
        result = values[0]
        for v in values[1:]:
            result = BinOp(result, op, v)
        return result
    
    def visit_Compare(self, node):
        """Handle comparisons."""
        from veripy.parser.syntax import CompOps
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        
        op_map = {
            ast.Lt: CompOps.Lt,
            ast.LtE: CompOps.Le,
            ast.Gt: CompOps.Gt,
            ast.GtE: CompOps.Ge,
            ast.Eq: CompOps.Eq,
            ast.NotEq: CompOps.Neq,
            ast.In: CompOps.In,
        }
        op = op_map.get(type(node.ops[0]), CompOps.Eq)
        return BinOp(left, op, right)
    
    def visit_BinOp(self, node):
        """Handle binary operations."""
        from veripy.parser.syntax import ArithOps
        left = self.visit(node.left)
        right = self.visit(node.right)
        
        op_map = {
            ast.Add: ArithOps.Add,
            ast.Sub: ArithOps.Minus,
            ast.Mult: ArithOps.Mult,
            ast.Div: ArithOps.IntDiv,
            ast.FloorDiv: ArithOps.IntDiv,
            ast.Mod: ArithOps.Mod,
        }
        op = op_map.get(type(node.op), ArithOps.Add)
        return BinOp(left, op, right)
    
    def visit_UnaryOp(self, node):
        """Handle unary operations."""
        from veripy.parser.syntax import ArithOps, BoolOps
        operand = self.visit(node.operand)
        
        if isinstance(node.op, ast.USub):
            return UnOp(ArithOps.Neg, operand)
        elif isinstance(node.op, ast.Not):
            return UnOp(BoolOps.Not, operand)
        else:
            return operand
    
    def visit_Call(self, node):
        """Handle function calls."""
        # Calls can appear inside expressions (e.g., x = f(n), return f(x)).
        # We translate those to FunctionCall expressions.
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
        elif isinstance(node.func, ast.Attribute):
            func_name = node.func.attr
        else:
            raise_exception(f'Unsupported call func: {ast.dump(node.func)}')

        args = [self.visit(arg) for arg in node.args]
        return FunctionCall(Var(func_name), args)
    
    def visit_IfExp(self, node):
        """Handle ternary expressions (x if cond else y)."""
        cond = self.visit(node.test)
        then_expr = self.visit(node.body)
        else_expr = self.visit(node.orelse)
        return If(cond, then_expr, else_expr)

    # =========================================================================
    # Extended Statement Visitors
    # =========================================================================

    def visit_AugAssign(self, node):
        """Handle augmented assignments: x += 1, x -= 1, etc."""
        var = self.visit(node.target)
        expr = self.visit(node.value)
        
        op_map = {
            ast.Add: ArithOps.Add,
            ast.Sub: ArithOps.Minus,
            ast.Mult: ArithOps.Mult,
            ast.Div: ArithOps.IntDiv,
            ast.FloorDiv: ArithOps.IntDiv,
            ast.Mod: ArithOps.Mod,
            ast.Pow: ArithOps.Mult,  # Approximation
        }
        
        op = op_map.get(type(node.op), ArithOps.Add)
        return AugAssign(var, op, expr)

    def visit_Try(self, node):
        """Handle try/except/finally/else statements."""
        body = self.visit_seq(node.body)
        
        handlers = []
        for handler in node.handlers:
            exc_type = handler.type.id if handler.type else 'Exception'
            exc_var = handler.name if handler.name else None
            handler_body = self.visit_seq(handler.body)
            handlers.append(ExceptHandler(exc_type, exc_var, handler_body))
        
        orelse = self.visit_seq(node.orelse) if node.orelse else None
        finalbody = self.visit_seq(node.finalbody) if node.finalbody else None
        
        return Try(body, handlers, orelse, finalbody)

    def visit_With(self, node):
        """Handle with statements."""
        # Handle simple with statements (single context manager)
        if len(node.items) == 1:
            item = node.items[0]
            context_expr = self.visit(item.context_expr)
            item_var = item.optional_vars.id if item.optional_vars else '__context__'
            body = self.visit_seq(node.body)
            return With(context_expr, item_var, body)
        else:
            # Nested with statements - simplify to single context
            raise_exception('Multiple context managers in with statement not yet supported')

    def visit_AsyncWith(self, node):
        """Handle async with statements."""
        return self.visit_With(node)  # Treat same as regular with for now

    def visit_AsyncFor(self, node):
        """Handle async for loops."""
        return self.visit_For(node)  # Treat same as regular for for now

    def visit_Break(self, node):
        """Handle break statements."""
        return Break()

    def visit_Continue(self, node):
        """Handle continue statements."""
        return Continue()

    def visit_Raise(self, node):
        """Handle raise statements."""
        exc_expr = self.visit(node.exc) if node.exc else None
        cause = self.visit(node.cause) if node.cause else None
        return Raise(exc_expr, cause)

    def visit_Global(self, node):
        """Handle global variable declarations."""
        return Global(node.names)

    def visit_Nonlocal(self, node):
        """Handle nonlocal variable declarations."""
        return Nonlocal(node.names)

    def visit_Import(self, node):
        """Handle import statements."""
        for alias in node.names:
            if alias.asname:
                return ImportStmt(alias.name, alias=alias.asname)
            else:
                return ImportStmt(alias.name)
        return Skip()  # Empty import

    def visit_ImportFrom(self, node):
        """Handle from...import statements."""
        module = node.module or ''
        names = [alias.name for alias in node.names]
        aliases = [alias.asname for alias in node.names if alias.asname]
        return ImportFrom(module, names, aliases if aliases else None)

    def visit_FunctionDef(self, node):
        """Translate function definitions by visiting their bodies."""
        # We ignore decorators and parameters here; the verifier supplies specs.
        return self.visit_seq(node.body)

    def visit_AsyncFunctionDef(self, node):
        """Handle async function definitions."""
        return AsyncFunctionDef(
            name=node.name,
            params=self._get_func_params(node.args),
            body=self.visit_seq(node.body) if node.body else None
        )

    def visit_ClassDef(self, node):
        """Handle class definitions."""
        fields = []
        methods = []
        class_invariants = []
        
        for item in node.body:
            if isinstance(item, ast.FunctionDef):
                # Extract method information
                method_name = item.name
                params = self._get_func_params(item.args)
                
                # Look for decorator @invariant
                invariants = []
                for deco in item.decorator_list:
                    if isinstance(deco, ast.Name) and deco.id == 'invariant':
                        if deco.args:
                            inv_text = deco.args[0].s if hasattr(deco.args[0], 's') else str(deco.args[0].s)
                            invariants.append(parse_assertion(inv_text))
                
                methods.append(MethodDef(
                    class_name=node.name,
                    name=method_name,
                    params=params,
                    body=self.visit_seq(item.body) if item.body else None
                ))
            elif isinstance(item, ast.AnnAssign):
                # Class field with type annotation
                if isinstance(item.target, ast.Name):
                    fields.append((item.target.id, self._get_type(item.annotation)))
            elif isinstance(item, ast.Assign):
                # Class field without type annotation
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        fields.append((target.id, 'Any'))
        
        return ClassDef(
            name=node.name,
            fields=fields,
            invariants=class_invariants,
            methods=methods
        )

    def visit_Match(self, node):
        """Handle match statements (Python 3.10+)."""
        subject = self.visit(node.subject)
        cases = []
        
        for case in node.cases:
            pattern = self._visit_pattern(case.pattern)
            guard = self.visit(case.guard) if case.guard else None
            body = self.visit_seq(case.body) if case.body else None
            cases.append(MatchCase(pattern, guard, body))
        
        return Match(subject, cases)

    def _visit_pattern(self, pattern):
        """Visit a match pattern."""
        if pattern is None:
            return PatternCapture('_')
        
        if isinstance(pattern, ast.MatchAs):
            # Pattern as (alias)
            inner = self._visit_pattern(pattern.pattern) if pattern.pattern else None
            if pattern.name:
                return PatternAs(inner or PatternCapture('_'), pattern.name)
            return inner or PatternCapture('_')
        
        elif isinstance(pattern, ast.MatchOr):
            # Pattern or (|)
            patterns = [self._visit_pattern(p) for p in pattern.patterns]
            return PatternOr(patterns)
        
        elif isinstance(pattern, ast.MatchMapping):
            # Pattern mapping ({...})
            keys = [self.visit(k) for k in pattern.keys]
            patterns = [self._visit_pattern(p) for p in pattern.patterns]
            rest = pattern.rest
            return PatternMapping(keys, patterns, rest)
        
        elif isinstance(pattern, ast.MatchSequence):
            # Pattern sequence (...)
            patterns = [self._visit_pattern(p) for p in pattern.patterns]
            return PatternSequence(patterns)
        
        elif isinstance(pattern, ast.MatchClass):
            # Pattern class (Name(...))
            class_name = pattern.name.id if isinstance(pattern.name, ast.Name) else pattern.name
            patterns = [self._visit_pattern(p) for p in pattern.patterns]
            return PatternClass(class_name, patterns)
        
        elif isinstance(pattern, ast.MatchStar):
            # Pattern star (*name or *)
            name = pattern.name if pattern.name else '_'
            return PatternCapture(name)
        
        elif isinstance(pattern, ast.MatchSingleton):
            # Pattern singleton (True, False, None)
            return PatternLiteral(pattern.value)
        
        elif isinstance(pattern, ast.Constant):
            # Constant pattern
            return PatternLiteral(pattern.value)
        
        elif isinstance(pattern, ast.Name):
            # Capture pattern (variable name)
            return PatternCapture(pattern.id)
        
        else:
            return PatternCapture('_')

    def visit_Lambda(self, node):
        """Handle lambda expressions."""
        params = self._get_func_params(node.args)
        body = self.visit(node.body)
        return Lambda(params, body)

    def visit_Yield(self, node):
        """Handle yield expressions."""
        value = self.visit(node.value) if node.value else None
        return Yield(value)

    def visit_YieldFrom(self, node):
        """Handle yield from expressions."""
        iterable = self.visit(node.value)
        return YieldFrom(iterable)

    def visit_Await(self, node):
        """Handle await expressions."""
        value = self.visit(node.value)
        return Await(value)

    def visit_NamedExpr(self, node):
        """Handle named expressions (walrus operator :=)."""
        target = node.target.id if isinstance(node.target, ast.Name) else str(node.target)
        value = self.visit(node.value)
        return Walrus(target, value)

    def _get_func_params(self, args):
        """Extract function parameters from ast.arguments."""
        params = []
        for arg in args.args:
            if arg.arg != 'self':  # Skip self for methods
                annotation = self._get_type(arg.annotation) if arg.annotation else 'Any'
                params.append((arg.arg, annotation))
        return params

    def _get_type(self, annotation):
        """Extract type from annotation."""
        if annotation is None:
            return 'Any'
        if isinstance(annotation, ast.Name):
            return annotation.id
        elif isinstance(annotation, ast.Constant):
            return str(annotation.value)
        else:
            return 'Any'

    def visit_seq(self, stmts):
        """Convert a list of statements to a sequence."""
        if not stmts:
            return Skip()
        result = None
        for stmt in stmts:
            stmt_translated = self.visit(stmt)
            if result is None:
                result = stmt_translated
            else:
                result = Seq(result, stmt_translated)
        return result if result else Skip()


class Expr2Z3:
    """
    Extended translator that converts veripy AST to Z3 constraints.
    
    Adds support for:
    - Sets (union, intersection, difference, membership, cardinality)
    - Dictionaries (get, set, keys, values)
    - Strings (concat, length, substring, index)
    - Field access (for OOP)
    """
    
    def __init__(self, name_dict: dict, old_dict: dict = None, 
                 func_returns: dict = None, class_fields: dict = None):
        self.name_dict = name_dict
        self.old_dict = old_dict or {}
        self.func_returns = func_returns or {}
        self.class_fields = class_fields or {}  # {class_name: {field_name: z3_sort}}
        # Cache uninterpreted functions/consts by (name, arg_sorts, ret_sort)
        self._uf_cache = {}
        # Cache for list-comprehension placeholders
        self._listcomp_cache = {}
        
        # Uninterpreted functions for special operations
        self._len_fun = z3.Function('len_int', z3.ArraySort(z3.IntSort(), z3.IntSort()), z3.IntSort())
        self._card_set_fun = z3.Function('card_set_int', 
            z3.ArraySort(z3.IntSort(), z3.BoolSort()), z3.IntSort())
        self._dom_map_fun = z3.Function('dom_map_int', 
            z3.ArraySort(z3.IntSort(), z3.IntSort()), 
            z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        
        # String operations
        self._str_len = z3.Function('str_len', z3.StringSort(), z3.IntSort())
        self._str_concat = z3.Function('str_concat', z3.StringSort(), z3.StringSort(), z3.StringSort())
        self._str_substr = z3.Function('str_substr', z3.StringSort(), z3.IntSort(), z3.IntSort(), z3.StringSort())
        self._str_index = z3.Function('str_index', z3.StringSort(), z3.IntSort(), z3.IntSort())

        # Array/list membership (best-effort, uninterpreted)
        self._arr_contains_int = z3.Function(
            'arr_contains_int',
            z3.ArraySort(z3.IntSort(), z3.IntSort()),
            z3.IntSort(),
            z3.BoolSort(),
        )
        
        # Set operations
        self._set_union = z3.Function('set_union',
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        self._set_inter = z3.Function('set_inter',
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        self._set_diff = z3.Function('set_diff',
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        self._set_subset = z3.Function('set_subset',
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.ArraySort(z3.IntSort(), z3.BoolSort()),
            z3.BoolSort())
        
    def translate_type(self, ty):
        if ty == TINT:
            return z3.IntSort()
        if ty == TBOOL:
            return z3.BoolSort()
        if isinstance(ty, TARR):
            return z3.ArraySort(z3.IntSort(), self.translate_type(ty.ty))
        return z3.IntSort()
    
    def visit_Literal(self, lit: Literal):
        v = lit.value
        if isinstance(v, VBool):
            return z3.BoolVal(bool(v.v))
        elif isinstance(v, VInt):
            return z3.IntVal(int(v.v))
        elif isinstance(v, VString):
            return z3.StringVal(v.v)
        elif isinstance(v, VSet):
            # Empty set
            return z3.K(z3.IntSort(), z3.BoolVal(False))
        elif isinstance(v, VDict):
            # Empty dict defaulting to 0
            return z3.K(z3.IntSort(), z3.IntVal(0))
        else:
            raise_exception(f'Unsupported literal: {v}')
    
    def visit_Var(self, node: Var):
        if node.name.endswith('$old'):
            if node.name in self.old_dict:
                return self.old_dict[node.name]
            if node.name not in self.name_dict:
                # Default to Int when type info is missing.
                self.name_dict[node.name] = z3.Int(node.name)
            return self.name_dict[node.name]
        if node.name not in self.name_dict:
            # In unit tests (and some translation paths), variables may appear
            # without having been pre-registered. Default to IntSort.
            self.name_dict[node.name] = z3.Int(node.name)
        return self.name_dict[node.name]
    
    def visit_BinOp(self, node: BinOp):
        c1 = self.visit(node.e1)
        c2 = self.visit(node.e2)
        
        op_handlers = {
            # Arithmetic
            ArithOps.Add: lambda: c1 + c2,
            ArithOps.Minus: lambda: c1 - c2,
            ArithOps.Mult: lambda: c1 * c2,
            ArithOps.IntDiv: lambda: c1 / c2,
            ArithOps.Mod: lambda: c1 % c2,
            
            # Boolean
            BoolOps.And: lambda: z3.And(c1, c2),
            BoolOps.Or: lambda: z3.Or(c1, c2),
            BoolOps.Implies: lambda: z3.Implies(c1, c2),
            BoolOps.Iff: lambda: z3.And(z3.Implies(c1, c2), z3.Implies(c2, c1)),
            
            # Comparison
            CompOps.Eq: lambda: c1 == c2,
            CompOps.Neq: lambda: c1 != c2,
            CompOps.Gt: lambda: c1 > c2,
            CompOps.Ge: lambda: c1 >= c2,
            CompOps.Lt: lambda: c1 < c2,
            CompOps.Le: lambda: c1 <= c2,
            CompOps.In: lambda: (
                z3.Select(c2, c1)
                if (hasattr(c2, "sort") and isinstance(c2.sort(), z3.ArraySortRef) and c2.sort().range() == z3.BoolSort())
                else self._arr_contains_int(c2, c1)
                if (hasattr(c2, "sort") and isinstance(c2.sort(), z3.ArraySortRef) and c2.sort().range() == z3.IntSort())
                else z3.BoolVal(False)
            ),
            CompOps.NotIn: lambda: z3.Not(
                z3.Select(c2, c1)
                if (hasattr(c2, "sort") and isinstance(c2.sort(), z3.ArraySortRef) and c2.sort().range() == z3.BoolSort())
                else self._arr_contains_int(c2, c1)
                if (hasattr(c2, "sort") and isinstance(c2.sort(), z3.ArraySortRef) and c2.sort().range() == z3.IntSort())
                else z3.BoolVal(False)
            ),
        }
        
        return op_handlers.get(node.op, lambda: raise_exception(f'Unsupported Operator: {node.op}'))()
    
    def visit_UnOp(self, node: UnOp):
        c = self.visit(node.e)
        if node.op == ArithOps.Neg:
            return -c
        elif node.op == BoolOps.Not:
            return z3.Not(c)
        raise_exception(f'Unsupported UnOp: {node.op}')
    
    def visit_Quantification(self, node: Quantification):
        # Defensive: some older builders used Quantification(var, expr, ty)
        # instead of Quantification(var, ty, expr).
        q_ty = node.ty
        q_expr = node.expr
        if isinstance(q_ty, Expr) and (q_expr == TINT or q_expr == TBOOL or isinstance(q_expr, TARR)):
            q_ty, q_expr = q_expr, q_ty

        bound_var = None
        if q_ty == TINT:
            bound_var = z3.Int(node.var.name)
        elif q_ty == TBOOL:
            bound_var = z3.Bool(node.var.name)
        elif isinstance(q_ty, TARR):
            bound_var = z3.Array(z3.IntSort(), self.translate_type(q_ty.ty))
        
        if bound_var is not None:
            self.name_dict[node.var.name] = bound_var
            return z3.ForAll(bound_var, self.visit(q_expr))
        raise_exception(f'Unsupported quantified type: {q_ty}')
    
    def visit_Old(self, node: Old):
        if isinstance(node.expr, Var):
            return self.visit(Var(node.expr.name + '$old'))
        if isinstance(node.expr, Subscript):
            base = node.expr.var
            sub = node.expr.subscript
            if isinstance(base, Var):
                return self.visit(Subscript(Var(base.name + '$old'), sub))
        raise_exception(f'Old not supported for {node.expr}')
    
    def visit_Subscript(self, node: Subscript):
        arr = self.visit(node.var)
        idx = self.visit(node.subscript)
        return z3.Select(arr, idx)
    
    def visit_Store(self, node: Store):
        arr = self.visit(node.arr)
        idx = self.visit(node.idx)
        val = self.visit(node.val)
        return z3.Store(arr, idx, val)
    
    def visit_FunctionCall(self, node: FunctionCall):
        func_name = node.func_name
        if isinstance(func_name, Var):
            fname = func_name.name
        else:
            fname = str(func_name)
        
        arg_terms = [self.visit(a) for a in node.args]
        
        # Handle built-in functions
        if fname == 'len':
            assert len(node.args) == 1
            arr = self.visit(node.args[0])
            return self._len_fun(arr)
        
        if fname == 'set':
            return z3.K(z3.IntSort(), z3.BoolVal(False))
        
        if fname == 'card':
            assert len(node.args) == 1
            s = self.visit(node.args[0])
            return self._card_set_fun(s)
        
        if fname == 'mem':
            assert len(node.args) == 2
            x = self.visit(node.args[0])
            s = self.visit(node.args[1])
            return z3.Select(s, x)
        
        if fname == 'dict':
            return z3.K(z3.IntSort(), z3.IntVal(0))
        
        if fname == 'keys':
            assert len(node.args) == 1
            m = self.visit(node.args[0])
            return self._dom_map_fun(m)
        
        if fname == 'str':
            assert len(node.args) == 1
            return z3.StringVal(str(arg_terms[0]))
        
        # Uninterpreted function/const for user functions
        ret_sort = self.translate_type(self.func_returns.get(fname, TINT))
        if not arg_terms:
            key = (f'uf_{fname}', tuple(), ret_sort)
            if key not in self._uf_cache:
                self._uf_cache[key] = z3.Const(f'uf_{fname}', ret_sort)
            return self._uf_cache[key]

        arg_sorts = tuple(t.sort() for t in arg_terms)
        key = (f'uf_{fname}', arg_sorts, ret_sort)
        if key not in self._uf_cache:
            self._uf_cache[key] = z3.Function(f'uf_{fname}', *arg_sorts, ret_sort)
        uf = self._uf_cache[key]
        return uf(*arg_terms)
    
    # =========================================================================
    # New expression visitors for extended features
    # =========================================================================
    
    def visit_StringLiteral(self, node: StringLiteral):
        return z3.StringVal(node.value)
    
    def visit_StringConcat(self, node: StringConcat):
        left = self.visit(node.left)
        right = self.visit(node.right)
        return self._str_concat(left, right)
    
    def visit_StringLength(self, node: StringLength):
        s = self.visit(node.string_expr)
        return self._str_len(s)
    
    def visit_StringIndex(self, node: StringIndex):
        s = self.visit(node.string_expr)
        i = self.visit(node.index)
        return self._str_index(s, i)
    
    def visit_StringSubstring(self, node: StringSubstring):
        s = self.visit(node.string_expr)
        start = self.visit(node.start)
        end = self.visit(node.end) if node.end else self._str_len(s)
        return self._str_substr(s, start, end)
    
    def visit_StringContains(self, node: StringContains):
        sub = self.visit(node.substring)
        s = self.visit(node.string_expr)
        # Check if sub is a substring of s
        # Z3 doesn't have direct substring, so we use contains
        return z3.Contains(s, sub)
    
    def visit_SetLiteral(self, node: SetLiteral):
        """Set literal: convert to Z3 set (array of bools)."""
        # Create empty set and add elements
        result = z3.K(z3.IntSort(), z3.BoolVal(False))
        for elem in node.elements:
            elem_z3 = self.visit(elem)
            result = z3.Store(result, elem_z3, z3.BoolVal(True))
        return result
    
    def visit_SetOp(self, node: SetOp):
        left = self.visit(node.left)
        right = self.visit(node.right)
        
        if node.op == SetOps.Union:
            return self._set_union(left, right)
        elif node.op == SetOps.Intersection:
            return self._set_inter(left, right)
        elif node.op == SetOps.Difference:
            return self._set_diff(left, right)
        elif node.op == SetOps.Member:
            return z3.Select(right, left)
        elif node.op == SetOps.Subset:
            return self._set_subset(left, right)
        elif node.op == SetOps.Superset:
            return self._set_subset(right, left)
        
        raise_exception(f'Unsupported set operation: {node.op}')
    
    def visit_SetCardinality(self, node: SetCardinality):
        s = self.visit(node.set_expr)
        return self._card_set_fun(s)
    
    def visit_DictLiteral(self, node: DictLiteral):
        """Dict literal: convert to Z3 map (array)."""
        # Infer sorts from the first key/value when available (needed for
        # string-key dictionaries).
        if node.keys:
            k_sort = self.visit(node.keys[0]).sort()
        else:
            k_sort = z3.IntSort()
        
        if node.values:
            v_sort = self.visit(node.values[0]).sort()
        else:
            v_sort = z3.IntSort()
        
        if v_sort == z3.BoolSort():
            default_v = z3.BoolVal(False)
        elif v_sort == z3.StringSort():
            default_v = z3.StringVal("")
        else:
            default_v = z3.IntVal(0)
        
        result = z3.K(k_sort, default_v)
        for k, v in zip(node.keys, node.values):
            k_z3 = self.visit(k)
            v_z3 = self.visit(v)
            result = z3.Store(result, k_z3, v_z3)
        return result
    
    def visit_DictGet(self, node: DictGet):
        d = self.visit(node.dict_expr)
        k = self.visit(node.key)
        if node.default:
            # Use Z3 If for default value
            # Check if key is in domain
            # This is simplified - proper handling requires domain tracking
            return z3.Select(d, k)
        return z3.Select(d, k)
    
    def visit_DictSet(self, node: DictSet):
        d = self.visit(node.dict_expr)
        k = self.visit(node.key)
        v = self.visit(node.value)
        return z3.Store(d, k, v)
    
    def visit_DictKeys(self, node: DictKeys):
        d = self.visit(node.dict_expr)
        return self._dom_map_fun(d)
    
    def visit_DictValues(self, node: DictValues):
        # Values are harder - we need to extract all values from the map
        # For now, return uninterpreted
        d = self.visit(node.dict_expr)
        # This is a simplification
        return d
    
    def visit_DictContains(self, node: DictContains):
        d = self.visit(node.dict_expr)
        k = self.visit(node.key)
        # Check if key is in domain (has non-default value)
        return z3.Select(self._dom_map_fun(d), k)
    
    def visit_FieldAccess(self, node: FieldAccess):
        """Field access: obj.field -> need class model."""
        obj = self.visit(node.obj)
        # For now, return uninterpreted access
        # In a full implementation, we'd have proper class models
        field_name = f'{node.field}'
        
        # Create uninterpreted function for field access
        if isinstance(obj, z3.ExprRef):
            # We can create a function that accesses the field
            obj_sort = obj.sort()
            field_func = z3.Function(f'field_{node.field}', obj_sort, z3.IntSort())
            return field_func(obj)
        
        return obj
    
    def visit_MethodCall(self, node: MethodCall):
        """Method call: obj.method(args)."""
        obj = self.visit(node.obj)
        method_name = node.method_name
        args = [self.visit(a) for a in node.args]
        
        # Create uninterpreted function for method call
        obj_sort = obj.sort() if isinstance(obj, z3.ExprRef) else z3.IntSort()
        arg_sorts = [a.sort() for a in args]
        ret_sort = z3.IntSort()  # Simplified
        
        # Z3 has no "Method" API; model as an uninterpreted function.
        method_func = z3.Function(f'method_{method_name}', obj_sort, *arg_sorts, ret_sort)
        return method_func(obj, *args)
    
    def visit_ListComprehension(self, node: ListComprehension):
        """
        List comprehension placeholder.

        For soundness, do NOT return a concrete constant array (that would
        assert facts like "all elements are 0"). Instead, model the result as
        an unconstrained array value.
        """
        key = repr(node)
        if key not in self._listcomp_cache:
            self._listcomp_cache[key] = z3.Array(
                f'listcomp_{len(self._listcomp_cache) + 1}',
                z3.IntSort(),
                z3.IntSort(),
            )
        return self._listcomp_cache[key]
    
    def visit_SetComprehension(self, node: SetComprehension):
        """Set comprehension - simplified to uninterpreted."""
        return z3.K(z3.IntSort(), z3.BoolVal(False))
    
    def visit(self, expr: Expr):
        """Main dispatch method with support for all expression types."""
        handlers = {
            Literal: self.visit_Literal,
            Var: self.visit_Var,
            BinOp: self.visit_BinOp,
            UnOp: self.visit_UnOp,
            Quantification: self.visit_Quantification,
            Subscript: self.visit_Subscript,
            Store: self.visit_Store,
            Old: self.visit_Old,
            FunctionCall: self.visit_FunctionCall,
            
            # String expressions
            StringLiteral: self.visit_StringLiteral,
            StringConcat: self.visit_StringConcat,
            StringLength: self.visit_StringLength,
            StringIndex: self.visit_StringIndex,
            StringSubstring: self.visit_StringSubstring,
            StringContains: self.visit_StringContains,
            
            # Set expressions
            SetLiteral: self.visit_SetLiteral,
            SetOp: self.visit_SetOp,
            SetCardinality: self.visit_SetCardinality,
            SetComprehension: self.visit_SetComprehension,
            
            # Dict expressions
            DictLiteral: self.visit_DictLiteral,
            DictGet: self.visit_DictGet,
            DictSet: self.visit_DictSet,
            DictKeys: self.visit_DictKeys,
            DictValues: self.visit_DictValues,
            DictContains: self.visit_DictContains,
            
            # OOP expressions
            FieldAccess: self.visit_FieldAccess,
            MethodCall: self.visit_MethodCall,
            
            # Comprehensions
            ListComprehension: self.visit_ListComprehension,
        }
        
        handler = handlers.get(type(expr))
        if handler:
            return handler(expr)
        raise_exception(f'Unsupported AST: {type(expr).__name__}')
