"""
Expression translator that converts Python AST to veripy AST.

This module is responsible for bridging the gap between Python's rich syntax
and the restricted, verifiable subset supported by Veripy. It handles:
-   **Literals**: Numbers, booleans, strings, and collections (lists, dicts, sets).
-   **Variables**: Names and attributes.
-   **Operations**: Arithmetic, logical, and comparison operators.
-   **Comprehensions**: List/Set/Generator comprehensions (with limitations).
-   **Function Calls**: Translating built-ins (len, range) and user calls.
-   **Control Flow Expressions**: If-expressions, lambdas.

Unsupported constructs (e.g., `try-except`, dynamic `eval`) raise exceptions
during translation to ensure only verifiable code is processed.
"""

import ast
from veripy.parser.syntax import *
from veripy.parser.parser import parse_assertion
from veripy.built_ins import BUILT_INS
from typing import List
from .utils import raise_exception


class ExprTranslator:
    """
    Translator that converts Python AST to veripy AST.
    
    Maintains state for generating fresh variables (e.g., for list literals).
    """

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

    def visit_Slice(self, node):
        lower = self.visit(node.lower) if node.lower else None
        upper = self.visit(node.upper) if node.upper else None
        step = self.visit(node.step) if node.step else None
        return Slice(lower, upper, step)

    def visit_Tuple(self, node):
        base = self._fresh_list_base()
        arr: Expr = base
        for i, elt in enumerate(node.elts):
            arr = Store(arr, Literal(VInt(i)), self.visit(elt))
        return arr

    def visit_List(self, node):
        # Represent list literals as a special call so the core verifier can
        # lower them into heap allocations.
        elts = [self.visit(e) for e in node.elts]
        return FunctionCall(Var('__list_lit'), elts)

    def visit_Dict(self, node):
        # Represent dict literals as a special call: __dict_lit(k1, v1, k2, v2, ...)
        flat = []
        for k, v in zip(node.keys, node.values):
            flat.append(self.visit(k))
            flat.append(self.visit(v))
        return FunctionCall(Var('__dict_lit'), flat)
    
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
        # Support `for x in ...` and (best-effort) tuple destructuring like
        # `for k, v in ...` by picking a stable binder name.
        if isinstance(gen.target, ast.Name):
            element_var = Var(gen.target.id)
        elif isinstance(gen.target, ast.Tuple) and gen.target.elts and isinstance(gen.target.elts[0], ast.Name):
            element_var = Var(gen.target.elts[0].id)
        else:
            element_var = Var('__comp_target')
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
        if isinstance(gen.target, ast.Name):
            element_var = Var(gen.target.id)
        elif isinstance(gen.target, ast.Tuple) and gen.target.elts and isinstance(gen.target.elts[0], ast.Name):
            element_var = Var(gen.target.elts[0].id)
        else:
            element_var = Var('__comp_target')
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
        # Best-effort support for tuple targets (`for k, v in ...`). This
        # translator currently returns a simplified DictLiteral anyway.
        if isinstance(gen.target, ast.Name):
            element_var = Var(gen.target.id)
        elif isinstance(gen.target, ast.Tuple) and gen.target.elts and isinstance(gen.target.elts[0], ast.Name):
            element_var = Var(gen.target.elts[0].id)
        else:
            element_var = Var('__comp_target')
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
        
        # Preserve comprehension structure so later stages can model it safely.
        return DictComprehension(key_expr, value_expr, element_var, iterable, predicate)
    
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
            ast.Slice: self.visit_Slice,
            ast.Attribute: self.visit_Attribute,
            ast.Index: self.visit_Index,
            ast.Tuple: self.visit_Tuple,
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
