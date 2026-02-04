"""
Statement translator that converts Python statement AST to veripy statement AST.
"""

import ast
from functools import reduce
from typing import List
from veripy.parser.syntax import *
from veripy.parser.parser import parse_assertion
from .expr_translator import ExprTranslator
from .utils import raise_exception


class StmtTranslator:
    """Translator that converts Python statement AST to veripy statement AST."""

    def __init__(self):
        # Counter for call-lifting temporaries
        self._tmp_idx = 0
        # Reuse expression translator so stmt-context literals/exprs stay consistent.
        self._expr_translator = ExprTranslator()
        # Track whether we are inside control-flow (if/while/for) to restrict returns.
        self._in_control = 0
        # Track whether returns are allowed (only at top-level function body).
        self._allow_return = False

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

    # --- Expression delegation helpers (stmt-context expression nodes) ---
    def _expr(self, node):
        return self._expr_translator.visit(node)
    
    def visit_List(self, node):
        return self._expr(node)
    
    def visit_Set(self, node):
        return self._expr(node)
    
    def visit_Dict(self, node):
        return self._expr(node)
    
    def visit_Tuple(self, node):
        # Model tuple literals identically to lists for verification purposes.
        # This keeps translation total without adding tuple-specific semantics.
        return self._expr(node)
    
    def visit_Assign(self, node):
        # Support tuple unpacking (a, *b, c = ...)
        if isinstance(node.targets[0], ast.Tuple):
            # Restrict tuple unpacking to tuple/list literals so RHS length is known.
            targets = []
            for t in node.targets[0].elts:
                if isinstance(t, ast.Starred):
                    raise_exception('Starred tuple unpacking is not supported')
                if isinstance(t, ast.Name):
                    targets.append(t.id)
                else:
                    raise_exception('Only simple name targets are supported in tuple unpacking')

            if not isinstance(node.value, (ast.Tuple, ast.List)):
                raise_exception('Tuple unpacking only supported for tuple/list literals')
            if any(isinstance(e, ast.Starred) for e in node.value.elts):
                raise_exception('Starred tuple unpacking on RHS is not supported')
            if len(node.value.elts) != len(targets):
                raise_exception('Tuple unpacking length mismatch')

            # Evaluate all RHS elements left-to-right into temporaries, then assign.
            stmts = []
            temps = []
            for e in node.value.elts:
                expr = self.visit(e)
                lifted, expr2 = self._lift_calls_expr(expr)
                tmp = self._fresh_tmp("__unpack_tmp")
                stmts.extend(lifted)
                stmts.append(Assign(tmp, expr2))
                temps.append(tmp)

            for tname, tmp in zip(targets, temps):
                stmts.append(Assign(tname, Var(tmp)))
            return self._seq_from(stmts)
        else:
            target = self.visit(node.targets[0])
        # Translate RHS (list literals need special handling in statement context).
        if isinstance(node.value, ast.List):
            expr = FunctionCall(Var('__list_lit'), [self.visit(e) for e in node.value.elts])
        elif isinstance(node.value, ast.Dict):
            flat = []
            for k, v in zip(node.value.keys, node.value.values):
                flat.append(self.visit(k))
                flat.append(self.visit(v))
            expr = FunctionCall(Var('__dict_lit'), flat)
        else:
            expr = self.visit(node.value)
        
        # Check for field assignment (obj.field = value)
        if isinstance(target, FieldAccess):
            return FieldAssignStmt(target.obj, target.field, expr)
        
        # Check if it's a subscript assignment (arr[i] = value)
        if isinstance(target, Subscript):
            base = target.var
            if isinstance(base, Var):
                return SubscriptAssignStmt(base, target.subscript, expr)
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
        expr = None
        if node.value is not None:
            if isinstance(node.value, ast.List):
                expr = FunctionCall(Var('__list_lit'), [self.visit(e) for e in node.value.elts])
            elif isinstance(node.value, ast.Dict):
                flat = []
                for k, v in zip(node.value.keys, node.value.values):
                    flat.append(self.visit(k))
                    flat.append(self.visit(v))
                expr = FunctionCall(Var('__dict_lit'), flat)
            else:
                expr = self.visit(node.value)
        return Assign(var, expr) if expr else Skip()
    
    def visit_If(self, node):
        cond = self.visit(node.test)
        # Translate full statement lists for each branch (dropping statements is unsound).
        self._in_control += 1
        try:
            lb = self.visit_seq(node.body) if node.body else Skip()
            rb = self.visit_seq(node.orelse) if node.orelse else Skip()
        finally:
            self._in_control -= 1
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
        self._in_control += 1
        try:
            body_stmts = [self.visit(s) for s in node.body if not _is_invariant_call(s)]
        finally:
            self._in_control -= 1
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
                def _int_literal(node):
                    if isinstance(node, ast.Constant) and isinstance(node.value, int):
                        return node.value
                    if isinstance(node, ast.Num) and isinstance(node.n, int):
                        return node.n
                    return None

                start = Literal(VInt(0))
                stop = self.visit(iterable.args[0])
                step = Literal(VInt(1))
                step_val = 1
                if len(iterable.args) > 1:
                    start = self.visit(iterable.args[0])
                    stop = self.visit(iterable.args[1])
                if len(iterable.args) > 2:
                    step_val = _int_literal(iterable.args[2])
                    if step_val is None:
                        raise_exception('range() step must be a constant integer for verification soundness')
                    if step_val == 0:
                        raise_exception('range() step cannot be zero')
                    step = Literal(VInt(step_val))
                
                # Create: i = start; while i < stop: body; i += step
                init = Assign(iter_var, start)
                if step_val < 0:
                    cond = BinOp(Var(iter_var), CompOps.Gt, stop)
                else:
                    cond = BinOp(Var(iter_var), CompOps.Lt, stop)
                self._in_control += 1
                try:
                    body_stmts = [self.visit(s) for s in node.body if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Call) and isinstance(s.value.func, ast.Name) and s.value.func.id == 'invariant')]
                finally:
                    self._in_control -= 1
                body = body_stmts[0] if body_stmts else Skip()
                for s in body_stmts[1:]:
                    body = Seq(body, s)
                inc = Assign(iter_var, BinOp(Var(iter_var), ArithOps.Add, step))
                loop_body = Seq(body, inc)
                return Seq(init, While(invariants, cond, loop_body))
        
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
        if self._in_control > 0:
            raise_exception('return is only supported at top-level function body (not inside control flow)')
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
        if isinstance(node.value, bool):
            return Literal(VBool(node.value))
        elif isinstance(node.value, int):
            return Literal(VInt(node.value))
        elif isinstance(node.value, str):
            return StringLiteral(node.value)
        elif node.value is None:
            raise_exception('None is not supported in verification')
        raise_exception(f'Unsupported constant: {node.value!r}')
    
    def visit_Num(self, node):
        """Handle numeric literals (Python 3.7 and earlier)."""
        return Literal(VInt(node.n))
    
    def visit_Str(self, node):
        """Handle string literals (Python 3.7 and earlier)."""
        return StringLiteral(node.s)
    
    def visit_NameConstant(self, node):
        """Handle name constants (True, False, None)."""
        if node.value is None:
            raise_exception('None is not supported in verification')
        return Literal(VBool(node.value))

    def visit_List(self, node):
        """Handle list literals in statement context."""
        if any(isinstance(e, ast.Starred) for e in node.elts):
            return ListComprehension(Var('__elem__'), Var('__x__'), Var('__iter__'))
        return self._list_literal_expr(node.elts)
    
    def visit_BoolOp(self, node):
        """Handle boolean operations."""
        values = [self.visit(v) for v in node.values]
        op = BoolOps.And if isinstance(node.op, ast.And) else BoolOps.Or
        result = values[0]
        for v in values[1:]:
            result = BinOp(result, op, v)
        return result
    
    def visit_Compare(self, node):
        """Handle comparisons."""
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
            ast.NotIn: CompOps.NotIn,
        }
        op = op_map.get(type(node.ops[0]))
        if op is None:
            raise_exception(f'Unsupported comparison operator: {type(node.ops[0]).__name__}')
        return BinOp(left, op, right)
    
    def visit_BinOp(self, node):
        """Handle binary operations."""
        left = self.visit(node.left)
        right = self.visit(node.right)
        
        op_map = {
            ast.Add: ArithOps.Add,
            ast.Sub: ArithOps.Minus,
            ast.Mult: ArithOps.Mult,
            ast.FloorDiv: ArithOps.IntDiv,
            ast.Mod: ArithOps.Mod,
        }
        op = op_map.get(type(node.op))
        if op is None:
            raise_exception(f'Unsupported binary operator: {type(node.op).__name__}')
        return BinOp(left, op, right)
    
    def visit_UnaryOp(self, node):
        """Handle unary operations."""
        operand = self.visit(node.operand)
        
        if isinstance(node.op, ast.USub):
            return UnOp(ArithOps.Neg, operand)
        elif isinstance(node.op, ast.Not):
            return UnOp(BoolOps.Not, operand)
        raise_exception(f'Unsupported unary operator: {type(node.op).__name__}')
    
    def visit_Call(self, node):
        """Handle function calls."""
        # Calls can appear inside expressions (e.g., x = f(n), return f(x)).
        # We translate those to FunctionCall expressions.
        if isinstance(node.func, ast.Name):
            func_name = node.func.id
            args = [self.visit(arg) for arg in node.args]
            return FunctionCall(Var(func_name), args)
        if isinstance(node.func, ast.Attribute):
            obj = self.visit(node.func.value)
            method_name = node.func.attr
            args = [self.visit(arg) for arg in node.args]
            return MethodCall(obj, method_name, args)
        raise_exception(f'Unsupported call func: {ast.dump(node.func)}')
    
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
            ast.FloorDiv: ArithOps.IntDiv,
            ast.Mod: ArithOps.Mod,
        }
        
        op = op_map.get(type(node.op))
        if op is None:
            raise_exception(f'Unsupported augmented assignment operator: {type(node.op).__name__}')
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
        prev_allow = self._allow_return
        self._allow_return = True
        try:
            return self.visit_seq(node.body)
        finally:
            self._allow_return = prev_allow

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
        if self._allow_return:
            for st in stmts[:-1]:
                if isinstance(st, ast.Return):
                    raise_exception('return must be the last statement in a function body')
            if any(isinstance(st, ast.Return) for st in stmts) and self._in_control > 0:
                raise_exception('return is only supported at top-level function body (not inside control flow)')
        result = None
        for stmt in stmts:
            stmt_translated = self.visit(stmt)
            if result is None:
                result = stmt_translated
            else:
                result = Seq(result, stmt_translated)
        return result if result else Skip()

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
            ast.Tuple: self.visit_Tuple,
            ast.Set: self.visit_Set,
            ast.Dict: self.visit_Dict,
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
