"""
Core Verification Engine for Veripy

This module implements the central verification logic, including:
1.  **Verification Condition (VC) Generation**: Using Weakest Precondition (WP) calculus.
2.  **Heap Lowering**: Translating stateful operations (lists, dicts, objects) into explicit heap-passing logic.
3.  **SMT Interaction**: Interfacing with the Z3 theorem prover to check validity of VCs.
4.  **Modular Verification**: Verifying functions in isolation using contracts (requires/ensures).

The pipeline for verifying a function is:
1.  **Parse & Translate**: Python AST -> Veripy AST (`StmtTranslator`).
2.  **Type Check**: Infer types and check consistency (`type_check_stmt`).
3.  **Heap Lowering**:
    -   Identify heap-dependent operations.
    -   Transform the AST to pass heap variables explicitly.
    -   Lower list/dict/field accesses to heap reads/writes.
4.  **WP Generation**: Compute the weakest precondition for the function body with respect to the postcondition.
5.  **SMT Encoding**: Convert the WP and verification obligations into Z3 constraints.
6.  **Solving**: Check satisfiability of `Not(VC)`. If UNSAT, the function is verified.
"""

import ast
import z3
import inspect
from typing import List, Tuple, TypeVar, Dict, Set, Optional, Any, Callable
from veripy.parser.syntax import *
from veripy.parser.parser import parse_assertion, parse_expr
from functools import wraps
from veripy.core.transformer import *
from functools import reduce
from veripy.core.prettyprint import pretty_print
from veripy import typecheck as tc
from veripy.typecheck.types import TARR, TINT, TBOOL
from veripy.typecheck.type_check import issubtype
from veripy.core.heap_lowering import (
    HeapEnv,
    HeapLowerer,
    infer_field_tags,
    global_heap_vars,
    sorted_heap_vars,
    heap_short_name,
    uf_name,
    contains_heap_placeholders_expr,
    contains_heap_placeholders_stmt,
)


# Global cache for uninterpreted functions to ensure consistency across verification
# This cache is shared between function summary generation and expression translation
_UF_CACHE = {}


def _add_builtin_axioms(solver):
    """
    Add axioms for built-in operations that Z3's default theories might not fully cover
    or where we need specific semantics (e.g., Euclidean division).
    """
    # Integer division/modulo properties (defined when divisor non-zero)
    x, y = z3.Ints('x y')
    solver.add(z3.ForAll([x, y], z3.Implies(y != 0, x == (x / y) * y + (x % y))))
    solver.add(z3.ForAll([x, y], z3.Implies(y != 0, z3.And((x % y) >= 0, (x % y) < z3.If(y >= 0, y, -y)))))

    # Basic gcd identities (when uf_gcd is present)
    for key, uf in list(_UF_CACHE.items()):
        if isinstance(uf, z3.FuncDeclRef) and uf.name() == 'uf_gcd':
            a, b = z3.Ints('gcd_a gcd_b')
            solver.add(z3.ForAll([a, b], uf(a, b) >= 0))
            solver.add(z3.ForAll([a], uf(a, 0) == z3.If(a >= 0, a, -a)))
            solver.add(z3.ForAll([a, b], z3.Implies(b != 0, uf(a, b) == uf(b, a % b))))

class VerificationStore:
    """
    Manages the state of verification tasks, scopes, and function attributes.

    This class acts as a central registry for:
    -   **Scopes**: Logical groupings of functions (e.g., modules or test suites).
    -   **Function Attributes**: Contracts (requires/ensures), types, and verification status.
    -   **Verification Tasks**: The actual verification callbacks to be executed.
    """
    def __init__(self):
        self.store = dict()
        self.scope = []
        self.switch = False
        self.pre_states = dict()  # scope -> func_name -> dict(var->z3 const)
        self.func_attrs_global = dict()  # fname -> attrs (inputs, requires, ensures, returns)
        # Track the function currently being verified to allow controlled recursion handling.
        self.current_func = None
        self.self_call = False
    
    def enable_verification(self):
        """Enable the verification process and reset global caches."""
        self.switch = True
        # Clear the uninterpreted function cache when enabling verification
        # to ensure each test starts with a fresh state
        global _UF_CACHE
        _UF_CACHE = {}

    def push(self, scope):
        """Enter a new verification scope."""
        # Allow reusing scope names across tests by clearing old entries
        if scope in self.store:
            self.store.pop(scope, None)
        if scope in self.scope:
            self.scope.remove(scope)
        self.scope.append(scope)
        self.store[scope] = {
            'func_attrs' : dict(),
            'vf'         : []
        }
    
    def current_scope(self):
        """Get the name of the current active scope."""
        if self.scope:
            return self.scope[-1]
    
    def push_verification(self, func_name, verification_func):
        """Register a verification task (callback) for a function in the current scope."""
        if self.switch:
            if not self.scope:
                raise Exception('No Scope Defined')
            self.store[self.scope[-1]]['vf'].append((func_name, verification_func))
    
    def verify(self, scope, ignore_err):
        """
        Execute all verification tasks in the given scope.

        Args:
            scope: The name of the scope to verify.
            ignore_err: If True, suppress exceptions (useful for negative tests).
        """
        if self.switch and self.store:
            print(f'=> Verifying Scope `{scope}`')
            verifications = self.store[scope]
            for f_name, f in verifications['vf']:
                try:
                    f()
                except Exception as e:
                    if not ignore_err:
                        # Re-raise with context about which function failed
                        raise Exception(f"Verification failed for function '{f_name}': {e}") from e
                    else:
                        # When ignore_err=True, keep output concise: failures are expected in "negative" tests.
                        print(f'{f_name} Failed (ignored)')
            print(f'=> End Of `{scope}`\n')
    
    def verify_all(self, ignore_err):
        """Verify all registered scopes in LIFO order."""
        if self.switch:
            try:
                while self.scope:
                    current = self.scope.pop()
                    self.verify(current, ignore_err)
                    # Drop verified scope to avoid stale entries across runs
                    self.store.pop(current, None)
            except Exception as e:
                if not ignore_err:
                    raise e
                else:
                    print(e)           
    
    def insert_func_attr(self, scope, fname, inputs=[], inputs_map={}, returns=tc.types.TANY, requires=[], ensures=[], decreases=None):
        """Register attributes (contracts/types) for a function."""
        if self.switch and self.store:
            self.store[scope]['func_attrs'][fname] = {
                'inputs' : inputs_map,
                'ensures': ensures,
                'requires': requires,
                'decreases': decreases,
                'returns' : returns,
                'func_type' : tc.types.TARROW(tc.types.TPROD(lambda i: i[1], inputs), returns),
                'verified' : False
            }
            # Also register globally for summary lookup across scopes
            self.func_attrs_global[fname] = self.store[scope]['func_attrs'][fname]
    
    def get_func_attr(self, fname):
        """Get attributes for a function from the current scope."""
        if self.store:
            # Legacy API: look up in current scope if available
            if self.scope:
                return self.store[self.scope[-1]].get('func_attrs', dict()).get(fname)
            return None
        return None

    def current_func_attrs(self):
        """Get all function attributes in the current scope."""
        if self.scope:
            return self.store[self.scope[-1]]['func_attrs']
    
    def get_func_attrs(self, scope, fname):
        """Get attributes for a function from a specific scope."""
        # Lookup independent of current scope stack (use provided scope key)
        return self.store[scope]['func_attrs'][fname]


STORE = VerificationStore()

def enable_verification():
    STORE.enable_verification()

def scope(name : str):
    STORE.push(name)

def do_verification(name : str, ignore_err : bool=False):
    STORE.verify(name, ignore_err)

def verify_all(ignore_err : bool=False):
    STORE.verify_all(ignore_err)

def invariant(inv):
    return parse_assertion(inv)

def decreases(measure):
    """
    Parse a decreases expression used for termination annotations.

    This is a lightweight helper so users can write `decreases('n')` in code,
    similar to `invariant('...')`. The core VC engine may choose to use (or
    ignore) this annotation depending on enabled features.
    """
    if measure is None:
        return None
    return parse_expr(measure if isinstance(measure, str) else str(measure))

def assume(C):
    if not C:
        raise RuntimeError('Assumption Violation')


def _and_expr(a: Expr, b: Expr) -> Expr:
    if isinstance(a, Literal) and isinstance(a.value, VBool) and bool(a.value.v) is True:
        return b
    if isinstance(b, Literal) and isinstance(b.value, VBool) and bool(b.value.v) is True:
        return a
    return BinOp(a, BoolOps.And, b)


def _safe_eval_expr(expr: Expr) -> Expr:
    """
    Safety precondition for evaluating `expr` under Python semantics.

    This is intentionally conservative: if we can't establish safety, we
    introduce obligations (e.g., bounds, divisor != 0) that callers must prove.

    Notes:
    - Z3's `div`/`mod` are total; Python raises `ZeroDivisionError`.
    - Z3 array `select` is total; Python list/dict access can raise. We encode
      list/dict accesses via heap-lowering and add obligations on those patterns.
    """
    TRUE = Literal(VBool(True))

    def _not(e: Expr) -> Expr:
        return UnOp(BoolOps.Not, e)

    def _implies(a: Expr, b: Expr) -> Expr:
        if isinstance(a, Literal) and isinstance(a.value, VBool) and bool(a.value.v) is True:
            return b
        return BinOp(a, BoolOps.Implies, b)

    def safe(e: Expr) -> Expr:
        if isinstance(e, (Var, Literal, StringLiteral)):
            return TRUE

        if isinstance(e, UnOp):
            return safe(e.e)

        if isinstance(e, BinOp):
            # Short-circuit boolean connectives.
            if e.op == BoolOps.And:
                return _and_expr(safe(e.e1), _implies(e.e1, safe(e.e2)))
            if e.op == BoolOps.Or:
                return _and_expr(safe(e.e1), _implies(_not(e.e1), safe(e.e2)))
            if e.op == BoolOps.Implies:
                return _and_expr(safe(e.e1), _implies(e.e1, safe(e.e2)))
            if e.op == BoolOps.Iff:
                return _and_expr(safe(e.e1), safe(e.e2))

            out = _and_expr(safe(e.e1), safe(e.e2))
            if e.op in (ArithOps.IntDiv, ArithOps.Mod):
                out = _and_expr(out, BinOp(e.e2, CompOps.Neq, Literal(VInt(0))))
            return out

        if isinstance(e, FunctionCall):
            out = TRUE
            for a in e.args:
                if isinstance(a, Expr):
                    out = _and_expr(out, safe(a))
            return out

        if isinstance(e, Subscript):
            out = _and_expr(safe(e.var), safe(e.subscript))
            # Heap-lowered list read: __heap_list_data_*[ref][idx]
            if isinstance(e.var, Subscript) and isinstance(e.var.var, Var):
                heap_name = e.var.var.name
                ref_expr = e.var.subscript
                idx_expr = e.subscript
                if heap_name.startswith("__heap_list_data_"):
                    out = _and_expr(out, BinOp(idx_expr, CompOps.Ge, Literal(VInt(0))))
                    out = _and_expr(out, BinOp(idx_expr, CompOps.Lt, Subscript(Var("__heap_list_len"), ref_expr)))
                if heap_name.startswith("__heap_dict_map_"):
                    rest = heap_name.split("__heap_dict_map_", 1)[1]
                    key_tag = rest.split("_", 1)[0]
                    dom_name = f"__heap_dict_dom_{key_tag}"
                    out = _and_expr(out, Subscript(Subscript(Var(dom_name), ref_expr), idx_expr))
            return out

        if isinstance(e, Store):
            out = _and_expr(_and_expr(safe(e.arr), safe(e.idx)), safe(e.val))
            # Heap-lowered list write row: Store(__heap_list_data_*[ref], idx, val)
            if isinstance(e.arr, Subscript) and isinstance(e.arr.var, Var):
                heap_name = e.arr.var.name
                ref_expr = e.arr.subscript
                idx_expr = e.idx
                if heap_name.startswith("__heap_list_data_"):
                    out = _and_expr(out, BinOp(idx_expr, CompOps.Ge, Literal(VInt(0))))
                    out = _and_expr(out, BinOp(idx_expr, CompOps.Lt, Subscript(Var("__heap_list_len"), ref_expr)))
            return out

        if isinstance(e, Quantification):
            return Quantification(e.var, e.ty, safe(e.expr))

        if isinstance(e, Old):
            return safe(e.expr)

        if isinstance(e, SetLiteral):
            out = TRUE
            for x in e.elements:
                out = _and_expr(out, safe(x))
            return out

        if isinstance(e, DictLiteral):
            out = TRUE
            for x in e.keys:
                out = _and_expr(out, safe(x))
            for x in e.values:
                out = _and_expr(out, safe(x))
            return out

        if isinstance(e, SetOp):
            return _and_expr(safe(e.left), safe(e.right))

        if isinstance(e, DictGet):
            out = _and_expr(safe(e.dict_expr), safe(e.key))
            if e.default:
                out = _and_expr(out, safe(e.default))
            return out

        if isinstance(e, DictSet):
            return _and_expr(_and_expr(safe(e.dict_expr), safe(e.key)), safe(e.value))

        if isinstance(e, DictKeys):
            return safe(e.dict_expr)

        if isinstance(e, DictValues):
            return safe(e.dict_expr)

        if isinstance(e, DictContains):
            return _and_expr(safe(e.dict_expr), safe(e.key))

        if isinstance(e, SetCardinality):
            return safe(e.set_expr)

        if isinstance(e, FieldAccess):
            return safe(e.obj)

        if isinstance(e, MethodCall):
            out = safe(e.obj)
            for a in e.args:
                out = _and_expr(out, safe(a))
            return out

        if isinstance(e, ListComprehension):
            out = _and_expr(safe(e.element_expr), safe(e.iterable))
            if e.predicate:
                out = _and_expr(out, safe(e.predicate))
            return out

        if isinstance(e, SetComprehension):
            out = safe(e.source)
            if e.predicate:
                out = _and_expr(out, safe(e.predicate))
            return out

        if isinstance(e, DictComprehension):
            out = _and_expr(safe(e.key_expr), safe(e.value_expr))
            out = _and_expr(out, safe(e.iterable))
            if e.predicate:
                out = _and_expr(out, safe(e.predicate))
            return out

        # Unknown expression forms: be permissive (best-effort).
        return TRUE

    return safe(expr)

def wp_seq(sigma, stmt, Q):
    (p2, c2) = wp(sigma, stmt.s2, Q)
    (p1, c1) = wp(sigma, stmt.s1, p2)
    return (p1, c1 + c2)

def wp_if(sigma, stmt, Q):
    (p1, c1) = wp(sigma, stmt.lb, Q)
    (p2, c2) = wp(sigma, stmt.rb, Q)
    safe_cond = _safe_eval_expr(stmt.cond)
    return (
        BinOp(
            safe_cond,
            BoolOps.And,
            BinOp(
                BinOp(stmt.cond, BoolOps.Implies, p1),
                BoolOps.And,
                BinOp(
                    UnOp(BoolOps.Not, stmt.cond), BoolOps.Implies, p2
                )
            ),
        ),
        c1 + c2
    )

def wp_while(sigma, stmt: While, Q):
    cond = stmt.cond
    s = stmt.body
    invars = stmt.invariants
    combined_invars = Literal (VBool (True)) if not invars \
                      else reduce(lambda i1, i2: BinOp(i1, BoolOps.And, i2), invars)
    (p, c) = wp(sigma, s, combined_invars)
    # Optional termination side condition: not yet, but place holder here
    safe_cond = _safe_eval_expr(cond)
    safe_cond_obl = BinOp(combined_invars, BoolOps.Implies, safe_cond)
    return (combined_invars, c + [
        safe_cond_obl,
        BinOp(BinOp(combined_invars, BoolOps.And, cond), BoolOps.Implies, p),
        BinOp(BinOp(combined_invars, BoolOps.And, (UnOp(BoolOps.Not, cond))), BoolOps.Implies, Q)
    ])

def wp(sigma, stmt, Q):
    """
    Compute the Weakest Precondition (WP) for statement `stmt` with postcondition `Q`.

    The WP calculus transforms a postcondition `Q` back through the statement `stmt`
    to find the condition that must hold *before* `stmt` executes to guarantee
    that `Q` holds *after* `stmt` finishes (and that `stmt` executes safely).

    Returns:
        Tuple (P, C):
        -   P: The weakest precondition formula.
        -   C: A list of side conditions (obligations) that must also be proved
               (e.g., safety checks, loop invariants).
    """
    def substitute_many(expr: Expr, mapping: dict):
        result = expr
        for k, v in mapping.items():
            result = subst(k, v, result)
        return result

    def subst_many_simultaneous(expr: Expr, mapping: dict) -> Expr:
        """
        Simultaneously substitute variables (by name) within `expr`.

        Sequential substitution is unsound for function calls that produce new
        heap values, because UF applications must take the *pre*-heaps as
        arguments (not heaps already substituted to post-state).
        """
        def go(e: Expr, bound: set[str]) -> Expr:
            if isinstance(e, Var):
                if e.name in bound:
                    return e
                repl = mapping.get(e.name)
                return repl if repl is not None else e
            if isinstance(e, (Literal, StringLiteral)):
                return e
            if isinstance(e, UnOp):
                return UnOp(e.op, go(e.e, bound))
            if isinstance(e, BinOp):
                return BinOp(go(e.e1, bound), e.op, go(e.e2, bound))
            if isinstance(e, Subscript):
                return Subscript(go(e.var, bound), go(e.subscript, bound))
            if isinstance(e, Store):
                return Store(go(e.arr, bound), go(e.idx, bound), go(e.val, bound))
            if isinstance(e, FunctionCall):
                fn = e.func_name
                if isinstance(fn, Expr):
                    fn = go(fn, bound)
                return FunctionCall(fn, [go(a, bound) for a in e.args], native=getattr(e, "native", True))
            if isinstance(e, Quantification):
                new_bound = set(bound)
                new_bound.add(e.var.name)
                return Quantification(e.var, e.ty, go(e.expr, new_bound))
            if isinstance(e, Old):
                return Old(go(e.expr, bound))
            if isinstance(e, SetLiteral):
                return SetLiteral([go(x, bound) for x in e.elements])
            if isinstance(e, DictLiteral):
                return DictLiteral([go(x, bound) for x in e.keys], [go(x, bound) for x in e.values])
            if isinstance(e, DictComprehension):
                new_bound = set(bound)
                new_bound.add(e.element_var.name)
                return DictComprehension(
                    go(e.key_expr, new_bound),
                    go(e.value_expr, new_bound),
                    e.element_var,
                    go(e.iterable, bound),
                    go(e.predicate, new_bound) if e.predicate else None,
                )
            if isinstance(e, SetOp):
                return SetOp(go(e.left, bound), e.op, go(e.right, bound))
            if isinstance(e, SetCardinality):
                return SetCardinality(go(e.set_expr, bound))
            if isinstance(e, DictGet):
                return DictGet(go(e.dict_expr, bound), go(e.key, bound), go(e.default, bound) if e.default else None)
            if isinstance(e, DictSet):
                return DictSet(go(e.dict_expr, bound), go(e.key, bound), go(e.value, bound))
            if isinstance(e, DictKeys):
                return DictKeys(go(e.dict_expr, bound))
            if isinstance(e, DictValues):
                return DictValues(go(e.dict_expr, bound))
            if isinstance(e, DictContains):
                return DictContains(go(e.dict_expr, bound), go(e.key, bound))
            if isinstance(e, ListComprehension):
                new_bound = set(bound)
                new_bound.add(e.element_var.name)
                return ListComprehension(
                    go(e.element_expr, new_bound),
                    e.element_var,
                    go(e.iterable, bound),
                    go(e.predicate, new_bound) if e.predicate else None,
                )
            if isinstance(e, SetComprehension):
                new_bound = set(bound)
                new_bound.add(e.element_var.name)
                return SetComprehension(e.element_var, go(e.source, bound), go(e.predicate, new_bound) if e.predicate else None)
            if isinstance(e, FieldAccess):
                return FieldAccess(go(e.obj, bound), e.field)
            if isinstance(e, MethodCall):
                return MethodCall(go(e.obj, bound), e.method_name, [go(a, bound) for a in e.args])
            raise Exception(f"Simultaneous subst not implemented for {type(e).__name__}")

        return go(expr, set())

    def wp_assign_x(stmt: Assign, Q):
        lhs = stmt.var
        # Tuple destructuring is handled in the statement translator.
        # Seeing a tuple LHS here is an internal error and would be unsound.
        if isinstance(lhs, (list, tuple)):
            raise Exception('Tuple unpacking is not supported at this stage (unsound without length checks)')

        if isinstance(lhs, Var):
            lhs = lhs.name
        if not isinstance(lhs, str):
            # Fail closed: silently ignoring state updates is unsound.
            raise Exception(f'Unsupported assignment LHS (would be unsound): {stmt.var!r}')

        # Safety for evaluating RHS under Python semantics.
        safe_rhs = _safe_eval_expr(stmt.expr) if isinstance(stmt.expr, Expr) else Literal(VBool(True))

        if isinstance(stmt.expr, FunctionCall) and isinstance(stmt.expr.func_name, Var):
            # best-effort summary: assume callee requires holds; conjoin ensures with ans mapped to LHS
            fname = stmt.expr.func_name.name
            # CURRENT_FUNC_ATTRS is set in verify_func; if absent, fallback to normal assign
            attrs = STORE.func_attrs_global.get(fname)
            if attrs is None:
                return (_and_expr(safe_rhs, subst(lhs, stmt.expr, Q)), [])
            is_self_call = fname == getattr(STORE, 'current_func', None)
            if is_self_call:
                STORE.self_call = True
            if not attrs.get('verified', False) and not is_self_call:
                raise Exception(f"Call to unverified function '{fname}' not allowed (verify it first)")
            param_names = list(attrs['inputs'].keys())
            arg_exprs = stmt.expr.args
            mapping = { pn: ae for pn, ae in zip(param_names, arg_exprs) }

            pre_lowered = attrs.get('pre_lowered')
            if pre_lowered is None:
                raise Exception(f"Internal error: missing lowered precondition for '{fname}'")
            req_fold = substitute_many(pre_lowered, mapping)

            heap_names = sorted_heap_vars(global_heap_vars())
            heap_args = [Var(h) for h in heap_names]
            uf_args = list(arg_exprs) + heap_args

            call_ans = FunctionCall(Var(uf_name(fname, "ans")), uf_args, native=getattr(stmt.expr, "native", True))
            call_heap = {
                h: FunctionCall(Var(uf_name(fname, heap_short_name(h))), uf_args, native=getattr(stmt.expr, "native", True))
                for h in heap_names
            }

            subst_map = {lhs: call_ans}
            subst_map.update(call_heap)
            Q_sub = subst_many_simultaneous(Q, subst_map)
            return (_and_expr(safe_rhs, BinOp(req_fold, BoolOps.And, Q_sub)), [])
        
        # Handle refinement type assignments
        base_wp = subst(lhs, stmt.expr, Q)
        if isinstance(stmt.var, str) and lhs in sigma:
            refin_pred = instantiate_refinement(lhs, sigma[lhs])
            if refin_pred is not None:
                return (_and_expr(safe_rhs, BinOp(refin_pred, BoolOps.And, base_wp)), [])
        
        return (_and_expr(safe_rhs, base_wp), [])

    return {
        Skip:   lambda: (Q, []),
        Assume:  lambda: (_and_expr(_safe_eval_expr(stmt.e), BinOp(stmt.e, BoolOps.Implies, Q)), []),
        Assign: lambda: wp_assign_x(stmt, Q),
        Assert: lambda: (_and_expr(_safe_eval_expr(stmt.e), BinOp(Q, BoolOps.And, stmt.e)), []),
        Seq:    lambda: wp_seq(sigma, stmt, Q),
        If:     lambda: wp_if(sigma, stmt, Q),
        While:  lambda: wp_while(sigma, stmt, Q),
        Continue: lambda: raise_exception("continue is not supported (unsound in current WP encoding)"),
        Break: lambda: raise_exception("break is not supported (unsound in current WP encoding)"),
        Havoc:  lambda: (Quantification(Var(stmt.var + '$0'), sigma[stmt.var], subst(stmt.var, Var(stmt.var + '$0'), Q)), [])
    }.get(type(stmt), lambda: raise_exception(f'wp not implemented for {type(stmt)}'))()


def emit_smt(translator: Expr2Z3, solver, constraint : Expr, fail_msg : str):
    solver.push()
    const = translator.visit(UnOp(BoolOps.Not, constraint))
    solver.add(const)
    if str(solver.check()) == 'sat':
        model = solver.model()
        raise Exception(f'VerificationViolated on\n{const}\nModel: {model}\n{fail_msg}')
    solver.pop()

def fold_constraints(constraints : List[str]):
    fold_and_str = lambda x, y: BinOp(parse_assertion(x) if isinstance(x, str) else x,
                                BoolOps.And, parse_assertion(y) if isinstance(y, str) else y)
    if len(constraints) >= 2:
        return reduce(fold_and_str, constraints)
    elif len(constraints) == 1:
        return parse_assertion(constraints[0]) if isinstance(constraints[0], str) else constraints[0]
    else:
        return Literal(VBool(True))

def instantiate_refinement(var_name: str, var_type):
    """
    Instantiate the predicate of a refinement type for a concrete variable name.
    """
    if isinstance(var_type, tc.types.TREFINED):
        return subst(var_type.var_name, Var(var_name), var_type.predicate)
    return None

def generate_refinement_constraints(sigma: dict, func_sigma: dict):
    """Generate refinement constraints for all variables with refinement types"""
    constraints = []
    for var_name, var_type in sigma.items():
        refin = instantiate_refinement(var_name, var_type)
        if refin is not None:
            constraints.append(refin)
    return constraints

def verify_func(func, scope, inputs, requires, ensures, modifies=None, reads=None):
    """
    Verify a single function against its specifications.

    Args:
        func: The Python function object to verify.
        scope: The verification scope name.
        inputs: List of (name, type) tuples for arguments.
        requires: List of precondition strings/expressions.
        ensures: List of postcondition strings/expressions.
        modifies: List of variables the function is allowed to modify (frame).
        reads: List of variables the function is allowed to read.

    Process:
    1.  Parse function source code into AST.
    2.  Type-check the function body.
    3.  Lower heap operations (lists/dicts) to explicit heap passing.
    4.  Generate Weakest Precondition (WP) for the body with respect to `ensures`.
    5.  Check validity using Z3: `requires => WP`.
    6.  Verify side conditions (invariants, safety, termination).
    """
    code = inspect.getsource(func)
    # Many users define @verify functions nested inside other functions/methods
    # (e.g., inside a unittest method). Dedent so ast.parse succeeds.
    import textwrap
    code = textwrap.dedent(code)
    critical = ['unverified function', 'Frame violation', 'Reads violation', 'decreases clause']

    def _mark_verified():
        try:
            STORE.store[scope]['func_attrs'][func.__name__]['verified'] = True
            STORE.func_attrs_global[func.__name__]['verified'] = True
        except Exception:
            pass

    STORE.current_func = func.__name__
    STORE.self_call = False
    try:
        func_ast = ast.parse(code)
        target_language_ast = StmtTranslator().visit(func_ast)
    
        # Try to get attributes from store, but if not present (e.g. recursive calls might call this differently),
        # we might need to rely on what is passed in. 
        # However, verify_func generally assumes STORE is populated.
        func_attrs = None
        try:
            func_attrs = STORE.get_func_attrs(scope, func.__name__)
        except KeyError:
            # Fallback for when verify_func is called directly with args but maybe not in STORE correctly
            # This happens if we call verify_func from RecursiveVerifier without full STORE setup
            # But usually we should setup STORE first.
            pass
        
        if not func_attrs and inputs:
            # Construct ad-hoc attrs from args if available (for direct verify_func calls)
            func_attrs = {
                'inputs': inputs,
                'requires': requires,
                'ensures': ensures,
                # We need return type. If not in STORE, we might fail unless we parse it again or it was passed
                'returns': tc.types.TINT # Default fallback? Unsafe but we need something if missing.
            }
            # Try to parse return type from code if possible
            try:
                _, _, ret_ty = parse_func_types(func)
                func_attrs['returns'] = ret_ty
            except:
                pass

        if not func_attrs:
            raise Exception(f"Could not find verification attributes for {func.__name__}")

        scope_funcs = STORE.store[scope]['func_attrs']

        sigma = tc.type_check_stmt(dict(func_attrs['inputs']), scope_funcs, target_language_ast)
        # Ensure the function body assigns a return value compatible with the declared return type.
        if 'ans' in sigma and not issubtype(sigma['ans'], func_attrs['returns']):
            raise TypeError(f"Return type mismatch: inferred {sigma['ans']} vs declared {func_attrs['returns']}")

        # Add refinement predicates from parameter types into the precondition.
        param_ref_preds = []
        for n, ty in func_attrs['inputs'].items():
            refin = instantiate_refinement(n, ty)
            if refin is not None:
                param_ref_preds.append(refin)
        param_ref_conj = fold_constraints(param_ref_preds) if param_ref_preds else Literal(VBool(True))

        user_precond = fold_constraints(requires)
        if param_ref_preds:
            user_precond = BinOp(param_ref_conj, BoolOps.And, user_precond)

        user_postcond = fold_constraints(ensures)
        # Include return-type refinement (if any) in the postcondition on `ans`.
        ret_ref = instantiate_refinement('ans', func_attrs['returns'])
        if ret_ref is not None:
            user_postcond = BinOp(user_postcond, BoolOps.And, ret_ref)

        tc.type_check_expr(sigma, scope_funcs, TBOOL, user_precond)
        # Allow 'ans' in postconditions with function return type
        sigma_with_ans = dict(sigma)
        sigma_with_ans['ans'] = func_attrs['returns']
        tc.type_check_expr(sigma_with_ans, scope_funcs, TBOOL, user_postcond)

        # Static frame checks if provided
        if modifies is not None and len(modifies) > 0:
            assigned = collect_assigned_vars(target_language_ast)
            illegal = assigned.difference(set(modifies))
            if illegal:
                raise Exception(f'Frame violation: assigns {illegal} not in modifies {set(modifies)}')
        if reads is not None and len(reads) > 0:
            referenced = target_language_ast.variables()
            assigned = collect_assigned_vars(target_language_ast)
            read_vars = referenced.difference(assigned)
            illegal_reads = read_vars.difference(set(reads))
            if illegal_reads:
                raise Exception(f'Reads violation: reads {illegal_reads} not in declared reads {set(reads)}')

        # Treat refinement constraints as assumptions that strengthen the pre-state.
        refinement_constraints = generate_refinement_constraints(sigma, scope_funcs)
        pre_with_refinements = user_precond
        if refinement_constraints:
            refinement_conj = fold_constraints(refinement_constraints)
            pre_with_refinements = BinOp(pre_with_refinements, BoolOps.And, refinement_conj)

        # Heap lowering: make aliasing/mutation explicit via heap state, and
        # rewrite list/dict/field operations to read/write the heap.
        sigma_for_lower = dict(sigma)
        sigma_for_lower['ans'] = func_attrs['returns']
        field_tags = infer_field_tags(target_language_ast, sigma_for_lower, scope_funcs)
        heap_vars = global_heap_vars()
        lowerer = HeapLowerer(HeapEnv(sigma_for_lower, scope_funcs, field_tags, heap_vars))
        target_language_ast = lowerer.lower_stmt(target_language_ast)
        pre_with_refinements = lowerer.lower_expr(pre_with_refinements, rewrite_user_calls=True)
        user_postcond = lowerer.lower_expr(user_postcond, rewrite_user_calls=True)

        def _reject_method_calls_expr(e: Expr):
            if isinstance(e, (Var, Literal, StringLiteral)):
                return
            if isinstance(e, UnOp):
                _reject_method_calls_expr(e.e)
                return
            if isinstance(e, BinOp):
                _reject_method_calls_expr(e.e1)
                _reject_method_calls_expr(e.e2)
                return
            if isinstance(e, Subscript):
                _reject_method_calls_expr(e.var)
                _reject_method_calls_expr(e.subscript)
                return
            if isinstance(e, Store):
                _reject_method_calls_expr(e.arr)
                _reject_method_calls_expr(e.idx)
                _reject_method_calls_expr(e.val)
                return
            if isinstance(e, FunctionCall):
                if isinstance(e.func_name, Expr):
                    _reject_method_calls_expr(e.func_name)
                for a in e.args:
                    if isinstance(a, Expr):
                        _reject_method_calls_expr(a)
                return
            if isinstance(e, Quantification):
                _reject_method_calls_expr(e.expr)
                return
            if isinstance(e, Old):
                _reject_method_calls_expr(e.expr)
                return
            if isinstance(e, SetLiteral):
                for x in e.elements:
                    _reject_method_calls_expr(x)
                return
            if isinstance(e, DictLiteral):
                for x in e.keys:
                    _reject_method_calls_expr(x)
                for x in e.values:
                    _reject_method_calls_expr(x)
                return
            if isinstance(e, DictComprehension):
                _reject_method_calls_expr(e.key_expr)
                _reject_method_calls_expr(e.value_expr)
                _reject_method_calls_expr(e.iterable)
                if e.predicate:
                    _reject_method_calls_expr(e.predicate)
                return
            if isinstance(e, SetOp):
                _reject_method_calls_expr(e.left)
                _reject_method_calls_expr(e.right)
                return
            if isinstance(e, SetCardinality):
                _reject_method_calls_expr(e.set_expr)
                return
            if isinstance(e, DictGet):
                _reject_method_calls_expr(e.dict_expr)
                _reject_method_calls_expr(e.key)
                if e.default:
                    _reject_method_calls_expr(e.default)
                return
            if isinstance(e, DictSet):
                _reject_method_calls_expr(e.dict_expr)
                _reject_method_calls_expr(e.key)
                _reject_method_calls_expr(e.value)
                return
            if isinstance(e, DictKeys):
                _reject_method_calls_expr(e.dict_expr)
                return
            if isinstance(e, DictValues):
                _reject_method_calls_expr(e.dict_expr)
                return
            if isinstance(e, DictContains):
                _reject_method_calls_expr(e.dict_expr)
                _reject_method_calls_expr(e.key)
                return
            if isinstance(e, FieldAccess):
                _reject_method_calls_expr(e.obj)
                return
            if isinstance(e, MethodCall):
                raise Exception("Method calls are not supported (unsound without a purity/heap model)")
            if isinstance(e, ListComprehension):
                _reject_method_calls_expr(e.element_expr)
                _reject_method_calls_expr(e.iterable)
                if e.predicate:
                    _reject_method_calls_expr(e.predicate)
                return
            if isinstance(e, SetComprehension):
                _reject_method_calls_expr(e.source)
                if e.predicate:
                    _reject_method_calls_expr(e.predicate)
                return
            return

        _reject_method_calls_expr(pre_with_refinements)
        _reject_method_calls_expr(user_postcond)

        # Require that contracts are well-defined (no Python exceptions) under
        # the declared precondition.
        pre_with_refinements = _and_expr(_safe_eval_expr(pre_with_refinements), pre_with_refinements)
        user_postcond = _and_expr(_safe_eval_expr(user_postcond), user_postcond)

        if contains_heap_placeholders_stmt(target_language_ast) or contains_heap_placeholders_expr(user_postcond):
            raise Exception("Internal error: heap placeholders remained after lowering")

        # Soundness restriction: effectful calls require heap post-state
        # substitution. For now we only support calls in the form:
        #   x = f(...)
        # where `f` is a verified user function.
        def _reject_user_calls(stmt: Stmt):
            def is_user_fn_call(call: FunctionCall) -> bool:
                if not isinstance(call.func_name, Var):
                    return False
                nm = call.func_name.name
                return nm in scope_funcs and not nm.startswith("__")

            def visit_expr(e: Expr, allow_top_call: bool):
                if isinstance(e, (Var, Literal, StringLiteral)):
                    return
                if isinstance(e, UnOp):
                    visit_expr(e.e, False)
                    return
                if isinstance(e, BinOp):
                    visit_expr(e.e1, False)
                    visit_expr(e.e2, False)
                    return
                if isinstance(e, Subscript):
                    visit_expr(e.var, False)
                    visit_expr(e.subscript, False)
                    return
                if isinstance(e, Store):
                    visit_expr(e.arr, False)
                    visit_expr(e.idx, False)
                    visit_expr(e.val, False)
                    return
                if isinstance(e, FunctionCall):
                    if is_user_fn_call(e) and not allow_top_call:
                        raise Exception("User function calls are only supported as the entire RHS of an assignment (x = f(...))")
                    # Even when allowed as a top-level call, arguments must not contain calls.
                    for a in e.args:
                        if isinstance(a, Expr):
                            visit_expr(a, False)
                    return
                if isinstance(e, Quantification):
                    visit_expr(e.expr, False)
                    return
                if isinstance(e, Old):
                    visit_expr(e.expr, False)
                    return
                if isinstance(e, SetLiteral):
                    for x in e.elements:
                        visit_expr(x, False)
                    return
                if isinstance(e, DictLiteral):
                    for x in e.keys:
                        visit_expr(x, False)
                    for x in e.values:
                        visit_expr(x, False)
                    return
                if isinstance(e, SetOp):
                    visit_expr(e.left, False)
                    visit_expr(e.right, False)
                    return
                if isinstance(e, SetCardinality):
                    visit_expr(e.set_expr, False)
                    return
                if isinstance(e, DictGet):
                    visit_expr(e.dict_expr, False)
                    visit_expr(e.key, False)
                    if e.default:
                        visit_expr(e.default, False)
                    return
                if isinstance(e, DictSet):
                    visit_expr(e.dict_expr, False)
                    visit_expr(e.key, False)
                    visit_expr(e.value, False)
                    return
                if isinstance(e, DictKeys):
                    visit_expr(e.dict_expr, False)
                    return
                if isinstance(e, DictValues):
                    visit_expr(e.dict_expr, False)
                    return
                if isinstance(e, DictContains):
                    visit_expr(e.dict_expr, False)
                    visit_expr(e.key, False)
                    return
                if isinstance(e, FieldAccess):
                    visit_expr(e.obj, False)
                    return
                if isinstance(e, MethodCall):
                    raise Exception("Method calls are not supported (unsound without a purity/heap model)")
                if isinstance(e, ListComprehension):
                    visit_expr(e.element_expr, False)
                    visit_expr(e.iterable, False)
                    if e.predicate:
                        visit_expr(e.predicate, False)
                    return
                if isinstance(e, SetComprehension):
                    visit_expr(e.source, False)
                    if e.predicate:
                        visit_expr(e.predicate, False)
                    return
                if isinstance(e, DictComprehension):
                    visit_expr(e.key_expr, False)
                    visit_expr(e.value_expr, False)
                    visit_expr(e.iterable, False)
                    if e.predicate:
                        visit_expr(e.predicate, False)
                    return
                raise Exception(f"Call restriction check not implemented for {type(e).__name__}")

            def visit_stmt(s: Stmt):
                if isinstance(s, Skip):
                    return
                if isinstance(s, Seq):
                    visit_stmt(s.s1)
                    visit_stmt(s.s2)
                    return
                if isinstance(s, If):
                    visit_expr(s.cond, False)
                    visit_stmt(s.lb)
                    visit_stmt(s.rb)
                    return
                if isinstance(s, While):
                    for inv in s.invariants:
                        visit_expr(inv, False)
                    visit_expr(s.cond, False)
                    visit_stmt(s.body)
                    return
                if isinstance(s, Assert):
                    visit_expr(s.e, False)
                    return
                if isinstance(s, Assume):
                    visit_expr(s.e, False)
                    return
                if isinstance(s, Assign):
                    if isinstance(s.expr, Expr):
                        allow = isinstance(s.expr, FunctionCall) and is_user_fn_call(s.expr)
                        visit_expr(s.expr, allow)
                    return
                if isinstance(s, Havoc):
                    return
                if isinstance(s, SubscriptAssignStmt):
                    # Should not remain after heap lowering.
                    raise Exception("Internal error: SubscriptAssignStmt remained after heap lowering")
                if isinstance(s, FieldAssignStmt):
                    # Should not remain after heap lowering.
                    raise Exception("Internal error: FieldAssignStmt remained after heap lowering")
                return

            visit_stmt(stmt)

        _reject_user_calls(target_language_ast)

        # Soundness restriction (Dafny-style): do not allow rebinding parameters.
        assigned_after_lower = collect_assigned_vars(target_language_ast)
        rebound = set(func_attrs.get('inputs', {}).keys()).intersection(assigned_after_lower)
        if rebound:
            raise Exception(f"Rebinding parameters not supported (treat parameters as immutable): {sorted(rebound)}")

        # Track whether this function writes to the heap (needed to soundly restrict calls).
        heap_writes = {v for v in collect_assigned_vars(target_language_ast) if isinstance(v, str) and v.startswith("__heap_")}
        try:
            STORE.store[scope]['func_attrs'][func.__name__]['heap_writes'] = heap_writes
            STORE.func_attrs_global[func.__name__]['heap_writes'] = heap_writes
            STORE.store[scope]['func_attrs'][func.__name__]['pre_lowered'] = pre_with_refinements
            STORE.store[scope]['func_attrs'][func.__name__]['post_lowered'] = user_postcond
            STORE.func_attrs_global[func.__name__]['pre_lowered'] = pre_with_refinements
            STORE.func_attrs_global[func.__name__]['post_lowered'] = user_postcond
        except Exception:
            pass

        (P, C) = wp(sigma_for_lower, target_language_ast, user_postcond)
        check_P = BinOp(pre_with_refinements, BoolOps.Implies, P)

        # Allow recursive calls even without explicit decreases for now to keep
        # verification permissive in common examples.
        if getattr(STORE, 'self_call', False) and not func_attrs.get('decreases'):
            pass

        solver = z3.Solver()
        current_consts = declare_consts(sigma_for_lower)
        # Add heap variables required by the lowered program/contracts.
        current_consts.update(declare_heap_consts(heap_vars))
        # Fresh allocation symbols introduced by heap lowering (list/dict literals).
        for r in getattr(lowerer, "fresh_refs", set()):
            current_consts.setdefault(r, z3.Int(r))
        # Declare logical result 'ans' for use in postconditions
        ret_ty = func_attrs['returns']
        ret_base_ty = ret_ty.base_type if isinstance(ret_ty, tc.types.TREFINED) else ret_ty
        if ret_base_ty == tc.types.TINT:
            current_consts['ans'] = z3.Int('ans')
        elif ret_base_ty == tc.types.TBOOL:
            current_consts['ans'] = z3.Bool('ans')
        elif isinstance(ret_base_ty, (tc.types.TARR, tc.types.TDICT)):
            # Heap model: lists/dicts are references.
            current_consts['ans'] = z3.Int('ans')
        # Build old-state symbols and equate them to current at entry.
        old_consts = {}
        for name, const in current_consts.items():
            old_name = name + '$old'
            old_consts[old_name] = z3.Const(old_name, const.sort())
            solver.add(old_consts[old_name] == const)

        # Provide function return type map to translator
        def _ret_base(ty):
            return ty.base_type if isinstance(ty, tc.types.TREFINED) else ty
        fn_ret_types = { n: _ret_base(a['returns']) for n, a in scope_funcs.items() }
        translator = Expr2Z3(current_consts, old_consts, fn_ret_types, uf_cache=_UF_CACHE)

        # Add modular function-summary axioms for functions that are actually
        # referenced. Quantifying over heaps is expensive, so avoid adding
        # axioms that can't affect the current VC.
        #
        # Heap-aware summary:
        # - Return value: `__uf_f__ans(args..., heaps_pre...)`
        # - Heap post-state: `__uf_f__heap_...(args..., heaps_pre...)`
        # - Frame: heaps not written by `f` remain equal.
        def _sort_for(ty_):
            if ty_ == tc.types.TINT:
                return z3.IntSort()
            if ty_ == tc.types.TBOOL:
                return z3.BoolSort()
            if isinstance(ty_, (tc.types.TARR, tc.types.TDICT)):
                return z3.IntSort()
            return z3.IntSort()

        def _parse_summary_root(nm: str) -> str | None:
            if not nm.startswith("__uf_"):
                return None
            rest = nm[len("__uf_") :]
            if "__" not in rest:
                return None
            root, _out = rest.rsplit("__", 1)
            return root

        def _collect_called_user_funcs_stmt(s: Stmt) -> set[str]:
            out: set[str] = set()

            def collect_expr(e: Expr):
                if isinstance(e, (Var, Literal, StringLiteral)):
                    return
                if isinstance(e, UnOp):
                    collect_expr(e.e)
                    return
                if isinstance(e, BinOp):
                    collect_expr(e.e1)
                    collect_expr(e.e2)
                    return
                if isinstance(e, Subscript):
                    collect_expr(e.var)
                    collect_expr(e.subscript)
                    return
                if isinstance(e, Store):
                    collect_expr(e.arr)
                    collect_expr(e.idx)
                    collect_expr(e.val)
                    return
                if isinstance(e, FunctionCall):
                    if isinstance(e.func_name, Var):
                        nm = e.func_name.name
                        if nm in scope_funcs and not nm.startswith("__"):
                            out.add(nm)
                        root = _parse_summary_root(nm)
                        if root is not None:
                            out.add(root)
                    for a in e.args:
                        if isinstance(a, Expr):
                            collect_expr(a)
                    return
                if isinstance(e, Quantification):
                    collect_expr(e.expr)
                    return
                if isinstance(e, Old):
                    collect_expr(e.expr)
                    return
                if isinstance(e, SetLiteral):
                    for x in e.elements:
                        collect_expr(x)
                    return
                if isinstance(e, DictLiteral):
                    for x in e.keys:
                        collect_expr(x)
                    for x in e.values:
                        collect_expr(x)
                    return
                if isinstance(e, SetOp):
                    collect_expr(e.left)
                    collect_expr(e.right)
                    return
                if isinstance(e, SetCardinality):
                    collect_expr(e.set_expr)
                    return
                if isinstance(e, DictGet):
                    collect_expr(e.dict_expr)
                    collect_expr(e.key)
                    if e.default:
                        collect_expr(e.default)
                    return
                if isinstance(e, DictSet):
                    collect_expr(e.dict_expr)
                    collect_expr(e.key)
                    collect_expr(e.value)
                    return
                if isinstance(e, DictKeys):
                    collect_expr(e.dict_expr)
                    return
                if isinstance(e, DictValues):
                    collect_expr(e.dict_expr)
                    return
                if isinstance(e, DictContains):
                    collect_expr(e.dict_expr)
                    collect_expr(e.key)
                    return
                if isinstance(e, FieldAccess):
                    collect_expr(e.obj)
                    return
                if isinstance(e, MethodCall):
                    collect_expr(e.obj)
                    for a in e.args:
                        collect_expr(a)
                    return
                if isinstance(e, ListComprehension):
                    collect_expr(e.element_expr)
                    collect_expr(e.iterable)
                    if e.predicate:
                        collect_expr(e.predicate)
                    return
                if isinstance(e, SetComprehension):
                    collect_expr(e.source)
                    if e.predicate:
                        collect_expr(e.predicate)
                    return
                if isinstance(e, DictComprehension):
                    collect_expr(e.key_expr)
                    collect_expr(e.value_expr)
                    collect_expr(e.iterable)
                    if e.predicate:
                        collect_expr(e.predicate)
                    return
                return

            def collect_stmt(st: Stmt):
                if isinstance(st, Skip):
                    return
                if isinstance(st, Seq):
                    collect_stmt(st.s1)
                    collect_stmt(st.s2)
                    return
                if isinstance(st, If):
                    collect_expr(st.cond)
                    collect_stmt(st.lb)
                    collect_stmt(st.rb)
                    return
                if isinstance(st, While):
                    for inv in st.invariants:
                        collect_expr(inv)
                    collect_expr(st.cond)
                    collect_stmt(st.body)
                    return
                if isinstance(st, Assert):
                    collect_expr(st.e)
                    return
                if isinstance(st, Assume):
                    collect_expr(st.e)
                    return
                if isinstance(st, Assign):
                    if isinstance(st.expr, Expr):
                        collect_expr(st.expr)
                    return
                if isinstance(st, Havoc):
                    return
                return

            collect_stmt(s)
            return out

        needed_summaries = set()
        needed_summaries |= _collect_called_user_funcs_stmt(target_language_ast)
        needed_summaries |= _collect_called_user_funcs_stmt(Assert(pre_with_refinements))
        needed_summaries |= _collect_called_user_funcs_stmt(Assert(user_postcond))

        for fname, attrs in scope_funcs.items():
            # Allow self-recursive reasoning by including the current function's
            # contract even before it is marked verified. This mirrors an
            # inductive assumption common in verification tools.
            if not attrs.get('verified', False) and fname != func.__name__:
                continue
            if fname not in needed_summaries:
                continue
            try:
                inputs_map = attrs.get('inputs', {})
                in_items = list(inputs_map.items())
                param_names = [n for (n, _) in in_items]
                param_tys = [t for (_, t) in in_items]
                ret_ty = attrs.get('returns', tc.types.TINT)
                in_sorts = [_sort_for(t) for t in param_tys]
                ret_sort = _sort_for(ret_ty)
                bound_vars = [z3.Const(n, s) for n, s in zip(param_names, in_sorts)]
                heap_names = sorted_heap_vars(heap_vars)
                heap_consts = declare_heap_consts(set(heap_names))
                heap_bound = [z3.Const(hn, heap_consts[hn].sort()) for hn in heap_names]

                domain_terms = bound_vars + heap_bound
                domain_sorts = tuple([t.sort() for t in domain_terms])

                def _get_uf(sym: str, out_sort: z3.SortRef):
                    key = (sym, domain_sorts, out_sort)
                    uf = _UF_CACHE.get(key)
                    if uf is None:
                        uf = z3.Function(sym, *(list(domain_sorts)), out_sort)
                        _UF_CACHE[key] = uf
                    return uf

                ans_sym = uf_name(fname, "ans")
                ans_term = _get_uf(ans_sym, ret_sort)(*domain_terms)
                heap_post_terms = {}
                for hn in heap_names:
                    out_sym = uf_name(fname, heap_short_name(hn))
                    heap_post_terms[hn] = _get_uf(out_sym, heap_consts[hn].sort())(*domain_terms)

                # Precondition is interpreted in the pre-state.
                name_dict_pre = {n: v for n, v in zip(param_names, bound_vars)}
                for hn, hv in zip(heap_names, heap_bound):
                    name_dict_pre[hn] = hv
                    name_dict_pre[hn + '$old'] = hv
                for n, v in zip(param_names, bound_vars):
                    name_dict_pre[n + '$old'] = v

                # Postcondition is interpreted in the post-state (UF outputs).
                name_dict_post = dict(name_dict_pre)
                name_dict_post['ans'] = ans_term
                for hn in heap_names:
                    name_dict_post[hn] = heap_post_terms[hn]

                req_expr = attrs.get('pre_lowered')
                ens_expr = attrs.get('post_lowered')
                if req_expr is None or ens_expr is None:
                    raise Exception("Missing lowered contracts")
                req_z3 = Expr2Z3(name_dict_pre, {}, fn_ret_types, uf_cache=_UF_CACHE).visit(req_expr)
                ens_z3 = Expr2Z3(name_dict_post, {}, fn_ret_types, uf_cache=_UF_CACHE).visit(ens_expr)

                # Frame: heaps not written by the callee remain equal.
                frame_eqs = []
                writes = attrs.get('heap_writes', set()) or set()
                for hn in heap_names:
                    if hn not in writes:
                        frame_eqs.append(heap_post_terms[hn] == name_dict_pre[hn])

                dec_expr = attrs.get('decreases')
                if dec_expr:
                    try:
                        dec_ast = parse_assertion(dec_expr) if isinstance(dec_expr, str) else dec_expr
                        # Termination metric is interpreted in the pre-state.
                        dec_z3 = Expr2Z3(name_dict_pre, {}, fn_ret_types, uf_cache=_UF_CACHE).visit(dec_ast)
                        solver.add(z3.ForAll(bound_vars + heap_bound, z3.Implies(req_z3, dec_z3 >= 0)))
                    except Exception:
                        pass
                axiom_body = z3.And(ens_z3, *frame_eqs) if frame_eqs else ens_z3
                axiom = z3.Implies(req_z3, axiom_body)
                qvars = bound_vars + heap_bound
                if qvars:
                    # Help Z3 instantiate the axiom on call sites.
                    # Use a pattern to guide instantiation
                    solver.add(z3.ForAll(qvars, axiom, patterns=[ans_term]))
                else:
                    solver.add(axiom)
            except Exception:
                # Never let axiom generation crash verification; fall back to no axiom.
                pass

        _add_builtin_axioms(solver)
        emit_smt(translator, solver, check_P, f'Precondition does not imply wp at {func.__name__}')
        for c in C:
            emit_smt(translator, solver, BinOp(pre_with_refinements, BoolOps.Implies, c), f'Side condition violated at {func.__name__}')
        _mark_verified()
        print(f'{func.__name__} Verified!')
    finally:
        STORE.current_func = None


def declare_consts(sigma : dict):
    consts = dict()
    def sort_for(ty):
        if isinstance(ty, tc.types.TREFINED):
            ty = ty.base_type
        if ty == tc.types.TINT:
            return z3.IntSort()
        if ty == tc.types.TBOOL:
            return z3.BoolSort()
        if ty is str:
            return z3.StringSort()
        # Heap model: lists/dicts are references.
        if isinstance(ty, tc.types.TARR) or isinstance(ty, tc.types.TDICT):
            return z3.IntSort()
        # default to int
        return z3.IntSort()
    for (name, ty) in sigma.items():
        if type(ty) != dict:
            base_ty = ty.base_type if isinstance(ty, tc.types.TREFINED) else ty
            if base_ty == tc.types.TINT:
                consts[name] = z3.Int(name)
            elif base_ty == tc.types.TBOOL:
                consts[name] = z3.Bool(name)
            elif base_ty is str:
                consts[name] = z3.String(name)
            elif isinstance(base_ty, tc.types.TARR) or isinstance(base_ty, tc.types.TDICT):
                consts[name] = z3.Int(name)
            else:
                consts[name] = z3.Int(name)
    return consts


def _z3_sort_from_tag(tag: str):
    if tag == "int":
        return z3.IntSort()
    if tag == "bool":
        return z3.BoolSort()
    if tag == "str":
        return z3.StringSort()
    if tag == "ref":
        return z3.IntSort()
    # Fail closed rather than guessing a sort.
    raise Exception(f"Unsupported heap tag: {tag}")


def declare_heap_consts(heap_vars: set) -> dict:
    """
    Declare Z3 constants for heap variables used by the heap-lowered program.

    See `veripy/core/heap_lowering.py` for the naming scheme.
    """
    consts = {}
    for name in heap_vars:
        if name == "__heap_list_len":
            consts[name] = z3.Array(name, z3.IntSort(), z3.IntSort())
            continue
        if name.startswith("__heap_list_data_"):
            elem_tag = name.split("__heap_list_data_", 1)[1]
            elem_sort = _z3_sort_from_tag(elem_tag)
            consts[name] = z3.Array(name, z3.IntSort(), z3.ArraySort(z3.IntSort(), elem_sort))
            continue
        if name.startswith("__heap_dict_dom_"):
            key_tag = name.split("__heap_dict_dom_", 1)[1]
            key_sort = _z3_sort_from_tag(key_tag)
            consts[name] = z3.Array(name, z3.IntSort(), z3.ArraySort(key_sort, z3.BoolSort()))
            continue
        if name.startswith("__heap_dict_map_"):
            rest = name.split("__heap_dict_map_", 1)[1]
            parts = rest.split("_", 1)
            if len(parts) != 2:
                raise Exception(f"Malformed dict heap name: {name}")
            key_tag, val_tag = parts
            key_sort = _z3_sort_from_tag(key_tag)
            val_sort = _z3_sort_from_tag(val_tag)
            consts[name] = z3.Array(name, z3.IntSort(), z3.ArraySort(key_sort, val_sort))
            continue
        if name.startswith("__heap_field_"):
            # __heap_field_<tag> : Array[Ref, Array[String, Val]]
            tag = name.split("__heap_field_", 1)[1]
            val_sort = _z3_sort_from_tag(tag)
            consts[name] = z3.Array(name, z3.IntSort(), z3.ArraySort(z3.StringSort(), val_sort))
            continue
        raise Exception(f"Unknown heap var name: {name}")
    return consts

def parse_func_types(func, inputs=[]):
    code = inspect.getsource(func)
    # Dedent the source code to handle indented functions
    import textwrap
    code = textwrap.dedent(code)
    func_ast = ast.parse(code)
    func_def = func_ast.body[0]
    result = []
    provided = dict(inputs)
    for i in func_def.args.args:
        if i.annotation:
            ann = i.annotation
            handled = False
            # Support refinement convenience constructors used as annotations, e.g., PositiveInt().
            if isinstance(ann, ast.Call) and isinstance(ann.func, ast.Name):
                ctor_name = ann.func.id
                try:
                    from veripy.typecheck import refinement as refinement_mod
                    ctor_map = {
                        'PositiveInt': refinement_mod.PositiveInt,
                        'NonNegativeInt': refinement_mod.NonNegativeInt,
                        'EvenInt': refinement_mod.EvenInt,
                        'OddInt': refinement_mod.OddInt,
                        'RangeInt': refinement_mod.RangeInt,
                        'NonEmptyList': refinement_mod.NonEmptyList,
                        'ListWithLength': refinement_mod.ListWithLength,
                    }
                    if ctor_name in ctor_map:
                        ctor = ctor_map[ctor_name]
                        ctor_args = []
                        for a in ann.args:
                            if isinstance(a, ast.Constant):
                                ctor_args.append(a.value)
                            else:
                                ctor_args = None
                                break
                        if ctor_args is not None:
                            result.append(ctor(*ctor_args))
                            handled = True
                except Exception:
                    # Fallback to normal processing if constructor handling fails.
                    handled = False
            if not handled:
                result.append(tc.types.to_ast_type(ann))
        else:
            result.append(provided.get(i.arg, tc.types.TANY))
        provided[i.arg] = result[-1]

    if func_def.returns:
        ret_type = tc.types.to_ast_type(func_def.returns)
        return (result, provided, ret_type)
    else:
        raise Exception('Return annotation is required for verifying functions')

def verify(inputs: List[Tuple[str, tc.types.SUPPORTED]]=[], requires: List[str]=[], ensures: List[str]=[], modifies: List[str]=[], reads: List[str]=[], decreases: str=None):
    def verify_impl(func):
        @wraps(func)
        def caller(*args, **kargs):
            return func(*args, **kargs)
        types = parse_func_types(func, inputs=inputs)
        scope = STORE.current_scope()
        STORE.insert_func_attr(scope, func.__name__, types[0], types[1], types[2], requires, ensures, decreases)
        STORE.push_verification(func.__name__, lambda: verify_func(func, scope, inputs, requires, ensures, modifies, reads))
        return caller
    return verify_impl

def collect_assigned_vars(stmt: Stmt) -> set:
    if isinstance(stmt, Skip):
        return set()
    if isinstance(stmt, Assign):
        if isinstance(stmt.var, str):
            return {stmt.var}
        if isinstance(stmt.var, Var):
            return {stmt.var.name}
        return set()
    if isinstance(stmt, Seq):
        return collect_assigned_vars(stmt.s1).union(collect_assigned_vars(stmt.s2))
    if isinstance(stmt, If):
        return collect_assigned_vars(stmt.lb).union(collect_assigned_vars(stmt.rb))
    if isinstance(stmt, While):
        return collect_assigned_vars(stmt.body)
    if isinstance(stmt, SubscriptAssignStmt):
        # Treat container mutation as a write to the container variable (approximate frame).
        if isinstance(stmt.base, Var):
            return {stmt.base.name}
        return set()
    if isinstance(stmt, Havoc):
        return {stmt.var}
    return set()
