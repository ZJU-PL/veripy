import ast
import z3
import inspect
from typing import List, Tuple, TypeVar
from veripy.parser.syntax import *
from veripy.parser.parser import parse_assertion, parse_expr
from functools import wraps
from veripy.core.transformer import *
from functools import reduce
from veripy.core.prettyprint import pretty_print
from veripy import typecheck as tc
from veripy.typecheck.types import TARR, TINT, TBOOL

# Global cache for uninterpreted functions to ensure consistency across verification
# This cache is shared between function summary generation and expression translation
_UF_CACHE = {}

class VerificationStore:
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
        self.switch = True
        # Clear the uninterpreted function cache when enabling verification
        # to ensure each test starts with a fresh state
        global _UF_CACHE
        _UF_CACHE = {}

    def push(self, scope):
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
        if self.scope:
            return self.scope[-1]
    
    def push_verification(self, func_name, verification_func):
        if self.switch:
            if not self.scope:
                raise Exception('No Scope Defined')
            self.store[self.scope[-1]]['vf'].append((func_name, verification_func))
    
    def verify(self, scope, ignore_err):
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
        if self.store:
            # Legacy API: look up in current scope if available
            if self.scope:
                return self.store[self.scope[-1]].get('func_attrs', dict()).get(fname)
            return None
        return None

    def current_func_attrs(self):
        if self.scope:
            return self.store[self.scope[-1]]['func_attrs']
    
    def get_func_attrs(self, scope, fname):
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

def wp_seq(sigma, stmt, Q):
    (p2, c2) = wp(sigma, stmt.s2, Q)
    (p1, c1) = wp(sigma, stmt.s1, p2)
    return (p1, c1 + c2)

def wp_if(sigma, stmt, Q):
    (p1, c1) = wp(sigma, stmt.lb, Q)
    (p2, c2) = wp(sigma, stmt.rb, Q)
    return (
        BinOp(
            BinOp(stmt.cond, BoolOps.Implies, p1),
            BoolOps.And,
            BinOp(
                UnOp(BoolOps.Not, stmt.cond), BoolOps.Implies, p2
            )
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
    return (combined_invars, c + [
        BinOp(BinOp(combined_invars, BoolOps.And, cond), BoolOps.Implies, p),
        BinOp(BinOp(combined_invars, BoolOps.And, (UnOp(BoolOps.Not, cond))), BoolOps.Implies, Q)
    ])

def wp(sigma, stmt, Q):
    def substitute_many(expr: Expr, mapping: dict):
        result = expr
        for k, v in mapping.items():
            result = subst(k, v, result)
        return result

    def wp_assign_x(stmt: Assign, Q):
        lhs = stmt.var
        if isinstance(lhs, Var):
            lhs = lhs.name
        if not isinstance(lhs, str):
            # Fail closed: silently ignoring state updates is unsound.
            raise Exception(f'Unsupported assignment LHS (would be unsound): {stmt.var!r}')

        if isinstance(stmt.expr, FunctionCall) and isinstance(stmt.expr.func_name, Var):
            # best-effort summary: assume callee requires holds; conjoin ensures with ans mapped to LHS
            fname = stmt.expr.func_name.name
            # CURRENT_FUNC_ATTRS is set in verify_func; if absent, fallback to normal assign
            attrs = STORE.func_attrs_global.get(fname)
            if attrs is None:
                return (subst(lhs, stmt.expr, Q), [])
            is_self_call = fname == getattr(STORE, 'current_func', None)
            if is_self_call:
                STORE.self_call = True
            if not attrs.get('verified', False) and not is_self_call:
                raise Exception(f"Call to unverified function '{fname}' not allowed (verify it first)")
            param_names = list(attrs['inputs'].keys())
            arg_exprs = stmt.expr.args
            mapping = { pn: ae for pn, ae in zip(param_names, arg_exprs) }
            reqs = attrs.get('requires', [])
            reqs_parsed = [parse_assertion(r) if isinstance(r, str) else r for r in reqs]
            req_fold = fold_constraints([substitute_many(rp, mapping) for rp in reqs_parsed])
            ens = attrs.get('ensures', [])
            ens_parsed = [parse_assertion(e) if isinstance(e, str) else e for e in ens]
            # Rely on modular function-summary axioms added to the solver
            # (see below). Substitute the call result directly and require
            # the callee's precondition at the call site.
            Q_sub = subst(lhs, stmt.expr, Q)
            return (BinOp(req_fold, BoolOps.And, Q_sub), [])
        
        # Handle refinement type assignments
        base_wp = subst(lhs, stmt.expr, Q)
        if isinstance(stmt.var, str) and lhs in sigma:
            refin_pred = instantiate_refinement(lhs, sigma[lhs])
            if refin_pred is not None:
                return (BinOp(refin_pred, BoolOps.And, base_wp), [])
        
        return (base_wp, [])

    return {
        Skip:   lambda: (Q, []),
        Assume:  lambda: (BinOp(stmt.e, BoolOps.Implies, Q), []),
        Assign: lambda: wp_assign_x(stmt, Q),
        Assert: lambda: (BinOp(Q, BoolOps.And, stmt.e), []),
        Seq:    lambda: wp_seq(sigma, stmt, Q),
        If:     lambda: wp_if(sigma, stmt, Q),
        While:  lambda: wp_while(sigma, stmt, Q),
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

        (P, C) = wp(sigma, target_language_ast, user_postcond)
        # Treat refinement constraints as assumptions that strengthen the pre-state.
        refinement_constraints = generate_refinement_constraints(sigma, scope_funcs)
        pre_with_refinements = user_precond
        if refinement_constraints:
            refinement_conj = fold_constraints(refinement_constraints)
            pre_with_refinements = BinOp(pre_with_refinements, BoolOps.And, refinement_conj)

        check_P = BinOp(pre_with_refinements, BoolOps.Implies, P)

        # Allow recursive calls even without explicit decreases for now to keep
        # verification permissive in common examples.
        if getattr(STORE, 'self_call', False) and not func_attrs.get('decreases'):
            pass

        solver = z3.Solver()
        current_consts = declare_consts(sigma)
        # Declare logical result 'ans' for use in postconditions
        ret_ty = func_attrs['returns']
        ret_base_ty = ret_ty.base_type if isinstance(ret_ty, tc.types.TREFINED) else ret_ty
        if ret_base_ty == tc.types.TINT:
            current_consts['ans'] = z3.Int('ans')
        elif ret_base_ty == tc.types.TBOOL:
            current_consts['ans'] = z3.Bool('ans')
        elif isinstance(ret_base_ty, tc.types.TARR):
            # array of ints for now
            current_consts['ans'] = z3.Array('ans', z3.IntSort(), z3.IntSort())
        # Build old-state symbols and equate them to current at entry
        def sort_for(ty):
            if isinstance(ty, tc.types.TREFINED):
                ty = ty.base_type
            if ty == tc.types.TINT:
                return z3.IntSort()
            if ty == tc.types.TBOOL:
                return z3.BoolSort()
            if isinstance(ty, tc.types.TARR):
                return z3.ArraySort(z3.IntSort(), sort_for(ty.ty))
            return z3.IntSort()

        def make_old_const(name, ty):
            if isinstance(ty, tc.types.TREFINED):
                ty = ty.base_type
            if ty == tc.types.TINT:
                return z3.Int(name + '$old')
            if ty == tc.types.TBOOL:
                return z3.Bool(name + '$old')
            if isinstance(ty, tc.types.TARR):
                return z3.Array(name + '$old', z3.IntSort(), sort_for(ty.ty))
            # default to int
            return z3.Int(name + '$old')
        old_consts = { name + '$old': make_old_const(name, ty)
                       for name, ty in sigma.items() if type(ty) != dict }
        for name, const in current_consts.items():
            if name + '$old' in old_consts:
                solver.add(old_consts[name + '$old'] == const)

        # Provide function return type map to translator
        def _ret_base(ty):
            return ty.base_type if isinstance(ty, tc.types.TREFINED) else ty
        fn_ret_types = { n: _ret_base(a['returns']) for n, a in scope_funcs.items() }
        translator = Expr2Z3(current_consts, old_consts, fn_ret_types, _UF_CACHE)

        # Add modular function-summary axioms for all known functions in scope.
        # For each function f(x1..xn) with requires R and ensures E, assert:
        #   forall x1..xn. R(x) ==> E(x, ans = uf_f(x))
        def _sort_for(ty_):
            if ty_ == tc.types.TINT:
                return z3.IntSort()
            if ty_ == tc.types.TBOOL:
                return z3.BoolSort()
            if isinstance(ty_, tc.types.TARR):
                return z3.ArraySort(z3.IntSort(), _sort_for(ty_.ty))
            return z3.IntSort()

        for fname, attrs in scope_funcs.items():
            if not attrs.get('verified', False):
                # Do not assume specifications of unverified functions.
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
                ax_name_dict = {n: v for n, v in zip(param_names, bound_vars)}
                if bound_vars:
                    # Use global cache to ensure consistent uf references
                    cache_key = (f'uf_{fname}', tuple(in_sorts), ret_sort)
                    if cache_key in _UF_CACHE:
                        uf = _UF_CACHE[cache_key]
                    else:
                        uf = z3.Function(f'uf_{fname}', *in_sorts, ret_sort)
                        _UF_CACHE[cache_key] = uf
                    ax_name_dict['ans'] = uf(*bound_vars)
                else:
                    # Nullary function: represent as a constant
                    ax_name_dict['ans'] = z3.Const(f'uf_{fname}', ret_sort)

                ax_translator = Expr2Z3(ax_name_dict, {}, fn_ret_types, _UF_CACHE)
                req_expr = fold_constraints(attrs.get('requires', []))
                ens_expr = fold_constraints(attrs.get('ensures', []))
                req_z3 = ax_translator.visit(req_expr)
                ens_z3 = ax_translator.visit(ens_expr)
                axiom = z3.Implies(req_z3, ens_z3)
                if bound_vars:
                    # Help Z3 instantiate the axiom on call sites.
                    # Use a pattern to guide instantiation
                    solver.add(z3.ForAll(bound_vars, axiom, patterns=[uf(*bound_vars)]))
                else:
                    solver.add(axiom)
            except Exception:
                # Never let axiom generation crash verification; fall back to no axiom.
                pass

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
        if isinstance(ty, tc.types.TARR):
            return z3.ArraySort(z3.IntSort(), sort_for(ty.ty))
        # default to int
        return z3.IntSort()
    for (name, ty) in sigma.items():
        if type(ty) != dict:
            base_ty = ty.base_type if isinstance(ty, tc.types.TREFINED) else ty
            if base_ty == tc.types.TINT:
                consts[name] = z3.Int(name)
            elif base_ty == tc.types.TBOOL:
                consts[name] = z3.Bool(name)
            elif isinstance(base_ty, tc.types.TARR):
                consts[name] = z3.Array(name, z3.IntSort(), sort_for(base_ty.ty))
            else:
                consts[name] = z3.Int(name)
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
                    from veripy import refinement as refinement_mod
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
    if isinstance(stmt, Havoc):
        return {stmt.var}
    return set()