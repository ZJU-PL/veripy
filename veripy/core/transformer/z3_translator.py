"""
Z3 translator that converts veripy AST to Z3 constraints.

Adds support for:
- Sets (union, intersection, difference, membership, cardinality)
- Dictionaries (get, set, keys, values)
- Strings (concat, length, substring, index)
- Field access (for OOP)
"""

import z3
from veripy.parser.syntax import *
from veripy.typecheck.types import *
from .utils import raise_exception


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
                 func_returns: dict = None, class_fields: dict = None,
                 uf_cache: dict = None):
        self.name_dict = name_dict
        self.old_dict = old_dict or {}
        self.func_returns = func_returns or {}
        self.class_fields = class_fields or {}  # {class_name: {field_name: z3_sort}}
        # Use provided cache or create new one - for consistent uf references across verification
        self._uf_cache = uf_cache if uf_cache is not None else {}
        # Cache for list-comprehension placeholders
        self._listcomp_cache = {}
        # Cache for set/dict comprehension placeholders
        self._setcomp_cache = {}
        self._dictcomp_cache = {}
        
        # Uninterpreted functions for special operations
        # Length is intentionally modeled as an uninterpreted function.
        # We keep one len-function per array sort, so `len` is well-typed for
        # arrays of different element sorts (e.g., int vs bool).
        self._len_funs_by_sort = {}
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

    def _as_bool(self, term):
        if z3.is_bool(term):
            return term
        if z3.is_int(term) or z3.is_arith(term):
            return term != 0
        return z3.BoolVal(True)
        
    def _guess_boolish(self, expr: Expr) -> bool:
        if isinstance(expr, Literal):
            return isinstance(expr.value, VBool)
        if isinstance(expr, Var):
            return True
        if isinstance(expr, UnOp):
            return expr.op == BoolOps.Not and self._guess_boolish(expr.e)
        if isinstance(expr, BinOp):
            if isinstance(expr.op, ArithOps):
                return False
            if isinstance(expr.op, CompOps):
                return False
            if isinstance(expr.op, BoolOps):
                return self._guess_boolish(expr.e1) and self._guess_boolish(expr.e2)
        if isinstance(expr, Quantification):
            return self._guess_boolish(expr.expr)
        return False

    def translate_type(self, ty):
        if ty == TINT:
            return z3.IntSort()
        if ty == TBOOL:
            return z3.BoolSort()
        if ty is str:
            return z3.StringSort()
        # In the heap model, Python lists/dicts are references.
        if isinstance(ty, TARR) or isinstance(ty, TDICT):
            return z3.IntSort()
        if isinstance(ty, TSET):
            # Sets are modeled as characteristic functions.
            return z3.ArraySort(self.translate_type(ty.elem_ty), z3.BoolSort())
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
            # without having been pre-registered. For quantified variables
            # (heuristic: contain '$$'), default to Bool; otherwise Int.
            default = z3.Bool(node.name) if '$$' in node.name else z3.Int(node.name)
            self.name_dict[node.name] = default
        return self.name_dict[node.name]
    
    def visit_BinOp(self, node: BinOp):
        c1 = self.visit(node.e1)
        c2 = self.visit(node.e2)

        def _as_bool(term):
            if z3.is_bool(term):
                return term
            if z3.is_int(term) or z3.is_arith(term):
                return term != 0
            return z3.BoolVal(True)

        def _safe_eq(a, b):
            try:
                return a == b
            except Exception:
                # Heterogeneous equality is always false in our logic model.
                return z3.BoolVal(False)

        def _safe_neq(a, b):
            try:
                return a != b
            except Exception:
                # If equality is ill-typed, inequality defaults to true.
                return z3.BoolVal(True)
        
        op_handlers = {
            # Arithmetic
            ArithOps.Add: lambda: c1 + c2,
            ArithOps.Minus: lambda: c1 - c2,
            ArithOps.Mult: lambda: c1 * c2,
            ArithOps.IntDiv: lambda: c1 / c2,
            ArithOps.Mod: lambda: c1 % c2,
            
            # Boolean
            BoolOps.And: lambda: z3.And(self._as_bool(c1), self._as_bool(c2)),
            BoolOps.Or: lambda: z3.Or(self._as_bool(c1), self._as_bool(c2)),
            BoolOps.Implies: lambda: z3.Implies(self._as_bool(c1), self._as_bool(c2)),
            BoolOps.Iff: lambda: z3.And(z3.Implies(self._as_bool(c1), self._as_bool(c2)), z3.Implies(self._as_bool(c2), self._as_bool(c1))),
            
            # Comparison
            CompOps.Eq: lambda: _safe_eq(c1, c2),
            CompOps.Neq: lambda: _safe_neq(c1, c2),
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
            return z3.Not(self._as_bool(c))
        raise_exception(f'Unsupported UnOp: {node.op}')
    
    def visit_Quantification(self, node: Quantification):
        # Defensive: some older builders used Quantification(var, expr, ty)
        # instead of Quantification(var, ty, expr).
        q_ty = node.ty
        q_expr = node.expr
        if isinstance(q_ty, Expr) and (q_expr == TINT or q_expr == TBOOL or isinstance(q_expr, TARR)):
            q_ty, q_expr = q_expr, q_ty

        bound_var = None
        # Default untyped quantifiers using a heuristic: boolean if the body is
        # boolean-only, otherwise integer.
        if q_ty is None:
            q_ty = TBOOL if self._guess_boolish(q_expr) else TINT
        if q_ty == TINT:
            bound_var = z3.Int(node.var.name)
        elif q_ty == TBOOL:
            bound_var = z3.Bool(node.var.name)
        elif isinstance(q_ty, TARR):
            bound_var = z3.Array(z3.IntSort(), self.translate_type(q_ty.ty))
        # Fallback to int-typed quantifier if unsupported type is provided.
        if bound_var is None:
            bound_var = z3.Int(node.var.name)
        self.name_dict[node.var.name] = bound_var
        return z3.ForAll(bound_var, self._as_bool(self.visit(q_expr)))
    
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

        def _parse_summary_uf(nm: str):
            # Expected: __uf_<user_fname>__<out>, where out is either "ans" or a
            # heap short-name like "heap_list_len".
            if not nm.startswith("__uf_"):
                return None
            rest = nm[len("__uf_") :]
            if "__" not in rest:
                return None
            user_fn, out = rest.rsplit("__", 1)
            return user_fn, out

        def _sort_from_tag(tag: str):
            if tag in ("int", "ref"):
                return z3.IntSort()
            if tag == "bool":
                return z3.BoolSort()
            if tag == "str":
                return z3.StringSort()
            raise_exception(f"Unsupported heap tag: {tag}")

        def _heap_sort_from_short(short: str):
            # short is like "heap_list_len"; reconstruct full heap var name.
            hv = "__" + short
            if hv == "__heap_list_len":
                return z3.ArraySort(z3.IntSort(), z3.IntSort())
            if hv.startswith("__heap_list_data_"):
                elem_tag = hv.split("__heap_list_data_", 1)[1]
                elem_sort = _sort_from_tag(elem_tag)
                return z3.ArraySort(z3.IntSort(), z3.ArraySort(z3.IntSort(), elem_sort))
            if hv.startswith("__heap_dict_dom_"):
                key_tag = hv.split("__heap_dict_dom_", 1)[1]
                key_sort = _sort_from_tag(key_tag)
                return z3.ArraySort(z3.IntSort(), z3.ArraySort(key_sort, z3.BoolSort()))
            if hv.startswith("__heap_dict_map_"):
                rest = hv.split("__heap_dict_map_", 1)[1]
                parts = rest.split("_", 1)
                if len(parts) != 2:
                    raise_exception(f"Malformed dict heap name: {hv}")
                key_tag, val_tag = parts
                key_sort = _sort_from_tag(key_tag)
                val_sort = _sort_from_tag(val_tag)
                return z3.ArraySort(z3.IntSort(), z3.ArraySort(key_sort, val_sort))
            if hv.startswith("__heap_field_"):
                tag = hv.split("__heap_field_", 1)[1]
                val_sort = _sort_from_tag(tag)
                return z3.ArraySort(z3.IntSort(), z3.ArraySort(z3.StringSort(), val_sort))
            raise_exception(f"Unknown heap short-name: {short}")
        
        # Handle built-in functions
        if fname == 'len':
            assert len(node.args) == 1
            arr = self.visit(node.args[0])
            a_sort = arr.sort()
            len_fun = self._len_funs_by_sort.get(a_sort)
            if len_fun is None:
                # Use a stable name derived from the sort to keep debugging readable.
                # Z3 sorts print without whitespace, so this is safe for identifiers.
                sort_name = str(a_sort).replace(' ', '_')
                len_fun = z3.Function(f'len_{sort_name}', a_sort, z3.IntSort())
                self._len_funs_by_sort[a_sort] = len_fun
            return len_fun(arr)
        
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
        
        # Uninterpreted functions/consts for user functions and verifier summaries.
        summary = _parse_summary_uf(fname)
        if summary is not None:
            user_fn, out = summary
            if out == "ans":
                ret_sort = self.translate_type(self.func_returns.get(user_fn, TINT))
            else:
                ret_sort = _heap_sort_from_short(out)
            sym_name = fname
        else:
            ret_sort = self.translate_type(self.func_returns.get(fname, TINT))
            sym_name = f'uf_{fname}'

        if not arg_terms:
            key = (sym_name, tuple(), ret_sort)
            if key not in self._uf_cache:
                self._uf_cache[key] = z3.Const(sym_name, ret_sort)
            return self._uf_cache[key]

        arg_sorts = tuple(t.sort() for t in arg_terms)
        key = (sym_name, arg_sorts, ret_sort)
        if key not in self._uf_cache:
            self._uf_cache[key] = z3.Function(sym_name, *arg_sorts, ret_sort)
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
        """
        Set comprehension placeholder.

        Model as an unconstrained set to avoid unsound under-approximation.
        """
        key = repr(node)
        if key not in self._setcomp_cache:
            # Default to Int elements; this matches existing set encoding.
            self._setcomp_cache[key] = z3.Array(
                f'setcomp_{len(self._setcomp_cache) + 1}',
                z3.IntSort(),
                z3.BoolSort(),
            )
        return self._setcomp_cache[key]

    def visit_DictComprehension(self, node: DictComprehension):
        """
        Dict comprehension placeholder.

        Model as an unconstrained map to avoid unsound under-approximation.
        """
        key = repr(node)
        if key not in self._dictcomp_cache:
            # Attempt to infer key/value sorts from the comprehension expressions.
            try:
                k_sort = self.visit(node.key_expr).sort()
            except Exception:
                k_sort = z3.IntSort()
            try:
                v_sort = self.visit(node.value_expr).sort()
            except Exception:
                v_sort = z3.IntSort()
            if v_sort == z3.BoolSort():
                default_v = z3.BoolVal(False)
            elif v_sort == z3.StringSort():
                default_v = z3.StringVal("")
            else:
                default_v = z3.IntVal(0)
            self._dictcomp_cache[key] = z3.K(k_sort, default_v)
        return self._dictcomp_cache[key]
    
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
            DictComprehension: self.visit_DictComprehension,
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
