from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple

from veripy.parser.syntax import *
from veripy.typecheck import types as tc_types
from veripy.typecheck.type_check import type_infer_expr


def _base_type(ty):
    return ty.base_type if isinstance(ty, tc_types.TREFINED) else ty


def _tag_of_type(ty) -> str:
    ty = _base_type(ty)
    if ty == tc_types.TINT:
        return "int"
    if ty == tc_types.TBOOL:
        return "bool"
    if ty is str:
        return "str"
    if isinstance(ty, (tc_types.TARR, tc_types.TDICT)):
        return "ref"
    if ty == tc_types.TANY:
        return "any"
    return "any"

_HEAP_TAGS: Tuple[str, ...] = ("int", "bool", "str", "ref")
_DICT_KEY_TAGS: Tuple[str, ...] = ("int", "str", "ref")


def global_heap_vars() -> Set[str]:
    """
    Global heap variables used by the Dafny/Boogie-style model.

    We keep this set fixed so uninterpreted summaries have a stable signature.
    """
    heaps: Set[str] = set()
    heaps.add("__heap_list_len")
    for t in _HEAP_TAGS:
        heaps.add(f"__heap_list_data_{t}")
    for k in _DICT_KEY_TAGS:
        heaps.add(f"__heap_dict_dom_{k}")
        for v in _HEAP_TAGS:
            heaps.add(f"__heap_dict_map_{k}_{v}")
    for t in _HEAP_TAGS:
        heaps.add(f"__heap_field_{t}")
    return heaps


def sorted_heap_vars(heaps: Set[str] | None = None) -> List[str]:
    return sorted(heaps if heaps is not None else global_heap_vars())


def heap_short_name(heap_var: str) -> str:
    if not heap_var.startswith("__"):
        raise Exception(f"Not a heap var: {heap_var}")
    return heap_var[2:]


def uf_name(fname: str, out: str) -> str:
    # out is either "ans" or a heap short-name like "heap_list_len".
    return f"__uf_{fname}__{out}"


def _require_known(tag: str, what: str):
    if tag == "any":
        raise Exception(f"Cannot lower heap operation with unknown {what} type; add annotations/refinements")


@dataclass
class HeapEnv:
    sigma: Dict[str, object]
    func_sigma: Dict[str, object]
    field_tags: Dict[str, str]
    heap_vars: Set[str]


def infer_field_tags(stmt: Stmt, sigma: Dict[str, object], func_sigma: Dict[str, object]) -> Dict[str, str]:
    """
    Infer per-field value tags (int/bool/str/ref) from field assignments.

    If a field is assigned multiple incompatible types, fail closed.
    """
    tags: Dict[str, str] = {}

    def visit(s: Stmt):
        if isinstance(s, Skip):
            return
        if isinstance(s, Seq):
            visit(s.s1)
            visit(s.s2)
            return
        if isinstance(s, If):
            visit(s.lb)
            visit(s.rb)
            return
        if isinstance(s, While):
            visit(s.body)
            return
        if isinstance(s, FieldAssignStmt):
            try:
                v_ty = type_infer_expr(sigma, func_sigma, s.value)
            except Exception:
                v_ty = tc_types.TANY
            tag = _tag_of_type(v_ty)
            _require_known(tag, f"field '{s.field}'")
            prev = tags.get(s.field)
            if prev is not None and prev != tag:
                raise Exception(f"Field '{s.field}' assigned with incompatible types: {prev} vs {tag}")
            tags[s.field] = tag
            return
        if isinstance(s, SubscriptAssignStmt):
            return
        if isinstance(s, Assign):
            return
        if isinstance(s, (Assume, Assert, Havoc)):
            return
        # Other statement forms are ignored by the core verifier anyway.
        return

    visit(stmt)
    return tags


def heap_vars_for(sigma: Dict[str, object], field_tags: Dict[str, str]) -> Set[str]:
    """
    Compute the set of heap variables required by the types in `sigma` and inferred fields.

    Naming scheme (parsed later when declaring Z3 sorts):
    - `__heap_list_len` : Array[Ref, Int]
    - `__heap_list_data_<elem>` : Array[Ref, Array[Int, Elem]]
    - `__heap_dict_dom_<key>` : Array[Ref, Array[Key, Bool]]
    - `__heap_dict_map_<key>_<val>` : Array[Ref, Array[Key, Val]]
    - `__heap_field_<field>_<val>` : Array[Ref, Val]
    """
    heaps: Set[str] = set()
    for _, ty in sigma.items():
        ty = _base_type(ty)
        if isinstance(ty, tc_types.TARR):
            heaps.add("__heap_list_len")
            elem_tag = _tag_of_type(ty.ty)
            _require_known(elem_tag, "list element")
            heaps.add(f"__heap_list_data_{elem_tag}")
        if isinstance(ty, tc_types.TDICT):
            key_tag = _tag_of_type(ty.key_ty)
            val_tag = _tag_of_type(ty.val_ty)
            _require_known(key_tag, "dict key")
            _require_known(val_tag, "dict value")
            heaps.add(f"__heap_dict_dom_{key_tag}")
            heaps.add(f"__heap_dict_map_{key_tag}_{val_tag}")
    for field, tag in field_tags.items():
        _require_known(tag, f"field '{field}'")
        heaps.add(f"__heap_field_{field}_{tag}")
    return heaps


class HeapLowerer:
    """
    Lower Python list/dict/object operations into a Dafny/Boogie-style explicit heap.

    The lowered program uses heap variables as ordinary mutable state, so the
    existing WP substitution engine can account for aliasing/mutation.
    """

    def __init__(self, env: HeapEnv):
        self.env = env
        self._fresh_idx = 0
        self.fresh_refs: Set[str] = set()

    def _fresh_ref(self, prefix: str) -> Var:
        self._fresh_idx += 1
        name = f"{prefix}{self._fresh_idx}"
        self.fresh_refs.add(name)
        return Var(name)

    def _list_elem_tag(self, list_name: str) -> str:
        ty = _base_type(self.env.sigma.get(list_name, tc_types.TANY))
        if not isinstance(ty, tc_types.TARR):
            raise Exception(f"Expected list type for '{list_name}', got {ty}")
        elem_tag = _tag_of_type(ty.ty)
        _require_known(elem_tag, "list element")
        return elem_tag

    def _dict_tags(self, dict_name: str) -> Tuple[str, str]:
        ty = _base_type(self.env.sigma.get(dict_name, tc_types.TANY))
        if not isinstance(ty, tc_types.TDICT):
            raise Exception(f"Expected dict type for '{dict_name}', got {ty}")
        key_tag = _tag_of_type(ty.key_ty)
        # Python treats bool as an int for hashing; reuse int-key heaps.
        if key_tag == "bool":
            key_tag = "int"
        val_tag = _tag_of_type(ty.val_ty)
        _require_known(key_tag, "dict key")
        _require_known(val_tag, "dict value")
        return key_tag, val_tag

    def lower_expr(self, e: Expr, rewrite_user_calls: bool = False) -> Expr:
        if isinstance(e, (Var, Literal, StringLiteral)):
            return e
        if isinstance(e, UnOp):
            return UnOp(e.op, self.lower_expr(e.e, rewrite_user_calls=rewrite_user_calls))
        if isinstance(e, BinOp):
            # Dict membership: k in d  ==>  heap_dom[d][k]
            if e.op == CompOps.In and isinstance(e.e2, Var):
                dname = e.e2.name
                dty = _base_type(self.env.sigma.get(dname, tc_types.TANY))
                if isinstance(dty, tc_types.TDICT):
                    key_tag, _ = self._dict_tags(dname)
                    dom_heap = Var(f"__heap_dict_dom_{key_tag}")
                    return Subscript(Subscript(dom_heap, Var(dname)), self.lower_expr(e.e1, rewrite_user_calls=rewrite_user_calls))
            return BinOp(self.lower_expr(e.e1, rewrite_user_calls=rewrite_user_calls), e.op, self.lower_expr(e.e2, rewrite_user_calls=rewrite_user_calls))
        if isinstance(e, Subscript):
            base = self.lower_expr(e.var, rewrite_user_calls=rewrite_user_calls)
            idx = self.lower_expr(e.subscript, rewrite_user_calls=rewrite_user_calls)
            if isinstance(base, Var):
                name = base.name
                ty = _base_type(self.env.sigma.get(name, tc_types.TANY))
                if isinstance(ty, tc_types.TARR):
                    elem_tag = self._list_elem_tag(name)
                    heap_data = Var(f"__heap_list_data_{elem_tag}")
                    return Subscript(Subscript(heap_data, base), idx)
                if isinstance(ty, tc_types.TDICT):
                    key_tag, val_tag = self._dict_tags(name)
                    heap_map = Var(f"__heap_dict_map_{key_tag}_{val_tag}")
                    return Subscript(Subscript(heap_map, base), idx)
            return Subscript(base, idx)
        if isinstance(e, Store):
            return Store(
                self.lower_expr(e.arr, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.idx, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.val, rewrite_user_calls=rewrite_user_calls),
            )
        if isinstance(e, FunctionCall):
            # Lower len(list) to heap_list_len[list]
            if isinstance(e.func_name, Var) and e.func_name.name == "len" and len(e.args) == 1:
                arg0 = self.lower_expr(e.args[0], rewrite_user_calls=rewrite_user_calls)
                if isinstance(arg0, Var):
                    name = arg0.name
                    ty = _base_type(self.env.sigma.get(name, tc_types.TANY))
                    if isinstance(ty, tc_types.TARR):
                        return Subscript(Var("__heap_list_len"), arg0)
                    if isinstance(ty, tc_types.TDICT):
                        key_tag, _ = self._dict_tags(name)
                        dom_heap = Var(f"__heap_dict_dom_{key_tag}")
                        # For int-key dicts, model len as card(dom(d)).
                        if key_tag == "int":
                            return FunctionCall(Var("card"), [Subscript(dom_heap, arg0)])
                        # Otherwise, keep as uninterpreted (sound but weak).
                        return FunctionCall(Var("__dict_len"), [Subscript(dom_heap, arg0)])
            lowered_args = [self.lower_expr(a, rewrite_user_calls=rewrite_user_calls) for a in e.args]
            if rewrite_user_calls and isinstance(e.func_name, Var):
                fname = e.func_name.name
                if fname in self.env.func_sigma and not fname.startswith("__"):
                    heap_args = [Var(h) for h in sorted_heap_vars(self.env.heap_vars)]
                    return FunctionCall(Var(uf_name(fname, "ans")), lowered_args + heap_args, native=getattr(e, "native", True))
            fn = self.lower_expr(e.func_name, rewrite_user_calls=rewrite_user_calls) if isinstance(e.func_name, Expr) else e.func_name
            return FunctionCall(fn, lowered_args, native=getattr(e, "native", True))
        if isinstance(e, Old):
            # Rewrite `old(E)` by evaluating E in the pre-state environment.
            # This avoids needing an Old-aware Z3 translation for heap-lowered
            # composite expressions.
            inner = self.lower_expr(e.expr, rewrite_user_calls=rewrite_user_calls)
            return _expr_in_old_state(inner)
        if isinstance(e, SetLiteral):
            return SetLiteral([self.lower_expr(x, rewrite_user_calls=rewrite_user_calls) for x in e.elements])
        if isinstance(e, DictLiteral):
            return DictLiteral(
                [self.lower_expr(x, rewrite_user_calls=rewrite_user_calls) for x in e.keys],
                [self.lower_expr(x, rewrite_user_calls=rewrite_user_calls) for x in e.values],
            )
        if isinstance(e, SetOp):
            return SetOp(
                self.lower_expr(e.left, rewrite_user_calls=rewrite_user_calls),
                e.op,
                self.lower_expr(e.right, rewrite_user_calls=rewrite_user_calls),
            )
        if isinstance(e, SetCardinality):
            return SetCardinality(self.lower_expr(e.set_expr, rewrite_user_calls=rewrite_user_calls))
        if isinstance(e, DictGet):
            return DictGet(
                self.lower_expr(e.dict_expr, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.key, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.default, rewrite_user_calls=rewrite_user_calls) if e.default else None,
            )
        if isinstance(e, DictSet):
            return DictSet(
                self.lower_expr(e.dict_expr, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.key, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.value, rewrite_user_calls=rewrite_user_calls),
            )
        if isinstance(e, DictKeys):
            return DictKeys(self.lower_expr(e.dict_expr, rewrite_user_calls=rewrite_user_calls))
        if isinstance(e, DictValues):
            return DictValues(self.lower_expr(e.dict_expr, rewrite_user_calls=rewrite_user_calls))
        if isinstance(e, DictContains):
            return DictContains(
                self.lower_expr(e.dict_expr, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.key, rewrite_user_calls=rewrite_user_calls),
            )
        if isinstance(e, ListComprehension):
            return ListComprehension(
                self.lower_expr(e.element_expr, rewrite_user_calls=rewrite_user_calls),
                e.element_var,
                self.lower_expr(e.iterable, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.predicate, rewrite_user_calls=rewrite_user_calls) if e.predicate else None,
            )
        if isinstance(e, SetComprehension):
            return SetComprehension(
                e.element_var,
                self.lower_expr(e.source, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.predicate, rewrite_user_calls=rewrite_user_calls) if e.predicate else None,
            )
        if isinstance(e, DictComprehension):
            return DictComprehension(
                self.lower_expr(e.key_expr, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.value_expr, rewrite_user_calls=rewrite_user_calls),
                e.element_var,
                self.lower_expr(e.iterable, rewrite_user_calls=rewrite_user_calls),
                self.lower_expr(e.predicate, rewrite_user_calls=rewrite_user_calls) if e.predicate else None,
            )
        if isinstance(e, Quantification):
            # Quantifiers are pure; just lower inside the body.
            # Bound variables are plain Vars and should not be rewritten.
            return Quantification(
                e.var,
                e.ty,
                self.lower_expr(e.expr, rewrite_user_calls=rewrite_user_calls),
            )
        if isinstance(e, FieldAccess):
            obj = self.lower_expr(e.obj, rewrite_user_calls=rewrite_user_calls)
            tag = self.env.field_tags.get(e.field, "any")
            _require_known(tag, f"field '{e.field}'")
            heap_field = Var(f"__heap_field_{tag}")
            return Subscript(Subscript(heap_field, obj), StringLiteral(e.field))
        if isinstance(e, MethodCall):
            return MethodCall(
                self.lower_expr(e.obj, rewrite_user_calls=rewrite_user_calls),
                e.method_name,
                [self.lower_expr(a, rewrite_user_calls=rewrite_user_calls) for a in e.args],
            )
        raise Exception(f"Heap lowering not implemented for expression {type(e).__name__}")

    def _seq(self, stmts: List[Stmt]) -> Stmt:
        if not stmts:
            return Skip()
        out = stmts[0]
        for s in stmts[1:]:
            out = Seq(out, s)
        return out

    def lower_stmt(self, s: Stmt) -> Stmt:
        if isinstance(s, Skip):
            return s
        if isinstance(s, Seq):
            return Seq(self.lower_stmt(s.s1), self.lower_stmt(s.s2))
        if isinstance(s, If):
            return If(self.lower_expr(s.cond, rewrite_user_calls=False), self.lower_stmt(s.lb), self.lower_stmt(s.rb))
        if isinstance(s, While):
            invs = [self.lower_expr(i, rewrite_user_calls=False) for i in s.invariants]
            return While(invs, self.lower_expr(s.cond, rewrite_user_calls=False), self.lower_stmt(s.body))
        if isinstance(s, Assert):
            return Assert(self.lower_expr(s.e, rewrite_user_calls=False))
        if isinstance(s, Assume):
            return Assume(self.lower_expr(s.e, rewrite_user_calls=False))
        if isinstance(s, Havoc):
            return s
        if isinstance(s, FieldAssignStmt):
            obj = self.lower_expr(s.obj, rewrite_user_calls=False)
            val = self.lower_expr(s.value, rewrite_user_calls=False)
            tag = self.env.field_tags.get(s.field, "any")
            _require_known(tag, f"field '{s.field}'")
            heap_name = f"__heap_field_{tag}"
            row = Subscript(Var(heap_name), obj)
            row2 = Store(row, StringLiteral(s.field), val)
            return Assign(heap_name, Store(Var(heap_name), obj, row2))
        if isinstance(s, SubscriptAssignStmt):
            if not isinstance(s.base, Var):
                raise Exception("Only variable bases are supported for subscript assignment")
            base_name = s.base.name
            idx = self.lower_expr(s.idx, rewrite_user_calls=False)
            val = self.lower_expr(s.value, rewrite_user_calls=False)
            ty = _base_type(self.env.sigma.get(base_name, tc_types.TANY))
            if isinstance(ty, tc_types.TARR):
                elem_tag = self._list_elem_tag(base_name)
                heap_data_name = f"__heap_list_data_{elem_tag}"
                ref = Var(base_name)
                row = Subscript(Var(heap_data_name), ref)
                row2 = Store(row, idx, val)
                return Assign(heap_data_name, Store(Var(heap_data_name), ref, row2))
            if isinstance(ty, tc_types.TDICT):
                key_tag, val_tag = self._dict_tags(base_name)
                dom_name = f"__heap_dict_dom_{key_tag}"
                map_name = f"__heap_dict_map_{key_tag}_{val_tag}"
                ref = Var(base_name)
                dom_row = Subscript(Var(dom_name), ref)
                dom_row2 = Store(dom_row, idx, Literal(VBool(True)))
                map_row = Subscript(Var(map_name), ref)
                map_row2 = Store(map_row, idx, val)
                return Seq(
                    Assign(dom_name, Store(Var(dom_name), ref, dom_row2)),
                    Assign(map_name, Store(Var(map_name), ref, map_row2)),
                )
            raise Exception(f"Unsupported subscript assignment base type for '{base_name}': {ty}")
        if isinstance(s, Assign):
            lhs = s.var.name if isinstance(s.var, Var) else s.var
            rhs = self.lower_expr(s.expr, rewrite_user_calls=False) if isinstance(s.expr, Expr) else s.expr

            # Expand list/dict literal placeholders in statement position.
            if isinstance(rhs, FunctionCall) and isinstance(rhs.func_name, Var):
                if rhs.func_name.name == "__list_lit":
                    if not isinstance(lhs, str):
                        raise Exception("List literal assignment requires a variable LHS")
                    ty = _base_type(self.env.sigma.get(lhs, tc_types.TANY))
                    if not isinstance(ty, tc_types.TARR):
                        raise Exception(f"List literal assigned to non-list variable '{lhs}'")
                    elem_tag = self._list_elem_tag(lhs)
                    ref = self._fresh_ref("__alloc_list_")
                    n = len(rhs.args)
                    heap_len = "__heap_list_len"
                    heap_data = f"__heap_list_data_{elem_tag}"

                    row = Subscript(Var(heap_data), ref)
                    for i, a in enumerate(rhs.args):
                        row = Store(row, Literal(VInt(i)), self.lower_expr(a, rewrite_user_calls=False))

                    return self._seq([
                        Assign(lhs, ref),
                        Assign(heap_len, Store(Var(heap_len), ref, Literal(VInt(n)))),
                        Assign(heap_data, Store(Var(heap_data), ref, row)),
                    ])
                if rhs.func_name.name == "__dict_lit":
                    if not isinstance(lhs, str):
                        raise Exception("Dict literal assignment requires a variable LHS")
                    ty = _base_type(self.env.sigma.get(lhs, tc_types.TANY))
                    if not isinstance(ty, tc_types.TDICT):
                        raise Exception(f"Dict literal assigned to non-dict variable '{lhs}'")
                    if len(rhs.args) % 2 != 0:
                        raise Exception("__dict_lit expects an even number of args (k/v pairs)")
                    key_tag, val_tag = self._dict_tags(lhs)
                    ref = self._fresh_ref("__alloc_dict_")
                    dom_name = f"__heap_dict_dom_{key_tag}"
                    map_name = f"__heap_dict_map_{key_tag}_{val_tag}"
                    dom_row = Subscript(Var(dom_name), ref)
                    map_row = Subscript(Var(map_name), ref)
                    for i in range(0, len(rhs.args), 2):
                        k = self.lower_expr(rhs.args[i], rewrite_user_calls=False)
                        v = self.lower_expr(rhs.args[i + 1], rewrite_user_calls=False)
                        dom_row = Store(dom_row, k, Literal(VBool(True)))
                        map_row = Store(map_row, k, v)
                    return self._seq([
                        Assign(lhs, ref),
                        Assign(dom_name, Store(Var(dom_name), ref, dom_row)),
                        Assign(map_name, Store(Var(map_name), ref, map_row)),
                    ])

            return Assign(lhs, rhs)

        raise Exception(f"Heap lowering not implemented for statement {type(s).__name__}")


def _expr_in_old_state(e: Expr) -> Expr:
    """
    Rewrite an expression to refer to pre-state variables by appending `$old`.

    This is a syntactic transformation (not capture-avoiding for user-defined
    `$old` identifiers). We avoid rewriting bound variables in quantifiers.
    """
    def go(expr: Expr, bound: Set[str]) -> Expr:
        if isinstance(expr, Var):
            if expr.name in bound:
                return expr
            return Var(expr.name + "$old")
        if isinstance(expr, Literal) or isinstance(expr, StringLiteral):
            return expr
        if isinstance(expr, UnOp):
            return UnOp(expr.op, go(expr.e, bound))
        if isinstance(expr, BinOp):
            return BinOp(go(expr.e1, bound), expr.op, go(expr.e2, bound))
        if isinstance(expr, Subscript):
            return Subscript(go(expr.var, bound), go(expr.subscript, bound))
        if isinstance(expr, Store):
            return Store(go(expr.arr, bound), go(expr.idx, bound), go(expr.val, bound))
        if isinstance(expr, FunctionCall):
            fn = expr.func_name
            if isinstance(fn, Expr):
                fn = go(fn, bound)
            return FunctionCall(fn, [go(a, bound) for a in expr.args], native=getattr(expr, "native", True))
        if isinstance(expr, Quantification):
            # Note: our Quantification node doesn't track forall/exists kind here;
            # but we must still respect the binder name.
            new_bound = set(bound)
            new_bound.add(expr.var.name)
            return Quantification(expr.var, expr.ty, go(expr.expr, new_bound))
        if isinstance(expr, SetLiteral):
            return SetLiteral([go(x, bound) for x in expr.elements])
        if isinstance(expr, DictLiteral):
            return DictLiteral([go(x, bound) for x in expr.keys], [go(x, bound) for x in expr.values])
        if isinstance(expr, SetOp):
            return SetOp(go(expr.left, bound), expr.op, go(expr.right, bound))
        if isinstance(expr, SetCardinality):
            return SetCardinality(go(expr.set_expr, bound))
        if isinstance(expr, DictGet):
            return DictGet(go(expr.dict_expr, bound), go(expr.key, bound), go(expr.default, bound) if expr.default else None)
        if isinstance(expr, DictSet):
            return DictSet(go(expr.dict_expr, bound), go(expr.key, bound), go(expr.value, bound))
        if isinstance(expr, DictKeys):
            return DictKeys(go(expr.dict_expr, bound))
        if isinstance(expr, DictValues):
            return DictValues(go(expr.dict_expr, bound))
        if isinstance(expr, DictContains):
            return DictContains(go(expr.dict_expr, bound), go(expr.key, bound))
        if isinstance(expr, ListComprehension):
            # Avoid rewriting the element_var binder.
            new_bound = set(bound)
            new_bound.add(expr.element_var.name)
            return ListComprehension(go(expr.element_expr, new_bound), expr.element_var, go(expr.iterable, bound),
                                     go(expr.predicate, new_bound) if expr.predicate else None)
        if isinstance(expr, SetComprehension):
            new_bound = set(bound)
            new_bound.add(expr.element_var.name)
            return SetComprehension(expr.element_var, go(expr.source, bound), go(expr.predicate, new_bound) if expr.predicate else None)
        if isinstance(expr, DictComprehension):
            new_bound = set(bound)
            new_bound.add(expr.element_var.name)
            return DictComprehension(
                go(expr.key_expr, new_bound),
                go(expr.value_expr, new_bound),
                expr.element_var,
                go(expr.iterable, bound),
                go(expr.predicate, new_bound) if expr.predicate else None,
            )
        if isinstance(expr, FieldAccess):
            return FieldAccess(go(expr.obj, bound), expr.field)
        if isinstance(expr, MethodCall):
            return MethodCall(go(expr.obj, bound), expr.method_name, [go(a, bound) for a in expr.args])
        raise Exception(f"old(...) rewrite not implemented for {type(expr).__name__}")

    return go(e, set())


def contains_heap_placeholders_expr(e: Expr) -> bool:
    if isinstance(e, FunctionCall) and isinstance(e.func_name, Var) and e.func_name.name in ("__list_lit", "__dict_lit"):
        return True
    for child_name in getattr(e, "__dict__", {}).keys():
        child = getattr(e, child_name)
        if isinstance(child, Expr) and contains_heap_placeholders_expr(child):
            return True
        if isinstance(child, list):
            for c in child:
                if isinstance(c, Expr) and contains_heap_placeholders_expr(c):
                    return True
    return False


def contains_heap_placeholders_stmt(s: Stmt) -> bool:
    if isinstance(s, Assign) and isinstance(s.expr, Expr) and contains_heap_placeholders_expr(s.expr):
        return True
    if isinstance(s, Seq):
        return contains_heap_placeholders_stmt(s.s1) or contains_heap_placeholders_stmt(s.s2)
    if isinstance(s, If):
        return (contains_heap_placeholders_expr(s.cond) or
                contains_heap_placeholders_stmt(s.lb) or
                contains_heap_placeholders_stmt(s.rb))
    if isinstance(s, While):
        return (any(contains_heap_placeholders_expr(i) for i in s.invariants) or
                contains_heap_placeholders_expr(s.cond) or
                contains_heap_placeholders_stmt(s.body))
    if isinstance(s, (Assert, Assume)):
        return contains_heap_placeholders_expr(s.e)
    if isinstance(s, FieldAssignStmt):
        return contains_heap_placeholders_expr(s.obj) or contains_heap_placeholders_expr(s.value)
    if isinstance(s, SubscriptAssignStmt):
        return (contains_heap_placeholders_expr(s.base) or
                contains_heap_placeholders_expr(s.idx) or
                contains_heap_placeholders_expr(s.value))
    return False
