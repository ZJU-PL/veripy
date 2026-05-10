"""
Lean backend aligned with Veripy's actual VC pipeline.

Unlike the earlier source-to-source exporter, this backend compiles the
heap-lowered weakest-precondition obligations that Veripy actually proves.
The emitted Lean file is therefore a rendering of the same logical formulas,
not a separate interpretation of raw Python syntax.
"""

from __future__ import annotations

import ast
import inspect
import json
import re
import shutil
import subprocess
import tempfile
import textwrap
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple

from veripy import typecheck as tc
from veripy.contracts import extract_spec
from veripy.core.heap_lowering import (
    HeapEnv,
    HeapLowerer,
    global_heap_vars,
    heap_short_name,
    infer_field_tags,
    sorted_heap_vars,
    uf_name,
)
from veripy.core.verify import (
    STORE,
    _add_builtin_axioms,
    _and_expr,
    _safe_eval_expr,
    collect_assigned_vars,
    fold_constraints,
    generate_refinement_constraints,
    instantiate_refinement,
    parse_func_types,
    wp,
)
from veripy.core.transformer import StmtTranslator
from veripy.parser.syntax import *
from veripy.typecheck.type_check import issubtype


class LeanTranslationError(Exception):
    """Raised when Lean export cannot faithfully render a VC artifact."""


@dataclass(frozen=True)
class LeanType:
    kind: str
    args: Tuple["LeanType", ...] = ()


INT_TY = LeanType("Int")
PROP_TY = LeanType("Prop")
STRING_TY = LeanType("String")


def ARRAY_TY(dom: LeanType, rng: LeanType) -> LeanType:
    return LeanType("SArray", (dom, rng))


def _render_type(ty: LeanType) -> str:
    if ty.kind in {"Int", "Prop", "String"}:
        return ty.kind
    if ty.kind == "SArray":
        return f"(SArray {_render_type(ty.args[0])} {_render_type(ty.args[1])})"
    raise LeanTranslationError(f"unsupported Lean type: {ty}")


def _safe_name(name: str) -> str:
    out = re.sub(r"[^0-9A-Za-z_]", "_", name)
    if not out:
        out = "x"
    if out[0].isdigit():
        out = f"v_{out}"
    return out


def _safe_module_name(name: str) -> str:
    return _safe_name(name or "VeripyExport")


def _heap_var_type(name: str) -> LeanType:
    if name == "__heap_list_len":
        return ARRAY_TY(INT_TY, INT_TY)
    if name.startswith("__heap_list_data_"):
        elem = name.split("__heap_list_data_", 1)[1]
        return ARRAY_TY(INT_TY, ARRAY_TY(INT_TY, _tag_to_type(elem)))
    if name.startswith("__heap_dict_dom_"):
        key = name.split("__heap_dict_dom_", 1)[1]
        return ARRAY_TY(INT_TY, ARRAY_TY(_tag_to_type(key), PROP_TY))
    if name.startswith("__heap_dict_map_"):
        rest = name.split("__heap_dict_map_", 1)[1]
        key_tag, val_tag = rest.split("_", 1)
        return ARRAY_TY(INT_TY, ARRAY_TY(_tag_to_type(key_tag), _tag_to_type(val_tag)))
    if name.startswith("__heap_field_"):
        tag = name.split("__heap_field_", 1)[1]
        return ARRAY_TY(INT_TY, ARRAY_TY(STRING_TY, _tag_to_type(tag)))
    raise LeanTranslationError(f"unknown heap variable: {name}")


def _tag_to_type(tag: str) -> LeanType:
    if tag in {"int", "ref"}:
        return INT_TY
    if tag == "bool":
        return PROP_TY
    if tag == "str":
        return STRING_TY
    raise LeanTranslationError(f"unsupported heap tag: {tag}")


def _veripy_type_to_lean(ty: Any) -> LeanType:
    base = ty.base_type if isinstance(ty, tc.types.TREFINED) else ty
    if base == tc.types.TINT:
        return INT_TY
    if base == tc.types.TBOOL:
        return PROP_TY
    if base is str:
        return STRING_TY
    if isinstance(base, tc.types.TARR) or isinstance(base, tc.types.TDICT):
        return INT_TY
    if isinstance(base, tc.types.TSET):
        return ARRAY_TY(_veripy_type_to_lean(base.elem_ty), PROP_TY)
    return INT_TY


def _normalize_old_vars(expr: Expr) -> Expr:
    def go(e: Expr, bound: Set[str]) -> Expr:
        if isinstance(e, Var):
            if e.name in bound:
                return e
            return Var(e.name[:-4] if e.name.endswith("$old") else e.name)
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
            fn = go(e.func_name, bound) if isinstance(e.func_name, Expr) else e.func_name
            return FunctionCall(fn, [go(a, bound) for a in e.args], native=getattr(e, "native", True))
        if isinstance(e, Quantification):
            new_bound = set(bound)
            new_bound.add(e.var.name)
            return Quantification(e.var, e.ty, go(e.expr, new_bound))
        if isinstance(e, Old):
            return go(e.expr, bound)
        if isinstance(e, SetLiteral):
            return SetLiteral([go(x, bound) for x in e.elements])
        if isinstance(e, DictLiteral):
            return DictLiteral([go(x, bound) for x in e.keys], [go(x, bound) for x in e.values])
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
            return ListComprehension(go(e.element_expr, new_bound), e.element_var, go(e.iterable, bound), go(e.predicate, new_bound) if e.predicate else None)
        if isinstance(e, SetComprehension):
            new_bound = set(bound)
            new_bound.add(e.element_var.name)
            return SetComprehension(e.element_var, go(e.source, bound), go(e.predicate, new_bound) if e.predicate else None)
        if isinstance(e, DictComprehension):
            new_bound = set(bound)
            new_bound.add(e.element_var.name)
            return DictComprehension(go(e.key_expr, new_bound), go(e.value_expr, new_bound), e.element_var, go(e.iterable, bound), go(e.predicate, new_bound) if e.predicate else None)
        if isinstance(e, FieldAccess):
            return FieldAccess(go(e.obj, bound), e.field)
        if isinstance(e, MethodCall):
            return MethodCall(go(e.obj, bound), e.method_name, [go(a, bound) for a in e.args])
        return e

    return go(expr, set())


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
        raise LeanTranslationError("method calls are not supported by the current verifier")
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
    if isinstance(e, DictComprehension):
        _reject_method_calls_expr(e.key_expr)
        _reject_method_calls_expr(e.value_expr)
        _reject_method_calls_expr(e.iterable)
        if e.predicate:
            _reject_method_calls_expr(e.predicate)
        return


def _reject_user_calls(stmt: Stmt, scope_funcs: dict):
    def is_user_fn_call(call: FunctionCall) -> bool:
        return isinstance(call.func_name, Var) and call.func_name.name in scope_funcs and not call.func_name.name.startswith("__")

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
                raise LeanTranslationError("user calls are only supported as x = f(...) in the current verifier")
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
            raise LeanTranslationError("method calls are not supported by the current verifier")
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
        raise LeanTranslationError(f"call restriction check not implemented for {type(e).__name__}")

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
        if isinstance(s, (SubscriptAssignStmt, FieldAssignStmt)):
            raise LeanTranslationError("internal error: heap lowering left mutating statements behind")

    visit_stmt(stmt)


@dataclass
class VerificationArtifacts:
    func_name: str
    check_precondition: Expr
    side_conditions: List[Expr]
    scope_funcs: dict
    fn_return_types: dict
    var_types: Dict[str, LeanType]
    used_heap_vars: List[str]
    summary_attrs: dict


def _bootstrap_func_attrs(fn: Callable[..., Any]) -> dict:
    parsed = parse_func_types(fn)
    spec = extract_spec(fn)
    return {
        "inputs": parsed[1],
        "requires": list(spec["requires"]),
        "ensures": list(spec["ensures"]),
        "returns": parsed[2],
        "decreases": spec["decreases"],
        "verified": True,
    }


def _build_verification_artifacts(fn: Callable[..., Any]) -> VerificationArtifacts:
    code = textwrap.dedent(inspect.getsource(fn))
    func_ast = ast.parse(code)
    target_language_ast = StmtTranslator().visit(func_ast)

    attrs = STORE.func_attrs_global.get(fn.__name__)
    if attrs is not None:
        inputs = list(attrs.get("inputs", {}).items())
        requires = list(attrs.get("requires", []))
        ensures = list(attrs.get("ensures", []))
    else:
        spec = extract_spec(fn)
        parsed = parse_func_types(fn)
        inputs = list(parsed[1].items())
        requires = spec["requires"]
        ensures = spec["ensures"]
        attrs = {
            **_bootstrap_func_attrs(fn),
            "requires": requires,
            "ensures": ensures,
        }

    scope_funcs = dict(STORE.func_attrs_global)
    scope_funcs.setdefault(fn.__name__, attrs)
    STORE.func_attrs_global.setdefault(fn.__name__, attrs)
    for name, value in fn.__globals__.items():
        if not callable(value):
            continue
        if not (hasattr(value, "_veripy_requires") or hasattr(value, "_veripy_ensures") or value.__name__ == fn.__name__):
            continue
        boot = _bootstrap_func_attrs(value)
        scope_funcs.setdefault(value.__name__, boot)
        STORE.func_attrs_global.setdefault(value.__name__, boot)
    sigma = tc.type_check_stmt(dict(attrs["inputs"]), scope_funcs, target_language_ast)
    if "ans" in sigma and not issubtype(sigma["ans"], attrs["returns"]):
        raise LeanTranslationError(f"return type mismatch in {fn.__name__}")

    param_ref_preds = []
    for n, ty in attrs["inputs"].items():
        refin = instantiate_refinement(n, ty)
        if refin is not None:
            param_ref_preds.append(refin)
    param_ref_conj = fold_constraints(param_ref_preds) if param_ref_preds else Literal(VBool(True))

    user_precond = fold_constraints(requires)
    if param_ref_preds:
        user_precond = BinOp(param_ref_conj, BoolOps.And, user_precond)
    user_postcond = fold_constraints(ensures)
    ret_ref = instantiate_refinement("ans", attrs["returns"])
    if ret_ref is not None:
        user_postcond = BinOp(user_postcond, BoolOps.And, ret_ref)

    sigma_with_ans = dict(sigma)
    sigma_with_ans["ans"] = attrs["returns"]
    refinement_constraints = generate_refinement_constraints(sigma, scope_funcs)
    pre_with_refinements = user_precond
    if refinement_constraints:
        refinement_conj = fold_constraints(refinement_constraints)
        pre_with_refinements = BinOp(pre_with_refinements, BoolOps.And, refinement_conj)

    sigma_for_lower = dict(sigma)
    sigma_for_lower["ans"] = attrs["returns"]
    field_tags = infer_field_tags(target_language_ast, sigma_for_lower, scope_funcs)
    heap_vars = global_heap_vars()
    lowerer = HeapLowerer(HeapEnv(sigma_for_lower, scope_funcs, field_tags, heap_vars))
    target_language_ast = lowerer.lower_stmt(target_language_ast)
    pre_with_refinements = lowerer.lower_expr(pre_with_refinements, rewrite_user_calls=True)
    user_postcond = lowerer.lower_expr(user_postcond, rewrite_user_calls=True)

    _reject_method_calls_expr(pre_with_refinements)
    _reject_method_calls_expr(user_postcond)
    _reject_user_calls(target_language_ast, scope_funcs)

    rebound = set(attrs.get("inputs", {}).keys()).intersection(collect_assigned_vars(target_language_ast))
    if rebound:
        raise LeanTranslationError(f"rebound parameters are not supported: {sorted(rebound)}")

    pre_with_refinements = _and_expr(_safe_eval_expr(pre_with_refinements), pre_with_refinements)
    user_postcond = _and_expr(_safe_eval_expr(user_postcond), user_postcond)

    heap_writes = {v for v in collect_assigned_vars(target_language_ast) if isinstance(v, str) and v.startswith("__heap_")}
    attrs["heap_writes"] = heap_writes
    attrs["pre_lowered"] = pre_with_refinements
    attrs["post_lowered"] = user_postcond

    P, C = wp(sigma_for_lower, target_language_ast, user_postcond)
    check_P = BinOp(pre_with_refinements, BoolOps.Implies, P)

    var_types: Dict[str, LeanType] = {}
    for name, ty in sigma_for_lower.items():
        var_types[name] = _veripy_type_to_lean(ty)
    for h in heap_vars:
        var_types[h] = _heap_var_type(h)
    for r in getattr(lowerer, "fresh_refs", set()):
        var_types[r] = INT_TY
    for name, ty in list(var_types.items()):
        var_types[name + "$old"] = ty

    fn_return_types = {
        n: _veripy_type_to_lean(a.get("returns", tc.types.TINT))
        for n, a in scope_funcs.items()
    }

    return VerificationArtifacts(
        func_name=fn.__name__,
        check_precondition=_normalize_old_vars(check_P),
        side_conditions=[_normalize_old_vars(c) for c in C],
        scope_funcs=scope_funcs,
        fn_return_types=fn_return_types,
        var_types=var_types,
        used_heap_vars=sorted_heap_vars(heap_vars),
        summary_attrs=attrs,
    )


def _is_summary_uf(name: str) -> Optional[Tuple[str, str]]:
    if not name.startswith("__uf_"):
        return None
    rest = name[len("__uf_"):]
    if "__" not in rest:
        return None
    return rest.rsplit("__", 1)


def _summary_result_type(name: str, fn_return_types: Dict[str, LeanType]) -> LeanType:
    parsed = _is_summary_uf(name)
    if parsed is None:
        return fn_return_types.get(name, INT_TY)
    user_fn, out = parsed
    if out == "ans":
        return fn_return_types.get(user_fn, INT_TY)
    return _heap_var_type("__" + out)


def _collect_calls(expr: Expr) -> List[FunctionCall]:
    out: List[FunctionCall] = []

    def go(e: Expr):
        if isinstance(e, (Var, Literal, StringLiteral)):
            return
        if isinstance(e, UnOp):
            go(e.e)
            return
        if isinstance(e, BinOp):
            go(e.e1)
            go(e.e2)
            return
        if isinstance(e, Subscript):
            go(e.var)
            go(e.subscript)
            return
        if isinstance(e, Store):
            go(e.arr)
            go(e.idx)
            go(e.val)
            return
        if isinstance(e, FunctionCall):
            out.append(e)
            if isinstance(e.func_name, Expr):
                go(e.func_name)
            for a in e.args:
                if isinstance(a, Expr):
                    go(a)
            return
        if isinstance(e, Quantification):
            go(e.expr)
            return
        if isinstance(e, Old):
            go(e.expr)
            return
        if isinstance(e, SetLiteral):
            for x in e.elements:
                go(x)
            return
        if isinstance(e, DictLiteral):
            for x in e.keys:
                go(x)
            for x in e.values:
                go(x)
            return
        if isinstance(e, SetOp):
            go(e.left)
            go(e.right)
            return
        if isinstance(e, SetCardinality):
            go(e.set_expr)
            return
        if isinstance(e, DictGet):
            go(e.dict_expr)
            go(e.key)
            if e.default:
                go(e.default)
            return
        if isinstance(e, DictSet):
            go(e.dict_expr)
            go(e.key)
            go(e.value)
            return
        if isinstance(e, DictKeys):
            go(e.dict_expr)
            return
        if isinstance(e, DictValues):
            go(e.dict_expr)
            return
        if isinstance(e, DictContains):
            go(e.dict_expr)
            go(e.key)
            return
        if isinstance(e, FieldAccess):
            go(e.obj)
            return
        if isinstance(e, MethodCall):
            go(e.obj)
            for a in e.args:
                go(a)
            return
        if isinstance(e, ListComprehension):
            go(e.element_expr)
            go(e.iterable)
            if e.predicate:
                go(e.predicate)
            return
        if isinstance(e, SetComprehension):
            go(e.source)
            if e.predicate:
                go(e.predicate)
            return
        if isinstance(e, DictComprehension):
            go(e.key_expr)
            go(e.value_expr)
            go(e.iterable)
            if e.predicate:
                go(e.predicate)

    go(expr)
    return out


def _infer_expr_type(expr: Expr, var_types: Dict[str, LeanType], fn_return_types: Dict[str, LeanType]) -> LeanType:
    if isinstance(expr, Var):
        ty = var_types.get(expr.name)
        if ty is None:
            raise LeanTranslationError(f"missing type for variable {expr.name}")
        return ty
    if isinstance(expr, Literal):
        if isinstance(expr.value, VInt):
            return INT_TY
        if isinstance(expr.value, VBool):
            return PROP_TY
        if isinstance(expr.value, VString):
            return STRING_TY
        if isinstance(expr.value, VSet):
            return ARRAY_TY(INT_TY, PROP_TY)
        if isinstance(expr.value, VDict):
            return ARRAY_TY(INT_TY, INT_TY)
        if isinstance(expr.value, VList):
            return ARRAY_TY(INT_TY, INT_TY)
    if isinstance(expr, StringLiteral):
        return STRING_TY
    if isinstance(expr, UnOp):
        return PROP_TY if expr.op == BoolOps.Not else INT_TY
    if isinstance(expr, BinOp):
        if isinstance(expr.op, ArithOps):
            return INT_TY
        return PROP_TY
    if isinstance(expr, Quantification):
        return PROP_TY
    if isinstance(expr, Subscript):
        arr_ty = _infer_expr_type(expr.var, var_types, fn_return_types)
        if arr_ty.kind != "SArray":
            raise LeanTranslationError(f"subscripted non-array expression: {expr.var}")
        return arr_ty.args[1]
    if isinstance(expr, Store):
        return _infer_expr_type(expr.arr, var_types, fn_return_types)
    if isinstance(expr, FunctionCall):
        if isinstance(expr.func_name, Var):
            fname = expr.func_name.name
        else:
            fname = str(expr.func_name)
        if fname in {"len", "card", "__dict_len"}:
            return INT_TY
        if fname == "set":
            return ARRAY_TY(INT_TY, PROP_TY)
        if fname == "dict":
            return ARRAY_TY(INT_TY, INT_TY)
        if fname == "keys":
            return ARRAY_TY(INT_TY, PROP_TY)
        if fname == "str":
            return STRING_TY
        return _summary_result_type(fname, fn_return_types)
    if isinstance(expr, SetLiteral):
        elem_ty = INT_TY if not expr.elements else _infer_expr_type(expr.elements[0], var_types, fn_return_types)
        return ARRAY_TY(elem_ty, PROP_TY)
    if isinstance(expr, DictLiteral):
        key_ty = INT_TY if not expr.keys else _infer_expr_type(expr.keys[0], var_types, fn_return_types)
        val_ty = INT_TY if not expr.values else _infer_expr_type(expr.values[0], var_types, fn_return_types)
        return ARRAY_TY(key_ty, val_ty)
    if isinstance(expr, SetOp):
        return PROP_TY if expr.op in {SetOps.Member, SetOps.Subset, SetOps.Superset} else _infer_expr_type(expr.left, var_types, fn_return_types)
    if isinstance(expr, SetCardinality):
        return INT_TY
    if isinstance(expr, DictGet):
        dict_ty = _infer_expr_type(expr.dict_expr, var_types, fn_return_types)
        return dict_ty.args[1] if dict_ty.kind == "SArray" else INT_TY
    if isinstance(expr, DictSet):
        return _infer_expr_type(expr.dict_expr, var_types, fn_return_types)
    if isinstance(expr, DictKeys):
        dict_ty = _infer_expr_type(expr.dict_expr, var_types, fn_return_types)
        key_ty = dict_ty.args[0] if dict_ty.kind == "SArray" else INT_TY
        return ARRAY_TY(key_ty, PROP_TY)
    if isinstance(expr, DictValues):
        return ARRAY_TY(INT_TY, PROP_TY)
    if isinstance(expr, DictContains):
        return PROP_TY
    raise LeanTranslationError(f"cannot infer Lean type for {type(expr).__name__}")


def _render_string(value: str) -> str:
    return json.dumps(value)


def _translate_expr(expr: Expr, var_types: Dict[str, LeanType], fn_return_types: Dict[str, LeanType]) -> str:
    def go(e: Expr) -> str:
        if isinstance(e, Var):
            return _safe_name(e.name)
        if isinstance(e, Literal):
            if isinstance(e.value, VInt):
                return str(int(e.value.v))
            if isinstance(e.value, VBool):
                return "True" if bool(e.value.v) else "False"
            if isinstance(e.value, VString):
                return _render_string(e.value.v)
            if isinstance(e.value, VSet):
                return "(const False)"
            if isinstance(e.value, VDict):
                return "(const 0)"
        if isinstance(e, StringLiteral):
            return _render_string(e.value)
        if isinstance(e, UnOp):
            inner = go(e.e)
            if e.op == BoolOps.Not:
                return f"(¬ {inner})"
            if e.op == ArithOps.Neg:
                return f"(-{inner})"
        if isinstance(e, BinOp):
            lhs = go(e.e1)
            rhs = go(e.e2)
            if e.op == ArithOps.Add:
                return f"({lhs} + {rhs})"
            if e.op == ArithOps.Minus:
                return f"({lhs} - {rhs})"
            if e.op == ArithOps.Mult:
                return f"({lhs} * {rhs})"
            if e.op == ArithOps.IntDiv:
                return f"({lhs} / {rhs})"
            if e.op == ArithOps.Mod:
                return f"({lhs} % {rhs})"
            if e.op == BoolOps.And:
                return f"({lhs} ∧ {rhs})"
            if e.op == BoolOps.Or:
                return f"({lhs} ∨ {rhs})"
            if e.op == BoolOps.Implies:
                return f"({lhs} → {rhs})"
            if e.op == BoolOps.Iff:
                return f"({lhs} ↔ {rhs})"
            lhs_ty = _infer_expr_type(e.e1, var_types, fn_return_types)
            if e.op == CompOps.Eq:
                return f"({lhs} ↔ {rhs})" if lhs_ty == PROP_TY else f"({lhs} = {rhs})"
            if e.op == CompOps.Neq:
                return f"(¬ ({lhs} ↔ {rhs}))" if lhs_ty == PROP_TY else f"({lhs} ≠ {rhs})"
            if e.op == CompOps.Lt:
                return f"({lhs} < {rhs})"
            if e.op == CompOps.Le:
                return f"({lhs} ≤ {rhs})"
            if e.op == CompOps.Gt:
                return f"({lhs} > {rhs})"
            if e.op == CompOps.Ge:
                return f"({lhs} ≥ {rhs})"
            if e.op == CompOps.In:
                rhs_ty = _infer_expr_type(e.e2, var_types, fn_return_types)
                if rhs_ty.kind == "SArray" and rhs_ty.args[1] == PROP_TY:
                    return f"({rhs} {lhs})"
                return f"(arr_contains_int {rhs} {lhs})"
            if e.op == CompOps.NotIn:
                rhs_ty = _infer_expr_type(e.e2, var_types, fn_return_types)
                if rhs_ty.kind == "SArray" and rhs_ty.args[1] == PROP_TY:
                    return f"(¬ ({rhs} {lhs}))"
                return f"(¬ (arr_contains_int {rhs} {lhs}))"
        if isinstance(e, Quantification):
            bound_ty = _veripy_type_to_lean(e.ty)
            new_var_types = dict(var_types)
            new_var_types[e.var.name] = bound_ty
            return f"(∀ ({_safe_name(e.var.name)} : {_render_type(bound_ty)}), {_translate_expr(e.expr, new_var_types, fn_return_types)})"
        if isinstance(e, Subscript):
            return f"({go(e.var)} {go(e.subscript)})"
        if isinstance(e, Store):
            return f"(store {go(e.arr)} {go(e.idx)} {go(e.val)})"
        if isinstance(e, FunctionCall):
            fn = _safe_name(e.func_name.name if isinstance(e.func_name, Var) else str(e.func_name))
            args = " ".join(go(a) for a in e.args)
            return f"({fn} {args})" if args else fn
        if isinstance(e, SetLiteral):
            if not e.elements:
                return "(const False)"
            result = "(const False)"
            for element in e.elements:
                result = f"(store {result} {go(element)} True)"
            return result
        if isinstance(e, DictLiteral):
            if not e.keys:
                return "(const 0)"
            result = "(const 0)"
            for k, v in zip(e.keys, e.values):
                result = f"(store {result} {go(k)} {go(v)})"
            return result
        if isinstance(e, SetCardinality):
            return f"(card {go(e.set_expr)})"
        if isinstance(e, DictGet):
            return f"({go(e.dict_expr)} {go(e.key)})"
        if isinstance(e, DictSet):
            return f"(store {go(e.dict_expr)} {go(e.key)} {go(e.value)})"
        if isinstance(e, DictKeys):
            return f"(keys {go(e.dict_expr)})"
        if isinstance(e, DictValues):
            return f"(dictValues {go(e.dict_expr)})"
        if isinstance(e, DictContains):
            return f"(({go(e.dict_expr)}) {go(e.key)})"
        raise LeanTranslationError(f"unsupported expression form in Lean translation: {type(e).__name__}")

    return go(expr)


def _collect_free_vars(expr: Expr) -> List[str]:
    seen: Set[str] = set()
    ordered: List[str] = []

    def go(e: Expr, bound: Set[str]):
        if isinstance(e, Var):
            if e.name not in bound and e.name not in seen:
                seen.add(e.name)
                ordered.append(e.name)
            return
        if isinstance(e, (Literal, StringLiteral)):
            return
        if isinstance(e, UnOp):
            go(e.e, bound)
            return
        if isinstance(e, BinOp):
            go(e.e1, bound)
            go(e.e2, bound)
            return
        if isinstance(e, Subscript):
            go(e.var, bound)
            go(e.subscript, bound)
            return
        if isinstance(e, Store):
            go(e.arr, bound)
            go(e.idx, bound)
            go(e.val, bound)
            return
        if isinstance(e, FunctionCall):
            if isinstance(e.func_name, Expr) and not isinstance(e.func_name, Var):
                go(e.func_name, bound)
            for a in e.args:
                go(a, bound)
            return
        if isinstance(e, Quantification):
            new_bound = set(bound)
            new_bound.add(e.var.name)
            go(e.expr, new_bound)
            return
        if isinstance(e, Old):
            go(e.expr, bound)
            return
        if isinstance(e, SetLiteral):
            for x in e.elements:
                go(x, bound)
            return
        if isinstance(e, DictLiteral):
            for x in e.keys:
                go(x, bound)
            for x in e.values:
                go(x, bound)
            return
        if isinstance(e, SetOp):
            go(e.left, bound)
            go(e.right, bound)
            return
        if isinstance(e, SetCardinality):
            go(e.set_expr, bound)
            return
        if isinstance(e, DictGet):
            go(e.dict_expr, bound)
            go(e.key, bound)
            if e.default:
                go(e.default, bound)
            return
        if isinstance(e, DictSet):
            go(e.dict_expr, bound)
            go(e.key, bound)
            go(e.value, bound)
            return
        if isinstance(e, DictKeys):
            go(e.dict_expr, bound)
            return
        if isinstance(e, DictValues):
            go(e.dict_expr, bound)
            return
        if isinstance(e, DictContains):
            go(e.dict_expr, bound)
            go(e.key, bound)
            return

    go(expr, set())
    return ordered


def _contains_div_mod(expr: Expr) -> bool:
    if isinstance(expr, BinOp):
        if expr.op in {ArithOps.IntDiv, ArithOps.Mod}:
            return True
        return _contains_div_mod(expr.e1) or _contains_div_mod(expr.e2)
    if isinstance(expr, UnOp):
        return _contains_div_mod(expr.e)
    if isinstance(expr, Subscript):
        return _contains_div_mod(expr.var) or _contains_div_mod(expr.subscript)
    if isinstance(expr, Store):
        return _contains_div_mod(expr.arr) or _contains_div_mod(expr.idx) or _contains_div_mod(expr.val)
    if isinstance(expr, FunctionCall):
        return any(_contains_div_mod(a) for a in e.args if isinstance(a, Expr)) if False else any(_contains_div_mod(a) for a in expr.args if isinstance(a, Expr))
    if isinstance(expr, Quantification):
        return _contains_div_mod(expr.expr)
    if isinstance(expr, SetLiteral):
        return any(_contains_div_mod(x) for x in expr.elements)
    if isinstance(expr, DictLiteral):
        return any(_contains_div_mod(x) for x in expr.keys + expr.values)
    if isinstance(expr, SetOp):
        return _contains_div_mod(expr.left) or _contains_div_mod(expr.right)
    if isinstance(expr, SetCardinality):
        return _contains_div_mod(expr.set_expr)
    if isinstance(expr, DictGet):
        return _contains_div_mod(expr.dict_expr) or _contains_div_mod(expr.key) or (_contains_div_mod(expr.default) if expr.default else False)
    if isinstance(expr, DictSet):
        return _contains_div_mod(expr.dict_expr) or _contains_div_mod(expr.key) or _contains_div_mod(expr.value)
    if isinstance(expr, (DictKeys, DictValues)):
        return _contains_div_mod(expr.dict_expr)
    if isinstance(expr, DictContains):
        return _contains_div_mod(expr.dict_expr) or _contains_div_mod(expr.key)
    return False


def _is_arithmetic_formula(expr: Expr) -> bool:
    if isinstance(expr, (Var, Literal, StringLiteral)):
        return True
    if isinstance(expr, UnOp):
        return _is_arithmetic_formula(expr.e)
    if isinstance(expr, BinOp):
        if isinstance(expr.op, (ArithOps, CompOps, BoolOps)):
            return _is_arithmetic_formula(expr.e1) and _is_arithmetic_formula(expr.e2)
        return False
    return False


def _summary_hypothesis(name: str, attrs: dict, fn_return_types: Dict[str, LeanType], heap_vars: List[str], var_types: Dict[str, LeanType]) -> str:
    req_expr = _normalize_old_vars(attrs.get("pre_lowered"))
    ens_expr = _normalize_old_vars(attrs.get("post_lowered"))
    if req_expr is None or ens_expr is None:
        raise LeanTranslationError(f"missing lowered contracts for summary {name}")

    local_types = dict(var_types)
    parts: List[str] = []
    for param, ty in attrs.get("inputs", {}).items():
        local_types[param] = _veripy_type_to_lean(ty)
        parts.append(f"({_safe_name(param)} : {_render_type(local_types[param])})")
    for heap in heap_vars:
        local_types[heap] = _heap_var_type(heap)
        parts.append(f"({_safe_name(heap)} : {_render_type(local_types[heap])})")

    req_text = _translate_expr(req_expr, local_types, fn_return_types)
    post_types = dict(local_types)
    post_types["ans"] = fn_return_types.get(name, INT_TY)
    fn_sym = _safe_name(uf_name(name, "ans"))
    call_args = " ".join(_safe_name(p) for p in attrs.get("inputs", {}).keys()) + (" " if attrs.get("inputs") else "")
    call_args += " ".join(_safe_name(h) for h in heap_vars)
    post_types["ans"] = fn_return_types.get(name, INT_TY)
    # Replace the result and heap post-state names the same way as the SMT summary axiom.
    ens_text = _translate_expr(ens_expr, post_types, fn_return_types).replace("ans", f"({fn_sym} {call_args})")

    frame_terms = []
    writes = attrs.get("heap_writes", set()) or set()
    for heap in heap_vars:
        if heap not in writes:
            frame_terms.append(f"({_safe_name(uf_name(name, heap_short_name(heap)))} {' '.join(_safe_name(p) for p in attrs.get('inputs', {}).keys())} {' '.join(_safe_name(h) for h in heap_vars)} = {_safe_name(heap)})")
    body = ens_text if not frame_terms else f"({ens_text} ∧ {' ∧ '.join(frame_terms)})"
    quantified = " ".join(parts)
    return f"(∀ {quantified}, {req_text} → {body})"


@dataclass
class LeanTheorem:
    name: str
    proposition: str
    binders: List[str]
    proof: str


@dataclass
class LeanCertificate:
    module_name: str
    source_name: str
    declarations: List[str] = field(default_factory=list)
    theorems: List[LeanTheorem] = field(default_factory=list)
    obligations: List[str] = field(default_factory=list)
    trust_level: str = "LEAN_EXPORTED"
    proved_count: int = 0
    sorry_count: int = 0
    lean_stdout: str = ""
    lean_stderr: str = ""

    def render(self) -> str:
        theorem_chunks = []
        for thm in self.theorems:
            binder_text = " ".join(thm.binders)
            header = f"theorem {thm.name}"
            if binder_text:
                header += f" {binder_text}"
            theorem_chunks.append(f"{header} : {thm.proposition} :=\n{thm.proof}")
        sections = [
            "/- Auto-generated by Veripy's VC-aligned Lean backend. -/",
            "import Std",
            "import Std.Tactic.Omega",
            "",
            "open Classical",
            "",
            f"namespace {self.module_name}",
            "",
            "def SArray (α : Type) (β : Sort _) := α → β",
            "def const {α : Type} {β : Sort _} (v : β) : SArray α β := fun _ => v",
            "def store {α : Type} {β : Sort _} [DecidableEq α] (a : SArray α β) (i : α) (v : β) : SArray α β :=",
            "  fun j => if j = i then v else a j",
            "",
            "opaque card : SArray Int Prop → Int",
            "opaque __dict_len : SArray Int Prop → Int",
            "opaque arr_contains_int : SArray Int Int → Int → Prop",
            "opaque dictValues : SArray Int Int → SArray Int Prop",
            "",
            *self.declarations,
            "",
            *theorem_chunks,
            "",
            f"end {self.module_name}",
            "",
        ]
        return "\n".join(sections)

    def write(self, output_path: str | Path) -> Path:
        path = Path(output_path)
        path.write_text(self.render(), encoding="utf-8")
        return path

    @property
    def is_syntax_complete(self) -> bool:
        return self.sorry_count == 0

    @property
    def is_kernel_verified(self) -> bool:
        return self.trust_level == "LEAN_KERNEL_VERIFIED"

    def summary(self) -> str:
        return "\n".join([
            f"LeanCertificate {self.module_name}",
            f"  theorems: {len(self.theorems)}",
            f"  proved: {self.proved_count}",
            f"  sorry: {self.sorry_count}",
            f"  trust: {self.trust_level}",
        ])

    def verify_with_lean(self, *, lean_cmd: Optional[str] = None, timeout_s: int = 60) -> "LeanCertificate":
        lean_bin = lean_cmd or shutil.which("lean")
        if not lean_bin:
            self.trust_level = "LEAN_UNAVAILABLE"
            self.lean_stderr = "lean binary not found on PATH"
            return self

        with tempfile.TemporaryDirectory(prefix="veripy-lean-") as tmpdir:
            path = Path(tmpdir) / f"{self.module_name}.lean"
            path.write_text(self.render(), encoding="utf-8")
            try:
                proc = subprocess.run([lean_bin, str(path)], capture_output=True, text=True, timeout=timeout_s, check=False)
            except (FileNotFoundError, PermissionError, OSError) as exc:
                self.trust_level = "LEAN_UNAVAILABLE"
                self.lean_stderr = str(exc)
                return self
            except subprocess.TimeoutExpired as exc:
                self.trust_level = "LEAN_REJECTED"
                self.lean_stdout = exc.stdout or ""
                self.lean_stderr = (exc.stderr or "") + f"\n<timeout after {timeout_s}s>"
                return self

        self.lean_stdout = proc.stdout
        self.lean_stderr = proc.stderr
        self.trust_level = "LEAN_KERNEL_VERIFIED" if proc.returncode == 0 else "LEAN_REJECTED"
        return self


def compile_to_lean(target: Callable[..., Any], output_path: Optional[str | Path] = None) -> LeanCertificate:
    fn = inspect.unwrap(target)
    if not callable(fn):
        raise TypeError("compile_to_lean expects a Python function")

    artifacts = _build_verification_artifacts(fn)
    module_name = _safe_module_name(fn.__name__.title() + "_vc")

    theorem_exprs = [artifacts.check_precondition, *artifacts.side_conditions]
    needed_calls: List[FunctionCall] = []
    for expr in theorem_exprs:
        needed_calls.extend(_collect_calls(expr))

    declarations: List[str] = []
    declared: Set[Tuple[str, Tuple[str, ...], str]] = set()

    def ensure_decl(name: str, arg_types: List[LeanType], ret_type: LeanType):
        key = (name, tuple(_render_type(t) for t in arg_types), _render_type(ret_type))
        if key in declared:
            return
        declared.add(key)
        arg_sig = " ".join(f"({_safe_name(f'a{i}')} : {_render_type(t)})" for i, t in enumerate(arg_types))
        decl = f"opaque {_safe_name(name)}"
        if arg_sig:
            decl += f" {arg_sig}"
        decl += f" : {_render_type(ret_type)}"
        declarations.append(decl)

    for call in needed_calls:
        if not isinstance(call.func_name, Var):
            raise LeanTranslationError("higher-order function calls are not supported in Lean export")
        fname = call.func_name.name
        if fname in {"len", "card", "__dict_len", "arr_contains_int", "dictValues"}:
            continue
        if fname == "keys":
            ensure_decl("keys", [_infer_expr_type(call.args[0], artifacts.var_types, artifacts.fn_return_types)], ARRAY_TY(INT_TY, PROP_TY))
            continue
        if fname == "str":
            ensure_decl("str", [_infer_expr_type(call.args[0], artifacts.var_types, artifacts.fn_return_types)], STRING_TY)
            continue
        ensure_decl(fname, [_infer_expr_type(arg, artifacts.var_types, artifacts.fn_return_types) for arg in call.args], _summary_result_type(fname, artifacts.fn_return_types))

    summary_names = sorted({
        parsed[0]
        for call in needed_calls
        for parsed in [_is_summary_uf(call.func_name.name if isinstance(call.func_name, Var) else "")]
        if parsed is not None
    })

    summary_binders = []
    for name in summary_names:
        attrs = artifacts.scope_funcs.get(name)
        if not attrs:
            continue
        summary_prop = _summary_hypothesis(name, attrs, artifacts.fn_return_types, artifacts.used_heap_vars, artifacts.var_types)
        summary_binders.append(f"(h_summary_{_safe_name(name)} : {summary_prop})")

    builtin_binders = []
    if any(_contains_div_mod(expr) for expr in theorem_exprs):
        builtin_binders.append("(h_div_mod : ∀ (x y : Int), y ≠ 0 → x = (x / y) * y + (x % y))")
        builtin_binders.append("(h_mod_range : ∀ (x y : Int), y ≠ 0 → 0 ≤ x % y ∧ x % y < (if y ≥ 0 then y else -y))")

    theorems: List[LeanTheorem] = []
    proved_count = 0
    sorry_count = 0

    for index, expr in enumerate(theorem_exprs):
        free_vars = _collect_free_vars(expr)
        binders = [f"({_safe_name(v)} : {_render_type(artifacts.var_types[v])})" for v in free_vars]
        binders.extend(summary_binders)
        binders.extend(builtin_binders)
        prop = _translate_expr(expr, artifacts.var_types, artifacts.fn_return_types)
        theorem_name = f"{_safe_name(fn.__name__)}_vc" if index == 0 else f"{_safe_name(fn.__name__)}_side_condition_{index}"
        if _is_arithmetic_formula(expr) and not summary_binders:
            proof = "by\n  omega"
            proved_count += 1
        else:
            proof = "by\n  sorry"
            sorry_count += 1
        theorems.append(LeanTheorem(theorem_name, prop, binders, proof))

    certificate = LeanCertificate(
        module_name=module_name,
        source_name=getattr(fn, "__qualname__", fn.__name__),
        declarations=declarations,
        theorems=theorems,
        obligations=[f"faithful VC export for {fn.__name__}; proofs using summary assumptions may still require manual Lean work"] if sorry_count else [],
        trust_level="LEAN_SYNTAX_COMPLETE" if sorry_count == 0 else "LEAN_EXPORTED",
        proved_count=proved_count,
        sorry_count=sorry_count,
    )

    if output_path is not None:
        certificate.write(output_path)

    return certificate
