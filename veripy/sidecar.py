"""
Lightweight sidecar-style metadata decorators inspired by Deppy.

These are metadata-only for now: they let users organize external-library
specifications without forcing a separate proof pipeline into Veripy.
"""

from __future__ import annotations

from typing import Any, Callable


def about(module_path: str):
    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        fn._veripy_about = module_path
        return fn

    return decorator


def proof_for(target: str):
    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        fn._veripy_proof_for = target
        return fn

    return decorator


def z3_hint(**kwargs):
    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        fn._veripy_z3_hint = dict(kwargs)
        return fn

    return decorator


def law(name_or_fn=None, statement: str = "", *, domain: str = ""):
    if callable(name_or_fn):
        fn = name_or_fn
        fn._veripy_law = True
        fn._veripy_law_name = getattr(fn, "__name__", "unnamed")
        fn._veripy_law_statement = statement
        fn._veripy_law_domain = domain
        return fn

    if isinstance(name_or_fn, str):
        def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
            fn._veripy_law = True
            fn._veripy_law_name = name_or_fn
            fn._veripy_law_statement = statement
            fn._veripy_law_domain = domain
            return fn

        return decorator

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        fn._veripy_law = True
        fn._veripy_law_name = getattr(fn, "__name__", "unnamed")
        fn._veripy_law_statement = statement
        fn._veripy_law_domain = domain
        return fn

    return decorator
