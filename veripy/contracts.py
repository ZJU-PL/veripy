"""
Deppy-style contract decorators layered on top of Veripy.

These helpers let users write stackable contract annotations such as
``@requires("x > 0")`` and ``@guarantee("result > 0")`` and then route
them through Veripy's existing ``@verify`` pipeline.
"""

from __future__ import annotations

import inspect
import re
from typing import Any, Callable, Dict, List, Optional


_RESULT_NAME_RE = re.compile(r"\bresult\b")


def _append_attr(fn: Callable[..., Any], attr: str, values: List[str]) -> Callable[..., Any]:
    existing = list(getattr(fn, attr, []))
    existing.extend(values)
    setattr(fn, attr, existing)
    return fn


def _normalize_postcondition(spec: str) -> str:
    # Deppy examples use `result`; Veripy's VC engine binds the return value as `ans`.
    return _RESULT_NAME_RE.sub("ans", spec)


def _dedupe(values: List[str]) -> List[str]:
    seen = set()
    result: List[str] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            result.append(value)
    return result


def requires(*conditions: str) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    """Attach one or more preconditions to a function."""

    normalized = [str(cond) for cond in conditions]

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        return _append_attr(fn, "_veripy_requires", normalized)

    return decorator


def guarantee(*conditions: str) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    """Attach one or more postconditions using Deppy-style `result` syntax."""

    normalized = [_normalize_postcondition(str(cond)) for cond in conditions]

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        return _append_attr(fn, "_veripy_ensures", normalized)

    return decorator


def ensures(*conditions: str) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    """Alias for `guarantee` for users who prefer explicit postcondition wording."""

    return guarantee(*conditions)


def contract_decreases(measure: str) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    """Decorator form of a termination measure."""

    normalized = str(measure)

    def decorator(fn: Callable[..., Any]) -> Callable[..., Any]:
        setattr(fn, "_veripy_decreases", normalized)
        return fn

    return decorator


def extract_spec(fn: Callable[..., Any]) -> Dict[str, Any]:
    """
    Extract contract metadata from a function, following wrapped functions too.
    """

    unwrapped = inspect.unwrap(fn)
    requires_specs = _dedupe(list(getattr(unwrapped, "_veripy_requires", [])))
    ensures_specs = _dedupe(list(getattr(unwrapped, "_veripy_ensures", [])))
    decreases_measure: Optional[str] = getattr(unwrapped, "_veripy_decreases", None)

    return {
        "requires": requires_specs,
        "ensures": ensures_specs,
        "decreases": decreases_measure,
    }
