"""
Auto-Active Verification Engine for Veripy

This module provides automatic invariant inference and lemma generation
for reducing the burden of manual verification annotations.
"""

import ast
import z3
from typing import List, Dict, Set, Optional, Any, Tuple
from dataclasses import dataclass, field
from enum import Enum
from functools import lru_cache
import inspect
import hashlib

from veripy.parser.syntax import *
from veripy.parser.parser import parse_assertion
from veripy.core.verify import STORE, wp, emit_smt, fold_constraints, declare_consts
from veripy.core.transformer import StmtTranslator, Expr2Z3
from veripy import typecheck as tc
from veripy.typecheck import types as tc_types
from veripy.core.prettyprint import pretty_print


class InferenceStrategy(Enum):
    """Strategy for automatic invariant inference."""
    NONE = "none"
    SIMPLE = "simple"          # Basic bounds and type-based invariants
    AGGRESSIVE = "aggressive"  # More sophisticated inference with SMT
    FULL = "full"             # Maximum inference, may be slow


@dataclass
class InvariantCandidate:
    """A candidate invariant with confidence score."""
    expression: str
    confidence: float  # 0.0 to 1.0
    source: str        # "bounds", "type", "arithmetic", "loop", "custom"
    variables: Set[str] = field(default_factory=set)


class AutoActiveEngine:
    """
    Auto-active verification engine that automatically infers invariants
    and generates lemmas to reduce manual annotation burden.
    
    Inspired by Dafny's auto-active approach, this engine attempts to:
    1. Infer loop invariants from loop structure
    2. Generate arithmetic lemmas for common patterns
    3. Infer type-based constraints
    4. Handle recursive function termination
    """
    
    def __init__(self, solver: z3.Solver = None, strategy: InferenceStrategy = InferenceStrategy.SIMPLE):
        self.solver = solver or z3.Solver()
        self.strategy = strategy
        self.inferred_invariants: Dict[str, List[InvariantCandidate]] = {}
        self.generated_lemmas: List[Dict[str, Any]] = []
        self.cache: Dict[str, bool] = {}
        self.statistics = {
            "invariants_inferred": 0,
            "lemmas_generated": 0,
            "solver_calls": 0,
            "cache_hits": 0
        }
    
    def infer_loop_invariants(self, loop_info: Dict[str, Any]) -> List[str]:
        """
        Automatically infer loop invariants based on loop structure.
        
        This method analyzes the loop and attempts to generate invariants that:
        - Bound loop variables
        - Capture relationship between loop variables
        - Track monotonic properties
        """
        invariants = []
        
        # Extract loop information
        loop_var = loop_info.get("loop_var")
        init_val = loop_info.get("init")
        condition = loop_info.get("condition")
        body = loop_info.get("body", [])
        
        if not loop_var:
            return invariants
        
        # Basic bounds inference
        if ">" in str(condition) or ">=" in str(condition):
            # Loop that decreases a variable
            if isinstance(init_val, (int, float)):
                upper_bound = str(init_val)
                invariants.append(f"{loop_var} >= {upper_bound}")
        
        if "<" in str(condition) or "<=" in str(condition):
            # Loop that increases a variable
            if isinstance(init_val, (int, float)):
                lower_bound = str(init_val)
                invariants.append(f"{loop_var} <= {lower_bound}")
        
        # Type-based invariants
        if self.strategy in (InferenceStrategy.SIMPLE, InferenceStrategy.AGGRESSIVE, InferenceStrategy.FULL):
            # Add integer bounds for loop variables
            invariants.append(f"{loop_var} == {loop_var}")  # Type constraint
            
            # Monotonicity for increment/decrement loops
            if self._is_incrementing_loop(loop_info):
                invariants.append(f"{loop_var} >= {init_val}")
            elif self._is_decrementing_loop(loop_info):
                invariants.append(f"{loop_var} <= {init_val}")
        
        # Advanced inference for aggressive/full strategies
        if self.strategy in (InferenceStrategy.AGGRESSIVE, InferenceStrategy.FULL):
            # Try to infer relational invariants between variables
            relational_invariants = self._infer_relational_invariants(loop_info)
            invariants.extend(relational_invariants)
        
        # Cache the result
        cache_key = f"invariants_{hash(str(loop_info))}"
        self.cache[cache_key] = invariants
        
        return invariants
    
    def _is_incrementing_loop(self, loop_info: Dict[str, Any]) -> bool:
        """Check if loop is incrementing its variable."""
        body = loop_info.get("body", [])
        for stmt in body:
            if isinstance(stmt, dict) and stmt.get("type") == "assign":
                if stmt.get("var") == loop_info.get("loop_var"):
                    rhs = str(stmt.get("expr", ""))
                    if f"{loop_info.get('loop_var')} +" in rhs or f"{loop_info.get('loop_var')} +=" in rhs:
                        return True
        return False
    
    def _is_decrementing_loop(self, loop_info: Dict[str, Any]) -> bool:
        """Check if loop is decrementing its variable."""
        body = loop_info.get("body", [])
        for stmt in body:
            if isinstance(stmt, dict) and stmt.get("type") == "assign":
                if stmt.get("var") == loop_info.get("loop_var"):
                    rhs = str(stmt.get("expr", ""))
                    if f"{loop_info.get('loop_var')} -" in rhs or f"{loop_info.get('loop_var')} -=" in rhs:
                        return True
        return False
    
    def _infer_relational_invariants(self, loop_info: Dict[str, Any]) -> List[str]:
        """Infer relationships between multiple loop variables."""
        invariants = []
        
        loop_var = loop_info.get("loop_var")
        if not loop_var:
            return invariants
        
        # Check for common patterns
        # Pattern: x and y in loop where x + y = constant
        # Pattern: x and y in loop where x * y = constant
        
        body = loop_info.get("body", [])
        variables_in_loop = list(self._collect_variables_in_loop(body))
        
        if len(variables_in_loop) >= 2:
            # Look for sum invariants
            for i, var1 in enumerate(variables_in_loop):
                for var2 in variables_in_loop[i+1:]:
                    if var1 != loop_var and var2 != loop_var:
                        # Check if they might have a sum relationship
                        invariants.append(f"true")  # Placeholder for more sophisticated inference
        
        return invariants
    
    def _collect_variables_in_loop(self, body: List) -> Set[str]:
        """Collect all variable names used in a loop body."""
        variables = set()
        
        for stmt in body:
            if isinstance(stmt, dict):
                if stmt.get("type") == "assign":
                    variables.add(stmt.get("var", ""))
                    # Also collect RHS variables
                    expr = str(stmt.get("expr", ""))
                    for var in self._extract_variables(expr):
                        variables.add(var)
                elif stmt.get("type") == "if":
                    # Check both branches
                    variables.update(self._collect_variables_in_loop(stmt.get("then", [])))
                    variables.update(self._collect_variables_in_loop(stmt.get("else", [])))
        
        return variables
    
    def _extract_variables(self, expr: str) -> List[str]:
        """Extract variable names from an expression string."""
        import re
        # Simple regex to find Python identifiers
        return re.findall(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b', expr)
    
    def infer_arithmetic_lemmas(self, expr: str) -> List[str]:
        """
        Generate arithmetic lemmas for common patterns.
        
        Examples:
        - x + y == y + x (commutativity)
        - (x + y) + z == x + (y + z) (associativity)
        - x * 0 == 0 (multiplication by zero)
        - x * 1 == x (multiplication by one)
        """
        lemmas = []
        
        # Commutativity of addition
        if '+' in expr:
            lemmas.append("forall(x: int, y: int :: x + y == y + x)")
        
        # Associativity of addition
        if '+' in expr:
            lemmas.append("forall(x: int, y: int, z: int :: (x + y) + z == x + (y + z))")
        
        # Multiplication properties
        if '*' in expr:
            lemmas.append("forall(x: int :: x * 0 == 0)")
            lemmas.append("forall(x: int :: x * 1 == x)")
            lemmas.append("forall(x: int, y: int :: x * y == y * x)")
        
        # Division properties
        if '/' in expr or '//' in expr:
            lemmas.append("forall(x: int, y: int :: y != 0 ==> x == (x / y) * y + (x % y))")
        
        # Modulo properties
        if '%' in expr:
            lemmas.append("forall(x: int, y: int :: y != 0 ==> 0 <= (x % y) && (x % y) < y)")
        
        self.statistics["lemmas_generated"] += len(lemmas)
        self.generated_lemmas.extend([
            {"expression": lemma, "type": "arithmetic"} for lemma in lemmas
        ])
        
        return lemmas
    
    def infer_type_constraints(self, var_name: str, var_type: Any) -> List[str]:
        """
        Generate type-based constraints for a variable.
        
        For refinement types, generates the appropriate predicates.
        """
        constraints = []
        
        if var_type == tc_types.TINT:
            constraints.append(f"{var_name} == {var_name}")  # Identity constraint
        
        elif var_type == tc_types.TBOOL:
            constraints.append(f"{var_name} == true || {var_name} == false")
        
        elif isinstance(var_type, tc_types.TARR):
            # Array type constraints
            constraints.append(f"len({var_name}) >= 0")
        
        elif isinstance(var_type, tc_types.TREFINED):
            # Refinement type - use the predicate directly
            # The predicate is already in our expression format
            pass  # Already handled by the refinement type itself
        
        return constraints
    
    def verify_with_auto_invariants(self, func, requires: List[str], ensures: List[str],
                                    loop_info: List[Dict] = None) -> Tuple[bool, str, Dict]:
        """
        Verify a function using automatically inferred invariants.
        
        Returns:
            Tuple of (success, message, statistics)
        """
        self.statistics["solver_calls"] += 1
        
        # Parse function and generate verification conditions (experimental).
        try:
            code = inspect.getsource(func)
            import textwrap
            code = textwrap.dedent(code)
            func_ast = ast.parse(code)
            target_language_ast = StmtTranslator().visit(func_ast)
            
            # Get function attributes
            scope = STORE.current_scope()
            func_attrs = STORE.get_func_attrs(scope, func.__name__)
            scope_funcs = STORE.store[scope]['func_attrs']
            sigma = tc.type_check_stmt(func_attrs['inputs'], scope_funcs, target_language_ast)
            
            # Generate verification condition using weakest precondition
            user_precond = fold_constraints(requires)
            user_postcond = fold_constraints(ensures)
            (P, C) = wp(sigma, target_language_ast, user_postcond)
            
            # Do not assume auto-generated lemmas here: they are not proven.
            # Soundness requires that only verified lemmas are added as axioms.
            # Background arithmetic facts are already available in Z3.

            # Create a fresh solver for this run.
            solver = z3.Solver()
            current_consts = declare_consts(sigma)
            fn_ret_types = { n: a['returns'] for n, a in scope_funcs.items() }
            translator = Expr2Z3(current_consts, {}, fn_ret_types)

            # Check validity: (requires => WP) and side conditions.
            check_P = BinOp(user_precond, BoolOps.Implies, P)
            emit_smt(translator, solver, check_P, "Precondition does not imply wp")
            for c in C:
                emit_smt(translator, solver, BinOp(user_precond, BoolOps.Implies, c), "Side condition violated")

            return True, "Verification succeeded", self.statistics
        
        except Exception as e:
            return False, f"Verification error: {str(e)}", self.statistics
    
    def get_inferred_invariants(self) -> Dict[str, List[InvariantCandidate]]:
        """Get all inferred invariants organized by context."""
        return self.inferred_invariants
    
    def clear_cache(self):
        """Clear the verification cache."""
        self.cache.clear()
        self.statistics["cache_hits"] = 0
    
    def get_statistics(self) -> Dict[str, int]:
        """Get verification statistics."""
        return self.statistics.copy()


class LemmaEngine:
    """
    Engine for managing and applying verification lemmas.
    
    Lemmas are verified facts that can be used in subsequent
    verification conditions without re-proof.
    """
    
    def __init__(self):
        self.lemmas: Dict[str, Dict] = {}
        self.verified_lemmas: Set[str] = set()
    
    def add_lemma(self, name: str, premises: List[str], conclusion: str,
                  source: str = "user") -> bool:
        """
        Add a lemma for verification.
        
        Args:
            name: Unique identifier for the lemma
            premises: List of premise expressions
            conclusion: Conclusion expression
            source: Source of the lemma ("user", "auto", "library")
        
        Returns:
            True if lemma was added successfully
        """
        self.lemmas[name] = {
            "premises": premises,
            "conclusion": conclusion,
            "source": source,
            "verified": False
        }
        return True
    
    def verify_lemma(self, name: str, solver: z3.Solver = None) -> bool:
        """
        Verify a lemma using the SMT solver.
        
        Args:
            name: Name of the lemma to verify
            solver: Optional solver instance
        
        Returns:
            True if lemma is verified, False otherwise
        """
        if name not in self.lemmas:
            return False
        
        lemma = self.lemmas[name]
        if lemma["verified"]:
            return True
        
        solver = solver or z3.Solver()
        
        try:
            # Parse premises and conclusion
            premises_exprs = [parse_assertion(p) for p in lemma["premises"]]
            conclusion_expr = parse_assertion(lemma["conclusion"])

            # Check that premises AND NOT conclusion is unsatisfiable
            # Essentially: premises ==> conclusion
            if premises_exprs:
                premises_conj = fold_constraints(premises_exprs)
                # Check: not (premises => conclusion)
                # <=> not (not premises or conclusion)
                # <=> premises and not conclusion
                check_expr = BinOp(premises_conj, BoolOps.And, UnOp(BoolOps.Not, conclusion_expr))
            else:
                check_expr = UnOp(BoolOps.Not, conclusion_expr)

            translator = Expr2Z3({})
            z3_expr = translator.visit(check_expr)

            solver.push()
            solver.add(z3_expr)
            result = solver.check()
            solver.pop()

            if result == z3.unsat:
                lemma["verified"] = True
                self.verified_lemmas.add(name)
                return True
            else:
                lemma["verified"] = False
                # Optionally log counterexample
                return False

        except Exception:
            lemma["verified"] = False
            return False
    
    def can_use_lemma(self, name: str) -> bool:
        """Check if a lemma can be used (is verified)."""
        return name in self.verified_lemmas
    
    def get_lemma(self, name: str) -> Optional[Dict]:
        """Get a lemma by name."""
        return self.lemmas.get(name)
    
    def get_all_lemmas(self) -> Dict[str, Dict]:
        """Get all registered lemmas."""
        return self.lemmas.copy()
    
    def get_verified_lemmas(self) -> Dict[str, Dict]:
        """Get only verified lemmas."""
        return {name: lemma for name, lemma in self.lemmas.items() 
                if lemma["verified"]}


def assert_by(lemma_name: str, **kwargs):
    """
    Decorator for lemmas that can be used in assert statements.
    
    Usage:
        @lemma
        @assert_by("commutativity", x=1, y=2)
        def commutativity(x, y):
            return x + y == y + x
    
    Or in an assert statement:
        assert_by("commutativity", x=n, y=m)
        assert x + m == m + n
    """
    def decorator(func):
        # Register the lemma
        lemma_engine = LemmaEngine()
        
        # Extract preconditions and postconditions from function docstring
        premises = []
        conclusion = ""
        
        # For now, assume the lemma is the function itself
        # In a full implementation, we'd parse the docstring
        
        lemma_engine.add_lemma(
            name=lemma_name,
            premises=premises,
            conclusion=func.__code__.co_name,
            source="user"
        )
        
        def wrapper(*args, **kw_args):
            return func(*args, **kw_args)
        
        return wrapper
    return decorator


class TerminationChecker:
    """
    Checker for recursive function termination.
    
    Verifies that recursive functions have a valid decreases clause
    and that the recursion will eventually terminate.
    """
    
    def __init__(self):
        self.recursion_depths: Dict[str, int] = {}
        self.decreases_info: Dict[str, Dict] = {}
    
    def check_termination(self, func_name: str, decreases: str, 
                         args: List[Any]) -> Tuple[bool, str]:
        """
        Check if a recursive function call respects termination.
        
        Args:
            func_name: Name of the function
            decreases: Decreases expression
            args: Function arguments
        
        Returns:
            Tuple of (is_valid, message)
        """
        # Check if we have a decreases clause
        if not decreases:
            return False, f"Recursive function '{func_name}' requires a decreases clause"
        
        # Evaluate the decreases measure best-effort.
        def _eval_measure(expr: str, call_args: List[Any]):
            # Numeric literal
            try:
                return int(expr)
            except Exception:
                pass
            # Single-argument heuristic: treat decreases as the first arg
            if call_args:
                first = call_args[0]
                if isinstance(first, (int, float)):
                    return first
            return None
        
        measure = _eval_measure(decreases, args)
        if measure is None:
            return False, f"Unable to evaluate decreases expression '{decreases}' for termination check"
        
        # Check if this is the first call
        if func_name not in self.decreases_info:
            self.decreases_info[func_name] = {
                "first_call": False,
                "decreases_var": decreases,
                "previous_values": {"last": measure}
            }
            return True, "First call - recorded decreases measure"
        
        info = self.decreases_info[func_name]
        prev = info.get("previous_values", {}).get("last", None)
        if prev is None:
            info.setdefault("previous_values", {})["last"] = measure
            return True, "Recorded initial decreases measure"
        
        if measure < prev:
            info["previous_values"]["last"] = measure
            return True, "Termination check passed (measure decreased)"
        
        return False, f"Termination check failed: measure {measure} does not decrease from {prev}"


# Singleton instances
auto_active_engine = AutoActiveEngine()
lemma_engine = LemmaEngine()
termination_checker = TerminationChecker()


def auto_infer_invariants(loop_info: Dict[str, Any]) -> List[str]:
    """
    Convenience function for inferring loop invariants.
    
    Args:
        loop_info: Dictionary containing loop information
    
    Returns:
        List of inferred invariant expressions
    """
    return auto_active_engine.infer_loop_invariants(loop_info)


def generate_arithmetic_lemmas(expr: str) -> List[str]:
    """
    Convenience function for generating arithmetic lemmas.
    
    Args:
        expr: Expression to analyze
    
    Returns:
        List of generated lemma expressions
    """
    return auto_active_engine.infer_arithmetic_lemmas(expr)


def register_lemma(name: str, premises: List[str], conclusion: str) -> bool:
    """
    Convenience function for registering a lemma.
    
    Args:
        name: Lemma name
        premises: List of premise expressions
        conclusion: Conclusion expression
    
    Returns:
        True if lemma was registered successfully
    """
    return lemma_engine.add_lemma(name, premises, conclusion)


def verify_lemma(name: str) -> bool:
    """
    Convenience function for verifying a lemma.
    
    Args:
        name: Lemma name
    
    Returns:
        True if lemma is verified
    """
    return lemma_engine.verify_lemma(name)


def check_termination(func_name: str, decreases: str, args: List[Any]) -> Tuple[bool, str]:
    """
    Convenience function for checking termination.
    
    Args:
        func_name: Function name
        decreases: Decreases expression
        args: Function arguments
    
    Returns:
        Tuple of (is_valid, message)
    """
    return termination_checker.check_termination(func_name, decreases, args)
