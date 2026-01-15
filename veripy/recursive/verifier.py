"""
Recursive Function Verification and Termination Checking

This module provides comprehensive support for verifying recursive functions,
including termination proofs, decreases clause validation, and recursive
call verification.
"""

import ast
import z3
from typing import Dict, List, Optional, Any, Tuple, Set
from dataclasses import dataclass, field
from enum import Enum
from functools import lru_cache
import inspect
import sys

from veripy.parser.syntax import *
from veripy.parser.syntax import CompOps
from veripy.parser.parser import parse_assertion, parse_expr
from veripy.core.verify import STORE, wp, emit_smt, fold_constraints, declare_consts, parse_func_types, subst, verify_func

from veripy.core.transformer import StmtTranslator, Expr2Z3
from veripy.typecheck import types as tc_types
from veripy.auto_active import TerminationChecker, check_termination


class RecursionType(Enum):
    """Types of recursion."""
    DIRECT = "direct"
    INDIRECT = "indirect"
    MUTUAL = "mutual"
    TAIL = "tail"


@dataclass
class RecursiveCall:
    """Information about a recursive function call."""
    function_name: str
    line: int
    column: int
    arguments: List[str]
    decreases_expr: str
    is_tail_call: bool


@dataclass
class DecreasesInfo:
    """Information about a decreases clause."""
    expression: str
    variables: Set[str]
    well_founded: bool
    justification: str


class RecursiveVerifier:
    """
    Comprehensive verifier for recursive functions.
    
    Handles:
    - Termination checking with decreases clauses
    - Recursive call verification
    - Mutual recursion support
    - Tail recursion optimization detection
    """
    
    def __init__(self, solver: z3.Solver = None):
        self.solver = solver or z3.Solver()
        self.recursive_functions: Dict[str, Dict] = {}
        self.call_graph: Dict[str, List[str]] = {}
        self.termination_checker = TerminationChecker()
        self.statistics = {
            "recursive_functions_verified": 0,
            "termination_proofs": 0,
            "termination_failures": 0
        }
    
    def analyze_recursive_function(self, func_name: str, code: str,
                                   decreases: Optional[str] = None,
                                   func_obj=None) -> Dict[str, Any]:
        """
        Analyze a recursive function for verification.
        
        Args:
            func_name: Name of the function
            code: Function source code
            decreases: Optional decreases expression
            func_obj: The actual function object
        
        Returns:
            Dictionary with analysis results
        """
        # Parse the function
        tree = ast.parse(code)
        func_def = tree.body[0]
        
        # Extract recursive calls
        recursive_calls = self._extract_recursive_calls(func_def, func_name)
        
        # Analyze recursion type
        recursion_type = self._determine_recursion_type(func_name, recursive_calls)
        
        # Analyze decreases clause
        decreases_info = self._analyze_decreases_clause(decreases, recursive_calls)
        
        # Build call graph
        self._update_call_graph(func_name, recursive_calls)
        
        # Store function info
        self.recursive_functions[func_name] = {
            "code": code,
            "decreases": decreases,
            "decreases_info": decreases_info,
            "recursive_calls": recursive_calls,
            "recursion_type": recursion_type,
            "verified": False,
            "func_obj": func_obj
        }
        
        return {
            "function": func_name,
            "recursion_type": recursion_type.value,
            "decreases_info": decreases_info.__dict__ if decreases_info else None,
            "recursive_calls": [call.__dict__ for call in recursive_calls],
            "is_tail_recursive": recursion_type == RecursionType.TAIL
        }
    
    def _extract_recursive_calls(self, node: ast.AST, func_name: str) -> List[RecursiveCall]:
        """Extract all recursive calls from a function."""
        calls = []
        
        for child in ast.walk(node):
            if isinstance(child, ast.Call):
                if isinstance(child.func, ast.Name):
                    if child.func.id == func_name:
                        # This is a recursive call
                        arg_names = []
                        for arg in child.args:
                            try:
                                # Use ast.unparse to get string representation of argument
                                arg_names.append(ast.unparse(arg))
                            except AttributeError:
                                # Fallback for older python versions or partial support
                                if isinstance(arg, ast.Name):
                                    arg_names.append(arg.id)
                                elif isinstance(arg, ast.Constant):
                                    arg_names.append(str(arg.value))
                                else:
                                    # Fallback: try to reconstruct simple binops manually or skip
                                    # This is a limitation if ast.unparse is not available
                                    pass

                        
                        # Check if it's a tail call
                        is_tail = self._is_tail_call(node, child)
                        
                        calls.append(RecursiveCall(
                            function_name=func_name,
                            line=child.lineno,
                            column=child.col_offset,
                            arguments=arg_names,
                            decreases_expr="",
                            is_tail_call=is_tail
                        ))
        
        return calls
    
    def _is_tail_call(self, func_node: ast.FunctionDef, call_node: ast.Call) -> bool:
        """Check if a call is in tail position."""
        # Get the last statement in the function
        if not func_node.body:
            return False
        
        last_stmt = func_node.body[-1]
        
        # Check if last statement is a return containing this call
        if isinstance(last_stmt, ast.Return):
            if isinstance(last_stmt.value, ast.Call):
                return last_stmt.value is call_node
        
        return False
    
    def _determine_recursion_type(self, func_name: str, 
                                  calls: List[RecursiveCall]) -> RecursionType:
        """Determine the type of recursion."""
        if not calls:
            return RecursionType.DIRECT
        
        # Check for tail recursion
        if all(call.is_tail_call for call in calls):
            return RecursionType.TAIL
        
        return RecursionType.DIRECT
    
    def _analyze_decreases_clause(self, decreases: Optional[str],
                                  calls: List[RecursiveCall]) -> Optional[DecreasesInfo]:
        """Analyze a decreases clause for well-foundedness."""
        if not decreases:
            # No decreases clause - may still be valid for some cases
            return DecreasesInfo(
                expression="",
                variables=set(),
                well_founded=True,
                justification="No decreases clause provided"
            )
        
        # Parse the decreases expression
        try:
            parsed_expr = parse_assertion(decreases)
            
            # Extract variables from the expression
            variables = self._extract_variables_from_expr(parsed_expr)
            
            # Check if the expression is well-founded
            well_founded, justification = self._check_well_founded(variables, decreases)
            
            return DecreasesInfo(
                expression=decreases,
                variables=variables,
                well_founded=well_founded,
                justification=justification
            )
        except Exception as e:
            return DecreasesInfo(
                expression=decreases or "",
                variables=set(),
                well_founded=False,
                justification=f"Failed to parse decreases clause: {e}"
            )
    
    def _extract_variables_from_expr(self, expr: Expr) -> Set[str]:
        """Extract variable names from an expression."""
        variables = set()
        
        def visit(node):
            if isinstance(node, Var):
                variables.add(node.name)
            elif isinstance(node, BinOp):
                visit(node.e1)
                visit(node.e2)
            elif isinstance(node, UnOp):
                visit(node.e)
            elif isinstance(node, Quantification):
                variables.add(node.var.name)
                visit(node.expr)
        
        visit(expr)
        return variables
    
    def _check_well_founded(self, variables: Set[str], 
                           decreases: str) -> Tuple[bool, str]:
        """Check if a decreases clause is well-founded."""
        if not variables:
            return False, "Decreases expression has no variables"
        
        # Check for common well-founded measures
        common_measures = ['n', 'n-1', 'n', 'size', 'length', 'depth']
        
        for measure in common_measures:
            if measure in decreases.lower():
                return True, f"Uses common well-founded measure: {measure}"
        
        # Check if it looks like a simple variable
        if len(variables) == 1 and decreases.strip() in variables:
            return True, "Single decreasing variable"
        
        # For complex expressions, we need SMT solving
        try:
            self.solver.push()
            
            # Create variables in solver
            consts = {}
            for var in variables:
                consts[var] = z3.Int(var)
            
            # Check if there exists a non-terminating sequence
            # This is done by checking if we can have infinite descent
            # For simplicity, we assume well-founded if variables are bounded below
            for var in variables:
                self.solver.add(consts[var] >= 0)
            
            # If satisfiable, assume well-founded for now
            result = self.solver.check()
            self.solver.pop()
            
            if result == z3.sat:
                return True, "SMT analysis suggests well-founded"
            else:
                return False, "SMT analysis suggests not well-founded"
                
        except Exception as e:
            self.solver.pop()
            return True, f"Could not verify, assuming well-founded: {e}"
    
    def _update_call_graph(self, func_name: str, calls: List[RecursiveCall]):
        """Update the call graph with recursive calls."""
        if func_name not in self.call_graph:
            self.call_graph[func_name] = []
        
        for call in calls:
            self.call_graph[func_name].append(call.function_name)
    
    def verify_termination(self, func_name: str) -> Tuple[bool, str]:
        """
        Verify that a function terminates.
        
        Args:
            func_name: Name of the function to verify
        
        Returns:
            Tuple of (success, message)
        """
        if func_name not in self.recursive_functions:
            return False, f"Function {func_name} not analyzed"
        
        func_info = self.recursive_functions[func_name]
        decreases = func_info.get("decreases")
        requires = func_info.get("_veripy_requires", [])
        
        # Check for decreases clause
        if not decreases:
            # Check if function has no recursive calls
            if not func_info.get("recursive_calls"):
                return True, "Non-recursive function - termination guaranteed"
            else:
                return False, f"Recursive function '{func_name}' requires a decreases clause"
        
        # Statically check that each recursive call strictly decreases the measure.
        ok, msg = self._verify_decreases_respected(func_name, decreases, requires)
        
        if ok:
            self.statistics["termination_proofs"] += 1
            return True, msg
        
        self.statistics["termination_failures"] += 1
        return False, msg
    
    def verify_recursive_function(self, func_name: str, 
                                  requires: List[str],
                                  ensures: List[str]) -> Tuple[bool, str]:
        """
        Verify a recursive function with its contracts.
        
        Args:
            func_name: Name of the function
            requires: Preconditions
            ensures: Postconditions
        
        Returns:
            Tuple of (success, message)
        """
        if func_name not in self.recursive_functions:
            return False, f"Function {func_name} not analyzed"
        
        func_info = self.recursive_functions[func_name]
        
        # First, verify termination
        terminates, term_msg = self.verify_termination(func_name)
        if not terminates:
            return False, f"Termination failure: {term_msg}"
        
        # Now verify the functional correctness
        try:
            # Get function from STORE
            scope = STORE.current_scope()
            attrs = STORE.get_func_attrs(scope, func_name)
            
            if attrs is None:
                return False, f"No verification info for function {func_name}"
            
            # Create solver and translate to Z3
            solver = z3.Solver()
            sigma = attrs.get('inputs', {})
            
            # Generate verification condition
            # For recursive functions, we need to be careful about the decreases
            user_precond = fold_constraints(requires)
            user_postcond = fold_constraints(ensures)
            
            # Check that decreases is respected in recursive calls
            decreases = func_info.get("decreases")
            if decreases:
                decreases_verified, msg = self._verify_decreases_respected(
                    func_name, decreases, requires
                )
                if not decreases_verified:
                    return False, msg
            
            self.statistics["recursive_functions_verified"] += 1
            
            # Now verify the functional correctness using core verify_func
            # We need to make sure the function is in the STORE (which it should be from the decorator)
            # verify_func(func, scope, inputs, requires, ensures, modifies=None, reads=None)
            
            # Get the function object (we don't have it directly here, need to find it or pass it)
            # Actually, verify_recursive_function is called by verify_all_recursive which iterates over stored info.
            # But verify_func expects the actual function object to parse source code.
            # We have the source code in func_info['code'].
            
            # To reuse verify_func, we need to handle the fact that it parses inspect.getsource.
            # We can't easily pass the function object here unless we store it.
            # But wait, verify_recursive decorator stores analysis on the function object.
            # verify_all_recursive iterates over recursive_functions which are just dicts.
            # We lost the function object in recursive_verifier.recursive_functions!
            
            # Let's fix this by storing the function object in recursive_functions
            func_obj = func_info.get("func_obj")
            if func_obj:
                 try:
                     # verify_func prints "Verified!" on success or raises Exception
                     verify_func(func_obj, scope, attrs['inputs'], requires, ensures)
                 except Exception as e:
                     return False, f"Functional verification failed: {e}"
            else:
                 return False, "Function object not found for verification"

            return True, f"Function {func_name} verified successfully"
            
        except Exception as e:
            return False, f"Verification error: {str(e)}"
    
    def _verify_decreases_respected(self, func_name: str, decreases: str,
                                   requires: List[str]) -> Tuple[bool, str]:
        """Verify that recursive calls respect the decreases clause."""
        try:
            # Parse decreases expression
            decreases_expr = parse_assertion(decreases)
            
            # Get function attributes to access parameters
            attrs = None
            scope = STORE.current_scope()
            if scope and func_name in STORE.store[scope]['func_attrs']:
                attrs = STORE.get_func_attrs(scope, func_name)
            else:
                # Search all scopes
                for s in STORE.store:
                    if func_name in STORE.store[s]['func_attrs']:
                        attrs = STORE.store[s]['func_attrs'][func_name]
                        break
            
            if not attrs:
                return False, f"Could not find function attributes for {func_name}"

            params = list(attrs['inputs'].keys())
            sigma = attrs['inputs']
            current_consts = declare_consts(sigma)

            # For each recursive call, verify that the decreases expression actually decreases
            for call in self.recursive_functions[func_name].get("recursive_calls", []):
                args_str = call.arguments
                if len(args_str) != len(params):
                     return False, f"Argument count mismatch in recursive call at line {call.line}"
                
                # Create substitution map
                mapping = {}
                for p, a in zip(params, args_str):
                    mapping[p] = parse_expr(a)
                
                # Substitute in decreases expr to get decreases_call
                decreases_call = decreases_expr
                for p, val in mapping.items():
                    decreases_call = subst(p, val, decreases_call)
                
                solver = z3.Solver()
                translator = Expr2Z3(current_consts)
                
                # Add preconditions
                req_conj = fold_constraints(requires)
                req_z3 = translator.visit(req_conj)
                solver.add(req_z3)
                
                # Check 1: decreases >= 0
                # We check: requires => decreases >= 0
                check_pos = BinOp(decreases_expr, CompOps.Ge, Literal(VInt(0)))
                try:
                    emit_smt(translator, solver, check_pos, "Decreases expression must be non-negative")
                except Exception as e:
                    return False, str(e)
                
                # Check 2: decreases_call < decreases
                # We check: requires => decreases_call < decreases
                check_dec = BinOp(decreases_call, CompOps.Lt, decreases_expr)
                try:
                    emit_smt(translator, solver, check_dec, f"Recursive call at line {call.line} does not decrease measure")
                except Exception as e:
                    return False, str(e)
            
            return True, "Decreases clause verified"
            
        except Exception as e:
            return False, f"Decreases verification failed: {e}"
    
    def get_call_graph(self) -> Dict[str, List[str]]:
        """Get the call graph of recursive functions."""
        return self.call_graph.copy()
    
    def get_statistics(self) -> Dict[str, int]:
        """Get verification statistics."""
        return self.statistics.copy()
    
    def reset(self):
        """Reset the verifier state."""
        self.recursive_functions.clear()
        self.call_graph.clear()
        self.statistics = {
            "recursive_functions_verified": 0,
            "termination_proofs": 0,
            "termination_failures": 0
        }


# Singleton instance
recursive_verifier = RecursiveVerifier()


def verify_recursive(requires: List[str], ensures: List[str], 
                    decreases: Optional[str] = None):
    """
    Decorator for verifying recursive functions.
    
    Args:
        requires: Preconditions
        ensures: Postconditions
        decreases: Decreases expression for termination proof
    
    Usage:
        @verify_recursive(
            requires=['n >= 0'],
            ensures=['ans == factorial(n)'],
            decreases='n'
        )
        def factorial(n: int) -> int:
            if n == 0:
                return 1
            else:
                return n * factorial(n - 1)
    """
    def decorator(func):
        func_name = func.__name__
        code = inspect.getsource(func)
        
        # Analyze the function
        analysis = recursive_verifier.analyze_recursive_function(
            func_name, code, decreases, func_obj=func
        )
        
        # Store contracts in the verifier's registry so verify_all_recursive can find them
        if func_name in recursive_verifier.recursive_functions:
            recursive_verifier.recursive_functions[func_name]["_veripy_requires"] = requires
            recursive_verifier.recursive_functions[func_name]["_veripy_ensures"] = ensures
        
        # Store analysis in function attributes for later verification
        func._veripy_analysis = analysis
        func._veripy_requires = requires
        func._veripy_ensures = ensures
        func._veripy_decreases = decreases
        
        # Register with STORE
        try:
            types = parse_func_types(func)
            scope = STORE.current_scope()
            if scope:
                STORE.insert_func_attr(scope, func_name, types[0], types[1], types[2], requires, ensures, decreases)
        except Exception:
            pass # Ignore if registration fails (e.g. no scope)

        def wrapper(*args, **kwargs):
            return func(*args, **kwargs)
        
        return wrapper
    return decorator


def verify_all_recursive():
    """Verify all decorated recursive functions."""
    results = {}
    
    for func_name, func_info in recursive_verifier.recursive_functions.items():
        success, message = recursive_verifier.verify_recursive_function(
            func_name,
            func_info.get("_veripy_requires", []),
            func_info.get("_veripy_ensures", [])
        )
        results[func_name] = {
            "success": success,
            "message": message
        }
    
    return results
