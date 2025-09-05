"""
Refinement types for veripy

This module provides convenient syntax for defining refinement types.
"""

from typing import TypeVar, Type
from veripy.typecheck.types import TREFINED, TINT, TBOOL, TARR

# Type variables for refinement types
T = TypeVar('T')

class Refined:
    """
    Helper class for creating refinement types with convenient syntax.
    
    Usage:
        Refined[int, "x > 0"]  # Positive integers
        Refined[int, "x >= 0 and x < 100"]  # Integers in range [0, 100)
        Refined[List[int], "len(x) > 0"]  # Non-empty integer lists
    """
    
    def __class_getitem__(cls, params):
        if isinstance(params, tuple) and len(params) == 2:
            base_type, predicate = params
            return TREFINED(base_type, predicate)
        else:
            raise TypeError("Refined[T, predicate] expects exactly two arguments")

# Convenience functions for common refinement types
def PositiveInt():
    """Returns refinement type for positive integers: {x: int | x > 0}"""
    from veripy.parser.parser import parse_assertion
    return TREFINED(TINT, parse_assertion("x > 0"), "x")

def NonNegativeInt():
    """Returns refinement type for non-negative integers: {x: int | x >= 0}"""
    from veripy.parser.parser import parse_assertion
    return TREFINED(TINT, parse_assertion("x >= 0"), "x")

def EvenInt():
    """Returns refinement type for even integers: {x: int | x % 2 == 0}"""
    from veripy.parser.parser import parse_assertion
    return TREFINED(TINT, parse_assertion("x % 2 == 0"), "x")

def OddInt():
    """Returns refinement type for odd integers: {x: int | x % 2 == 1}"""
    from veripy.parser.parser import parse_assertion
    return TREFINED(TINT, parse_assertion("x % 2 == 1"), "x")

def RangeInt(min_val: int, max_val: int):
    """Returns refinement type for integers in range [min_val, max_val)"""
    from veripy.parser.parser import parse_assertion
    predicate = f"x >= {min_val} and x < {max_val}"
    return TREFINED(TINT, parse_assertion(predicate), "x")

def NonEmptyList(element_type):
    """Returns refinement type for non-empty lists: {x: List[T] | len(x) > 0}"""
    from veripy.parser.parser import parse_assertion
    return TREFINED(TARR(element_type), parse_assertion("len(x) > 0"), "x")

def ListWithLength(element_type, length: int):
    """Returns refinement type for lists with specific length: {x: List[T] | len(x) == length}"""
    from veripy.parser.parser import parse_assertion
    predicate = f"len(x) == {length}"
    return TREFINED(TARR(element_type), parse_assertion(predicate), "x")
