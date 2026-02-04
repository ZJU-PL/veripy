"""
Extended syntax definitions for veripy.

This module adds support for:
- Classes/OOP (class definitions, methods, fields)
- Sets (union, intersection, membership, cardinality)
- Dictionaries (maps with get, set, keys)
- Strings (concat, length, substring, index)
- List comprehensions (transformed to loops)
"""

# Import all from submodules to maintain backward compatibility
from .operations import *
from .values import *
from .expressions import *
from .oop import *
from .collections import *
from .strings import *
from .statements import *
from .extended_statements import *
from .patterns import *
from .async_features import *
from .types import *
from .iterators import *

# Re-export everything for backward compatibility
__all__ = [
    # Operations
    'Op', 'ArithOps', 'CompOps', 'BoolOps', 'SetOps', 'DictOps',
    # Values
    'Value', 'VInt', 'VBool', 'VString', 'VSet', 'VDict', 'VList',
    # Core Expressions
    'Expr', 'Var', 'Literal', 'BinOp', 'UnOp', 'Quantification',
    'Subscript', 'Slice', 'Store', 'FunctionCall', 'Old', 'RecordField',
    # OOP
    'FieldAccess', 'FieldAssign', 'ClassInvariant', 'MethodCall',
    'ClassDef', 'MethodDef',
    # Collections
    'SetLiteral', 'SetOp', 'SetCardinality', 'SetComprehension',
    'DictLiteral', 'DictComprehension', 'DictGet', 'DictSet', 'DictKeys', 'DictValues', 'DictContains',
    'ListComprehension',
    # Strings
    'StringLiteral', 'StringConcat', 'StringLength', 'StringIndex',
    'StringSubstring', 'StringContains',
    # Core Statements
    'Stmt', 'Skip', 'Assign', 'FieldAssignStmt', 'If', 'Seq', 'Assume',
    'Assert', 'While', 'Havoc', 'SubscriptAssignStmt',
    # Extended Statements
    'Try', 'ExceptHandler', 'With', 'ForLoop', 'AugAssign', 'Break',
    'Continue', 'Raise', 'Global', 'Nonlocal', 'ImportStmt', 'ImportFrom',
    # Patterns
    'Match', 'MatchCase', 'Pattern', 'PatternConstant', 'PatternCapture',
    'PatternSequence', 'PatternMapping', 'PatternClass', 'PatternLiteral',
    'PatternAs', 'PatternOr',
    # Async
    'AsyncFunctionDef', 'AsyncFor', 'AsyncWith', 'Await',
    # Types
    'Property', 'StaticMethod', 'ClassMethod', 'VarArgs', 'KwArgs',
    'FString', 'Decorator', 'DecoratorChain', 'DataClass', 'TypeAlias',
    'Protocol', 'MethodSignature', 'TypeVar', 'UnionType', 'OptionalType',
    'LiteralType', 'Final', 'TypeGuard',
    # Iterators
    'Iterator', 'Range', 'Enumerate', 'Zip', 'Map', 'Filter', 'Reduce',
    'Comprehension', 'Generator', 'Lambda', 'Yield', 'YieldFrom', 'Walrus',
]
