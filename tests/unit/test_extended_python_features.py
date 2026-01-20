"""
Comprehensive tests for extended Python features in veripy.

This test suite covers:
- Classes/OOP (field access, method calls, class definitions)
- For loops (complete implementation)
- With statements (context management)
- Lambda expressions
- Generators (yield, yield from)
- Import statements
- Augmented assignments (+=, -=, etc.)
- Break/continue statements
- Exception handling (try/except/finally)
- Raise statements
- Global/nonlocal declarations
- Async/await support
- Match statements (Python 3.10+)
- Walrus operator (Python 3.8+)
"""

import unittest
import ast
from veripy.parser.syntax import (
    # Core expressions
    Var, Literal, BinOp, UnOp, Quantification, FunctionCall,
    # Extended expressions
    StringLiteral, StringConcat, StringLength, StringIndex,
    StringSubstring, StringContains,
    SetLiteral, SetOp, SetCardinality, SetComprehension,
    DictLiteral, DictGet, DictSet, DictKeys, DictValues, DictContains,
    FieldAccess, MethodCall, FieldAssignStmt,
    ListComprehension, SetOps, DictOps,
    VInt, VBool, VString,
    # Extended statements
    Try, ExceptHandler, With, ForLoop, AugAssign,
    Break, Continue, Raise, Global, Nonlocal,
    ImportStmt, ImportFrom, Lambda, Yield, YieldFrom,
    Await, AsyncFunctionDef, AsyncFor, AsyncWith,
    Match, MatchCase, Pattern, PatternConstant, PatternCapture,
    PatternSequence, PatternMapping, PatternClass, PatternAs,
    PatternOr, PatternLiteral, Walrus,
    # Statements
    Assign, If, While, Assume, Assert, Skip, Seq, ClassDef, MethodDef,
    # Operations
    ArithOps, CompOps, BoolOps
)
from veripy.core.transformer import ExprTranslator, StmtTranslator


class TestAugmentedAssignment(unittest.TestCase):
    """Test augmented assignment support (+=, -=, etc.)."""
    
    def test_aug_assign_add(self):
        """Test += operation."""
        translator = StmtTranslator()
        code = "x += 1"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, AugAssign)
        self.assertEqual(result.var.name, 'x')
        self.assertEqual(result.op, ArithOps.Add)
    
    def test_aug_assign_sub(self):
        """Test -= operation."""
        translator = StmtTranslator()
        code = "x -= 5"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, AugAssign)
        self.assertEqual(result.op, ArithOps.Minus)
    
    def test_aug_assign_mult(self):
        """Test *= operation."""
        translator = StmtTranslator()
        code = "x *= 2"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, AugAssign)
        self.assertEqual(result.op, ArithOps.Mult)


class TestExceptionHandling(unittest.TestCase):
    """Test exception handling (try/except/finally/else)."""
    
    def test_try_except(self):
        """Test simple try/except."""
        translator = StmtTranslator()
        code = """
try:
    x = 1
except ValueError:
    x = 2
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Try)
        self.assertEqual(len(result.handlers), 1)
        self.assertEqual(result.handlers[0].exc_type, 'ValueError')
    
    def test_try_except_as(self):
        """Test try/except with variable binding."""
        translator = StmtTranslator()
        code = """
try:
    x = 1
except Exception as e:
    x = 2
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Try)
        self.assertEqual(result.handlers[0].exc_var, 'e')
    
    def test_try_except_else_finally(self):
        """Test try/except/else/finally."""
        translator = StmtTranslator()
        code = """
try:
    x = 1
except:
    x = 2
else:
    x = 3
finally:
    x = 4
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Try)
        self.assertIsNotNone(result.orelse)
        self.assertIsNotNone(result.finalbody)
    
    def test_multiple_handlers(self):
        """Test multiple except handlers."""
        translator = StmtTranslator()
        code = """
try:
    x = 1
except ValueError:
    x = 2
except TypeError:
    x = 3
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Try)
        self.assertEqual(len(result.handlers), 2)


class TestLoopStatements(unittest.TestCase):
    """Test loop control statements (break, continue, for loops)."""
    
    def test_break(self):
        """Test break statement."""
        translator = StmtTranslator()
        code = "break"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Break)
    
    def test_continue(self):
        """Test continue statement."""
        translator = StmtTranslator()
        code = "continue"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Continue)
    
    def test_for_loop_range(self):
        """Test for loop with range - transformed to While loop with initialization."""
        translator = StmtTranslator()
        code = "for i in range(10):\n    x = i"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        # For loops are transformed to Seq containing initialization and While loop
        # The Seq preserves the semantics: init; while cond: body
        self.assertIsInstance(result, Seq)
        # The Seq should contain a While loop
        self.assertIsInstance(result.s2, While)
        self.assertIn('i', str(result.s2.cond))


class TestWithStatement(unittest.TestCase):
    """Test with statement for context management."""
    
    def test_with_simple(self):
        """Test simple with statement."""
        translator = StmtTranslator()
        code = """
with open('file.txt') as f:
    x = 1
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, With)
        self.assertEqual(result.item_var, 'f')


class TestRaiseStatement(unittest.TestCase):
    """Test raise statement for exceptions."""
    
    def test_raise_simple(self):
        """Test simple raise."""
        translator = StmtTranslator()
        code = "raise ValueError()"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Raise)
    
    def test_raise_with_message(self):
        """Test raise with message."""
        translator = StmtTranslator()
        code = "raise ValueError('error message')"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Raise)
    
    def test_raise_from(self):
        """Test raise ... from ... statement."""
        translator = StmtTranslator()
        code = "raise ValueError() from e"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Raise)
        self.assertIsNotNone(result.cause)


class TestGlobalNonlocal(unittest.TestCase):
    """Test global and nonlocal declarations."""
    
    def test_global(self):
        """Test global declaration."""
        translator = StmtTranslator()
        code = "global x, y"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Global)
        self.assertEqual(result.names, ['x', 'y'])
    
    def test_nonlocal(self):
        """Test nonlocal declaration."""
        translator = StmtTranslator()
        code = "nonlocal x, y"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Nonlocal)
        self.assertEqual(result.names, ['x', 'y'])


class TestImportStatements(unittest.TestCase):
    """Test import statements."""
    
    def test_import_module(self):
        """Test import module."""
        translator = StmtTranslator()
        code = "import os"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, ImportStmt)
        self.assertEqual(result.module, 'os')
    
    def test_import_module_alias(self):
        """Test import module with alias."""
        translator = StmtTranslator()
        code = "import os as operating_system"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, ImportStmt)
        self.assertEqual(result.alias, 'operating_system')
    
    def test_import_from(self):
        """Test from...import statement."""
        translator = StmtTranslator()
        code = "from os import path"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, ImportFrom)
        self.assertEqual(result.module, 'os')
        self.assertEqual(result.names, ['path'])
    
    def test_import_from_multiple(self):
        """Test from...import multiple names."""
        translator = StmtTranslator()
        code = "from os import path, getcwd"
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, ImportFrom)
        self.assertEqual(len(result.names), 2)


class TestLambdaExpression(unittest.TestCase):
    """Test lambda expressions."""
    
    def test_lambda_simple(self):
        """Test simple lambda."""
        translator = ExprTranslator()
        code = "lambda x: x + 1"
        tree = ast.parse(code, mode='eval')
        result = translator.visit(tree.body)
        self.assertIsInstance(result, Lambda)
        self.assertEqual(len(result.params), 1)
    
    def test_lambda_multiple_params(self):
        """Test lambda with multiple parameters."""
        translator = ExprTranslator()
        code = "lambda x, y: x + y"
        tree = ast.parse(code, mode='eval')
        result = translator.visit(tree.body)
        self.assertIsInstance(result, Lambda)
        self.assertEqual(len(result.params), 2)


class TestGenerators(unittest.TestCase):
    """Test generator expressions (yield, yield from)."""
    
    def test_yield(self):
        """Test yield expression."""
        translator = ExprTranslator()
        code = "(yield x)"
        tree = ast.parse(code, mode='eval')
        result = translator.visit(tree.body)
        self.assertIsInstance(result, Yield)
    
    def test_yield_without_value(self):
        """Test yield without value."""
        translator = ExprTranslator()
        code = "(yield)"
        tree = ast.parse(code, mode='eval')
        result = translator.visit(tree.body)
        self.assertIsInstance(result, Yield)
        self.assertIsNone(result.value)
    
    def test_yield_from(self):
        """Test yield from expression."""
        translator = ExprTranslator()
        code = "(yield from iterable)"
        tree = ast.parse(code, mode='eval')
        result = translator.visit(tree.body)
        self.assertIsInstance(result, YieldFrom)


class TestAwaitExpression(unittest.TestCase):
    """Test await expression."""
    
    def test_await(self):
        """Test await expression."""
        translator = ExprTranslator()
        code = "(await coro)"
        tree = ast.parse(code, mode='eval')
        result = translator.visit(tree.body)
        self.assertIsInstance(result, Await)


class TestWalrusOperator(unittest.TestCase):
    """Test walrus operator (:=)."""
    
    def test_walrus(self):
        """Test named expression (walrus operator)."""
        translator = ExprTranslator()
        code = "(x := 1)"
        tree = ast.parse(code, mode='eval')
        result = translator.visit(tree.body)
        self.assertIsInstance(result, Walrus)
        self.assertEqual(result.name, 'x')


class TestMatchStatement(unittest.TestCase):
    """Test match statement (Python 3.10+)."""
    
    def test_match_simple(self):
        """Test simple match statement."""
        translator = StmtTranslator()
        code = """
match x:
    case 1:
        y = 2
    case 2:
        y = 3
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Match)
        self.assertEqual(len(result.cases), 2)
    
    def test_match_with_guard(self):
        """Test match with guard."""
        translator = StmtTranslator()
        code = """
match x:
    case n if n > 0:
        y = 1
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Match)
        self.assertIsNotNone(result.cases[0].guard)
    
    def test_match_pattern_capture(self):
        """Test match with capture pattern."""
        translator = StmtTranslator()
        code = """
match x:
    case n:
        y = n
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Match)
    
    def test_match_pattern_sequence(self):
        """Test match with sequence pattern."""
        translator = StmtTranslator()
        code = """
match x:
    case [a, b]:
        y = a + b
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, Match)


class TestClassDefinitions(unittest.TestCase):
    """Test class definition support."""
    
    def test_simple_class(self):
        """Test simple class definition."""
        translator = StmtTranslator()
        code = """
class Counter:
    def __init__(self):
        self.value = 0
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, ClassDef)
        self.assertEqual(result.name, 'Counter')
        self.assertTrue(len(result.methods) > 0)
    
    def test_class_with_fields(self):
        """Test class with field definitions."""
        translator = StmtTranslator()
        code = """
class Point:
    x: int
    y: int
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, ClassDef)
        self.assertTrue(len(result.fields) >= 2)
    
    def test_class_method(self):
        """Test class with methods."""
        translator = StmtTranslator()
        code = """
class Counter:
    def increment(self):
        self.value += 1
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, ClassDef)
        method_names = [m.name for m in result.methods]
        self.assertIn('increment', method_names)


class TestAsyncFeatures(unittest.TestCase):
    """Test async/await features."""
    
    def test_async_function(self):
        """Test async function definition."""
        translator = StmtTranslator()
        code = """
async def fetch():
    await coro()
"""
        tree = ast.parse(code, mode='exec')
        result = translator.visit(tree.body[0])
        self.assertIsInstance(result, AsyncFunctionDef)
        self.assertEqual(result.name, 'fetch')


class TestSyntaxModuleExports(unittest.TestCase):
    """Test that all new syntax classes are properly exported."""
    
    def test_try_exports(self):
        """Test Try and ExceptHandler are exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Try']), 'Try'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['ExceptHandler']), 'ExceptHandler'))
    
    def test_loop_exports(self):
        """Test ForLoop, Break, Continue are exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['ForLoop']), 'ForLoop'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Break']), 'Break'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Continue']), 'Continue'))
    
    def test_with_exports(self):
        """Test With is exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['With']), 'With'))
    
    def test_aug_assign_exports(self):
        """Test AugAssign is exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['AugAssign']), 'AugAssign'))
    
    def test_raise_exports(self):
        """Test Raise is exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Raise']), 'Raise'))
    
    def test_global_nonlocal_exports(self):
        """Test Global and Nonlocal are exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Global']), 'Global'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Nonlocal']), 'Nonlocal'))
    
    def test_import_exports(self):
        """Test ImportStmt and ImportFrom are exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['ImportStmt']), 'ImportStmt'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['ImportFrom']), 'ImportFrom'))
    
    def test_lambda_exports(self):
        """Test Lambda is exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Lambda']), 'Lambda'))
    
    def test_generator_exports(self):
        """Test Yield and YieldFrom are exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Yield']), 'Yield'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['YieldFrom']), 'YieldFrom'))
    
    def test_await_exports(self):
        """Test Await is exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Await']), 'Await'))
    
    def test_match_exports(self):
        """Test Match and related patterns are exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Match']), 'Match'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['MatchCase']), 'MatchCase'))
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Pattern']), 'Pattern'))
    
    def test_walrus_exports(self):
        """Test Walrus is exported."""
        self.assertTrue(hasattr(__import__('veripy.parser.syntax', fromlist=['Walrus']), 'Walrus'))


if __name__ == '__main__':
    unittest.main()
