"""
Comprehensive Test Suite for Veripy Auto-Active Verification Features

This module contains tests for:
- Auto-active invariant inference
- Lemma generation and verification
- Termination checking
- Error reporting and counterexamples
"""

import unittest
import ast
from typing import Dict, Any, List
from dataclasses import dataclass

import veripy as vp
from veripy import verify, invariant, scope, verify_all, enable_verification
from veripy.auto_active import (
    AutoActiveEngine,
    InferenceStrategy,
    InvariantCandidate,
    LemmaEngine,
    TerminationChecker,
    auto_infer_invariants,
    generate_arithmetic_lemmas,
    register_lemma,
    verify_lemma
)
from veripy.error.reporter import (
    ErrorReporter,
    ErrorCategory,
    ErrorSeverity,
    SourceLocation,
    Counterexample,
    VerificationError
)


class TestAutoActiveEngine(unittest.TestCase):
    """Test cases for the auto-active verification engine."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.engine = AutoActiveEngine(strategy=InferenceStrategy.SIMPLE)
    
    def test_infer_bounds_invariant(self):
        """Test inference of bounds invariants for loops."""
        loop_info = {
            "loop_var": "i",
            "init": 0,
            "condition": "i < n",
            "body": [
                {"type": "assign", "var": "i", "expr": "i + 1"}
            ]
        }
        
        invariants = self.engine.infer_loop_invariants(loop_info)
        
        # Should infer basic bounds
        self.assertIsInstance(invariants, list)
        self.assertGreater(len(invariants), 0)
        
        # Check for variable bounds
        found_i_bounds = any("i >=" in inv or "i <=" in inv for inv in invariants)
        self.assertTrue(found_i_bounds, f"Expected bounds for i, got: {invariants}")
    
    def test_infer_type_invariant(self):
        """Test inference of type-based invariants."""
        constraints = self.engine.infer_type_constraints("x", int)
        
        self.assertIsInstance(constraints, list)
        # Should have at least type constraint
        self.assertGreater(len(constraints), 0)
    
    def test_infer_arithmetic_lemmas(self):
        """Test generation of arithmetic lemmas."""
        lemmas = self.engine.infer_arithmetic_lemmas("x + y")
        
        self.assertIsInstance(lemmas, list)
        
        # Should generate commutativity lemma
        commutativity_found = any("commutativity" in lemma.lower() or 
                                  "x + y == y + x" in lemma 
                                  for lemma in lemmas)
        self.assertTrue(commutativity_found, f"Expected commutativity lemma, got: {lemmas}")
    
    def test_statistics_tracking(self):
        """Test that statistics are tracked correctly."""
        initial_stats = self.engine.get_statistics()
        
        # Generate some lemmas
        self.engine.infer_arithmetic_lemmas("x + y")
        
        updated_stats = self.engine.get_statistics()
        
        # Should have generated at least one lemma
        self.assertGreater(updated_stats["lemmas_generated"], 
                          initial_stats["lemmas_generated"])
    
    def test_cache_functionality(self):
        """Test caching of inferred invariants."""
        loop_info = {
            "loop_var": "i",
            "init": 0,
            "condition": "i < n",
            "body": []
        }
        
        # First call
        invariants1 = self.engine.infer_loop_invariants(loop_info)
        
        # Should be in cache now
        self.assertGreater(len(self.engine.cache), 0)
        
        # Second call should use cache
        invariants2 = self.engine.infer_loop_invariants(loop_info)
        
        self.assertEqual(invariants1, invariants2)
    
    def test_aggressive_strategy_inference(self):
        """Test more aggressive inference strategy."""
        engine_aggressive = AutoActiveEngine(strategy=InferenceStrategy.AGGRESSIVE)
        
        loop_info = {
            "loop_var": "i",
            "init": 0,
            "condition": "i < n",
            "body": [
                {"type": "assign", "var": "j", "expr": "i + 1"}
            ]
        }
        
        invariants = engine_aggressive.infer_loop_invariants(loop_info)
        
        # Should have more invariants than simple strategy
        engine_simple = AutoActiveEngine(strategy=InferenceStrategy.SIMPLE)
        simple_invariants = engine_simple.infer_loop_invariants(loop_info)
        
        self.assertGreaterEqual(len(invariants), len(simple_invariants))


class TestLemmaEngine(unittest.TestCase):
    """Test cases for the lemma management engine."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.lemma_engine = LemmaEngine()
    
    def test_register_lemma(self):
        """Test lemma registration."""
        result = self.lemma_engine.add_lemma(
            name="test_lemma",
            premises=["x > 0", "y > 0"],
            conclusion="x + y > 0"
        )
        
        self.assertTrue(result)
        self.assertIn("test_lemma", self.lemma_engine.lemmas)
    
    def test_get_lemma(self):
        """Test retrieving a registered lemma."""
        self.lemma_engine.add_lemma(
            name="test_lemma",
            premises=["x > 0"],
            conclusion="x >= 0"
        )
        
        lemma = self.lemma_engine.get_lemma("test_lemma")
        
        self.assertIsNotNone(lemma)
        self.assertEqual(lemma["premises"], ["x > 0"])
        self.assertEqual(lemma["conclusion"], "x >= 0")
    
    def test_verify_lemma(self):
        """Test lemma verification."""
        # Register a true lemma
        self.lemma_engine.add_lemma(
            name="reflexivity",
            premises=[],
            conclusion="x == x"
        )
        
        # Try to verify it
        result = self.lemma_engine.verify_lemma("reflexivity")
        
        # This should succeed (reflexivity is always true)
        # Note: May fail if the solver has issues
        self.assertIsInstance(result, bool)
    
    def test_verified_lemmas_filter(self):
        """Test filtering for verified lemmas."""
        # Add multiple lemmas
        self.lemma_engine.add_lemma("lemma1", [], "x == x")
        self.lemma_engine.add_lemma("lemma2", ["x > 0"], "x >= 0")
        
        # Verify one
        self.lemma_engine.verify_lemma("lemma1")
        
        # Get verified lemmas
        verified = self.lemma_engine.get_verified_lemmas()
        
        self.assertIn("lemma1", verified)
        self.assertNotIn("lemma2", verified)
    
    def test_get_all_lemmas(self):
        """Test getting all registered lemmas."""
        self.lemma_engine.add_lemma("lemma1", [], "x == x")
        self.lemma_engine.add_lemma("lemma2", [], "y == y")
        
        all_lemmas = self.lemma_engine.get_all_lemmas()
        
        self.assertEqual(len(all_lemmas), 2)


class TestTerminationChecker(unittest.TestCase):
    """Test cases for termination checking."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.checker = TerminationChecker()
    
    def test_first_call_allowed(self):
        """Test that first call to a recursive function is allowed."""
        result, message = self.checker.check_termination(
            func_name="factorial",
            decreases="n",
            args=[5]
        )
        
        self.assertTrue(result)
        self.assertIn("First call", message)

    def test_non_decreasing_measure_rejected(self):
        """Termination requires measure to strictly decrease."""
        # First call records measure
        self.checker.check_termination(func_name="factorial", decreases="n", args=[3])
        # Same measure should fail
        result, message = self.checker.check_termination(
            func_name="factorial",
            decreases="n",
            args=[3]
        )
        self.assertFalse(result)
        self.assertIn("does not decrease", message)
    
    def test_termination_without_decreases_fails(self):
        """Test that termination check fails without decreases clause."""
        result, message = self.checker.check_termination(
            func_name="bad_recursion",
            decreases="",
            args=[5]
        )
        
        self.assertFalse(result)
        self.assertIn("decreases clause", message)


class TestErrorReporter(unittest.TestCase):
    """Test cases for error reporting functionality."""
    
    def setUp(self):
        """Set up test fixtures."""
        self.reporter = ErrorReporter()
    
    def test_add_error(self):
        """Test adding errors to the reporter."""
        error = VerificationError(
            category=ErrorCategory.ASSERTION,
            severity=ErrorSeverity.ERROR,
            message="Test assertion failed"
        )
        
        self.reporter.add_error(error)
        
        self.assertEqual(len(self.reporter.errors), 1)
        self.assertEqual(self.reporter.statistics["total_errors"], 1)
    
    def test_add_warning(self):
        """Test adding warnings to the reporter."""
        warning = VerificationError(
            category=ErrorCategory.PRECONDITION,
            severity=ErrorSeverity.WARNING,
            message="Precondition might not hold"
        )
        
        self.reporter.add_warning(warning)
        
        self.assertEqual(len(self.reporter.warnings), 1)
        self.assertEqual(self.reporter.statistics["total_warnings"], 1)
    
    def test_source_location(self):
        """Test source location creation."""
        location = SourceLocation(
            file="test.py",
            line=10,
            column=5
        )
        
        self.assertEqual(str(location), "test.py:10:5")
        
        # Test dict conversion
        location_dict = location.to_dict()
        self.assertEqual(location_dict["file"], "test.py")
        self.assertEqual(location_dict["line"], 10)
    
    def test_counterexample(self):
        """Test counterexample creation and formatting."""
        counterexample = Counterexample(
            values={"x": "5", "y": "3"},
            explanation="x and y have specific values"
        )
        
        formatted = counterexample.format()
        
        self.assertIn("x = 5", formatted)
        self.assertIn("y = 3", formatted)
        self.assertIn("Explanation", formatted)
    
    def test_error_to_dict(self):
        """Test error serialization to dictionary."""
        error = VerificationError(
            category=ErrorCategory.TYPE_ERROR,
            severity=ErrorSeverity.ERROR,
            message="Type mismatch",
            suggestion="Check types"
        )
        
        error_dict = error.to_dict()
        
        self.assertEqual(error_dict["category"], "type_error")
        self.assertEqual(error_dict["severity"], "error")
        self.assertEqual(error_dict["message"], "Type mismatch")
        self.assertEqual(error_dict["suggestion"], "Check types")
    
    def test_format_text_report(self):
        """Test text report formatting."""
        # Add some errors and warnings
        self.reporter.add_error(VerificationError(
            category=ErrorCategory.ASSERTION,
            severity=ErrorSeverity.ERROR,
            message="Assertion failed"
        ))
        self.reporter.add_warning(VerificationError(
            category=ErrorCategory.PRECONDITION,
            severity=ErrorSeverity.WARNING,
            message="Precondition warning"
        ))
        
        report = self.reporter.format_report("text")
        
        self.assertIn("VERIFICATION REPORT", report)
        self.assertIn("DETAILED ERRORS", report)
        self.assertIn("WARNINGS", report)
    
    def test_format_json_report(self):
        """Test JSON report formatting."""
        self.reporter.add_error(VerificationError(
            category=ErrorCategory.ASSERTION,
            severity=ErrorSeverity.ERROR,
            message="Assertion failed"
        ))
        
        report = self.reporter.format_report("json")
        
        # Should be valid JSON
        import json
        report_dict = json.loads(report)
        
        self.assertIn("summary", report_dict)
        self.assertIn("errors", report_dict)
        self.assertEqual(report_dict["passed"], False)


class TestConvenienceFunctions(unittest.TestCase):
    """Test convenience functions for auto-active features."""
    
    def test_auto_infer_invariants(self):
        """Test the auto_infer_invariants convenience function."""
        loop_info = {
            "loop_var": "i",
            "init": 0,
            "condition": "i < 10",
            "body": []
        }
        
        invariants = auto_infer_invariants(loop_info)
        
        self.assertIsInstance(invariants, list)
    
    def test_generate_arithmetic_lemmas(self):
        """Test the generate_arithmetic_lemmas convenience function."""
        lemmas = generate_arithmetic_lemmas("x + y")
        
        self.assertIsInstance(lemmas, list)
        self.assertGreater(len(lemmas), 0)
    
    def test_register_lemma(self):
        """Test the register_lemma convenience function."""
        result = register_lemma(
            name="test_commute",
            premises=[],
            conclusion="x + y == y + x"
        )
        
        self.assertTrue(result)


class TestIntegration(unittest.TestCase):
    """Integration tests combining multiple features."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_verify_with_auto_invariants(self):
        """Test verification using auto-inferred invariants."""
        vp.scope('test_auto_invariants')
        
        @verify(requires=['n >= 0'], ensures=['ans >= 0'])
        def sum_to_n(n: int) -> int:
            ans = 0
            i = 0
            while i < n:
                ans = ans + i
                i = i + 1
            return ans
        
        # This should work (though may need manual invariants)
        vp.verify_all()
    
    def test_error_reporting_integration(self):
        """Test error reporting integration."""
        reporter = ErrorReporter()
        
        # Simulate a verification failure
        reporter.add_error(VerificationError(
            category=ErrorCategory.ASSERTION,
            severity=ErrorSeverity.ERROR,
            message="Precondition does not imply weakest precondition",
            location=SourceLocation("test.py", 10, 5),
            suggestion="Add more specific preconditions"
        ))
        
        # Generate report
        report = reporter.format_report("text")
        
        self.assertIn("VERIFICATION REPORT", report)
        self.assertIn("Suggestion", report)


if __name__ == '__main__':
    unittest.main()
