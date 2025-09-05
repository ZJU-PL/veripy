# Unit Tests

This directory contains unit tests for the veripy verification system. Each test file focuses on a specific aspect of verification functionality.

## Test Files

- `test_arrays.py` - Tests for array operations and verification
- `test_calls.py` - Tests for function calls and recursive functions
- `test_counter.py` - Tests for counter function with invariants
- `test_decreases.py` - Tests for functions with decreases clauses
- `test_frames.py` - Tests for frame conditions and modifies clauses
- `test_loops.py` - Tests for loop verification with invariants
- `test_quantifiers.py` - Tests for quantifier verification
- `test_structures.py` - Tests for data structures verification

## Running Tests

To run all unit tests:
```bash
python -m unittest discover tests/unit
```

To run a specific test file:
```bash
python -m unittest tests.unit.test_arrays
```

To run a specific test method:
```bash
python -m unittest tests.unit.test_arrays.TestArrays.test_set_first
```

## Test Structure

Each test file follows the standard unittest pattern:
- Uses `unittest.TestCase` as the base class
- Sets up verification in `setUp()` method with `vp.enable_verification()` and `vp.scope()`
- Contains individual test methods that define functions with `@verify` decorators
- Each test method calls `vp.verify_all()` to perform verification
- The test passes if verification succeeds (no exception) and fails if verification fails (exception raised)

The tests verify that the verification system correctly validates the specified preconditions, postconditions, and invariants. The core assertion is that `vp.verify_all()` completes without raising an exception, indicating that all verification conditions are satisfied.