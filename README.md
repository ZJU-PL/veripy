# Veripy

A production-ready auto-active verification system for Python, similar to Dafny and Verus.

## Overview

Veripy transforms Python code verification from a work-in-progress into a production-ready system with automatic invariant inference, comprehensive error reporting, and a professional CLI.

## Soundness note

Veripy is **not sound for full Python** today. The core VC engine is intended to be sound for a restricted, “verification-oriented” subset (roughly: side-effect-free code over `int`/`bool` plus mathematical arrays, with structured `if`/`while`, and user-supplied invariants), and it rejects or approximates many Python features (exceptions, dynamic dispatch, aliasing/mutation semantics of real lists/dicts/objects, etc.).

Recent work is moving toward a Dafny/Boogie-style explicit heap model for **aliasing + mutation** (lists/dicts/fields as references) and for **exception safety** (e.g., bounds and `div/mod` by zero become proof obligations). This is still a work in progress and many Python features remain unsupported.

## Key Features

### Auto-Active Verification
- Automatic loop invariant inference
- Type-based constraint generation
- Arithmetic lemma automation
- Multiple inference strategies (NONE, SIMPLE, AGGRESSIVE, FULL)

### Production Readiness
- Professional CLI with multiple commands
- Rich terminal output with syntax highlighting
- JSON output for CI/CD
- Comprehensive error reporting with counterexamples
- Source location tracking

### Recursive Functions
- Termination checking with decreases clauses
- Tail recursion detection
- Call graph analysis

## Installation

```bash
pip install py-veripy
```

For development:
```bash
make install-dev
```

## Usage

### Basic Verification
```python
import veripy as vp

vp.enable_verification()

@vp.verify(requires=['x > 0'], ensures=['ans == x * 2'])
def double(x: int) -> int:
    return x * 2

vp.verify_all()
```

### Deppy-Style Contracts
```python
import veripy as vp

vp.enable_verification()
vp.scope("demo")

@vp.verify()
@vp.requires("x > 0")
@vp.guarantee("result > x")
def succ(x: int) -> int:
    return x + 1

vp.verify_all()
```

Veripy normalizes Deppy-style `result` postconditions to its internal `ans`
binding and also exposes lightweight sidecar metadata helpers such as
`@vp.about(...)`, `@vp.proof_for(...)`, and `@vp.z3_hint(...)`.

### Lean4 Export
```python
import veripy as vp

@vp.verify(requires=["x > 0"], ensures=["ans > x"])
def succ(x: int) -> int:
    return x + 1

cert = vp.compile_to_lean(succ)
print(cert.render())

# Optional, if Lean is installed locally:
# cert.verify_with_lean()
```

The Lean backend now exports Veripy's actual heap-lowered VC obligations rather
than re-translating raw Python syntax. In practice that means the generated Lean
theorems track the same `pre => wp` and side-condition formulas the SMT backend
checks, including summary assumptions for verified callees and explicit heap
state binders when lists/dicts/fields are involved.

### CLI Usage
```bash
# Verify files
veripy verify file.py

# With counterexamples and statistics
veripy verify --counterexample --statistics file.py

# JSON output for CI/CD
veripy verify --output json file.py
```

### Auto-Active Features
```python
from veripy.auto_active import auto_infer_invariants

invariants = auto_infer_invariants({
    "loop_var": "i",
    "init": 0,
    "condition": "i < n",
    "body": []
})
```

## Architecture

```
veripy/
├── core/           # Verification condition generation, AST transformation
├── auto_active/    # Auto-active features (invariant inference, lemmas)
├── cli/            # Command-line interface
├── parser/         # Syntax parsing
├── typecheck/      # Type checking
├── error_reporter.py
├── recursive.py
└── prettyprint.py
```

## Development

```bash
make test          # Run tests
make test-cov      # With coverage
make lint          # Linting
make format        # Formatting
make typecheck     # Type checking
make check         # All checks
```

## Dependencies

- `z3-solver` - SMT solver
- `rich` - Terminal output
- `click` - CLI framework
- `pyparsing` - Expression parsing
- `apronpy` - Abstract interpretation

## Related Work

- Nagini: https://github.com/marcoeilers/nagini
