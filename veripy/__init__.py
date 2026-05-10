"""
Veripy - An auto-active verification system for Python.

This package provides comprehensive verification capabilities for Python programs,
inspired by Dafny and Verus.
"""

# Import submodules to ensure they're registered
from . import parser
from . import typecheck
from . import built_ins
from . import log
from . import core
from . import auto_active
from . import error
from . import recursive
from . import cli
from . import contracts
from . import sidecar
from . import lean

# Re-export key APIs for convenience
from .core import (
    verify,
    assume,
    invariant,
    decreases,
    do_verification,
    enable_verification,
    scope,
    verify_all,
    STORE,
    VerificationStore,
    StmtTranslator,
    ExprTranslator,
    Expr2Z3,
    subst,
    pretty_print
)

from .contracts import (
    requires,
    guarantee,
    ensures,
    contract_decreases,
    extract_spec
)

from .sidecar import (
    about,
    proof_for,
    z3_hint,
    law
)

from .lean import (
    LeanCertificate,
    compile_to_lean
)

from .auto_active import (
    AutoActiveEngine,
    LemmaEngine,
    TerminationChecker,
    InferenceStrategy,
    InvariantCandidate,
    auto_active_engine,
    lemma_engine,
    termination_checker,
    auto_infer_invariants,
    generate_arithmetic_lemmas,
    register_lemma,
    verify_lemma,
    check_termination,
    assert_by
)

from .error import (
    ErrorReporter,
    ErrorSeverity,
    ErrorCategory,
    SourceLocation,
    Counterexample,
    VerificationError,
    error_reporter,
    report_verification_failure,
    print_verification_report,
    extract_source_location,
    parse_smt_model
)

from .recursive import (
    RecursiveVerifier,
    RecursionType,
    RecursiveCall,
    DecreasesInfo,
    recursive_verifier,
    verify_recursive,
    verify_all_recursive
)

from .cli import __version__

__all__ = [
    # Submodules
    'parser',
    'typecheck',
    'built_ins',
    'log',
    'core',
    'auto_active',
    'error',
    'recursive',
    'cli',
    'contracts',
    'sidecar',
    'lean',
    
    # Core verification
    'verify',
    'assume',
    'invariant',
    'decreases',
    'do_verification',
    'enable_verification',
    'scope',
    'verify_all',
    'STORE',
    'VerificationStore',
    'StmtTranslator',
    'ExprTranslator',
    'Expr2Z3',
    'subst',
    'pretty_print',
    'requires',
    'guarantee',
    'ensures',
    'contract_decreases',
    'extract_spec',
    'about',
    'proof_for',
    'z3_hint',
    'law',
    'LeanCertificate',
    'compile_to_lean',
    
    # Auto-active verification
    'AutoActiveEngine',
    'LemmaEngine',
    'TerminationChecker',
    'InferenceStrategy',
    'InvariantCandidate',
    'auto_active_engine',
    'lemma_engine',
    'termination_checker',
    'auto_infer_invariants',
    'generate_arithmetic_lemmas',
    'register_lemma',
    'verify_lemma',
    'check_termination',
    'assert_by',
    
    # Error reporting
    'ErrorReporter',
    'ErrorSeverity',
    'ErrorCategory',
    'SourceLocation',
    'Counterexample',
    'VerificationError',
    'error_reporter',
    'report_verification_failure',
    'print_verification_report',
    'extract_source_location',
    'parse_smt_model',
    
    # Recursive verification
    'RecursiveVerifier',
    'RecursionType',
    'RecursiveCall',
    'DecreasesInfo',
    'recursive_verifier',
    'verify_recursive',
    'verify_all_recursive',
    
    # Version
    '__version__'
]
