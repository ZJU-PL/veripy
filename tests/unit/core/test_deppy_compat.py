"""
Tests for the Deppy-inspired compatibility layer.
"""

import unittest

import veripy as vp


class TestDeppyCompat(unittest.TestCase):
    def setUp(self):
        vp.enable_verification()

    def test_extracts_stackable_contract_metadata(self):
        @vp.requires("x > 0")
        @vp.guarantee("result > x")
        def succ(x: int) -> int:
            return x + 1

        spec = vp.extract_spec(succ)

        self.assertEqual(spec["requires"], ["x > 0"])
        self.assertEqual(spec["ensures"], ["ans > x"])
        self.assertIsNone(spec["decreases"])

    def test_verify_consumes_contract_decorators(self):
        vp.scope("deppy_contracts")

        @vp.verify()
        @vp.requires("x > 0")
        @vp.guarantee("result > x")
        def succ(x: int) -> int:
            return x + 1

        vp.verify_all()

    def test_verify_merges_explicit_and_decorator_contracts(self):
        vp.scope("deppy_contract_merge")

        @vp.verify(ensures=["ans >= x"])
        @vp.requires("x >= 0")
        @vp.guarantee("result >= 0")
        def identity(x: int) -> int:
            return x

        spec = vp.extract_spec(identity)
        self.assertEqual(spec["requires"], ["x >= 0"])
        self.assertEqual(spec["ensures"], ["ans >= 0", "ans >= x"])

        vp.verify_all()

    def test_sidecar_metadata_decorators_attach_attributes(self):
        @vp.about("math")
        @vp.proof_for("sqrt_nonnegative")
        @vp.z3_hint(mode="nonlinear")
        @vp.law("nonnegative", statement="x * x >= 0", domain="ints")
        def sqrt_spec(x: int) -> int:
            return x

        self.assertEqual(sqrt_spec._veripy_about, "math")
        self.assertEqual(sqrt_spec._veripy_proof_for, "sqrt_nonnegative")
        self.assertEqual(sqrt_spec._veripy_z3_hint, {"mode": "nonlinear"})
        self.assertTrue(sqrt_spec._veripy_law)
        self.assertEqual(sqrt_spec._veripy_law_name, "nonnegative")


if __name__ == "__main__":
    unittest.main()
