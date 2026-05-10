"""
Tests for the Lean 4 backend.
"""

import tempfile
import unittest
from pathlib import Path
from typing import List

import veripy as vp


@vp.verify(requires=["x > 0"], ensures=["ans > x"])
def lean_succ(x: int) -> int:
    return x + 1


@vp.verify(ensures=["ans >= 0"])
def lean_abs_like(x: int) -> int:
    ans = x
    if x < 0:
        ans = -x
    return ans


@vp.verify(requires=["len(xs) > 0"], ensures=["ans >= 0"])
def lean_first(xs: List[int]) -> int:
    ans = xs[0]
    return ans


@vp.verify(requires=["x > 0"], ensures=["ans > x + 1"])
def lean_twice(x: int) -> int:
    y = lean_succ(x)
    ans = y + 1
    return ans


class TestLeanBackend(unittest.TestCase):
    def test_compile_simple_function_to_vc_theorem(self):
        cert = vp.compile_to_lean(lean_succ)
        text = cert.render()

        self.assertIn("theorem lean_succ_vc", text)
        self.assertIn("((x > 0) → ((x + 1) > x))", text)
        self.assertEqual(cert.trust_level, "LEAN_SYNTAX_COMPLETE")
        self.assertEqual(cert.sorry_count, 0)

    def test_compile_supported_if_shape(self):
        cert = vp.compile_to_lean(lean_abs_like)
        text = cert.render()

        self.assertIn("theorem lean_abs_like_vc", text)
        self.assertIn("(x < 0)", text)
        self.assertEqual(cert.sorry_count, 0)

    def test_heap_lowered_vc_mentions_heap_state(self):
        cert = vp.compile_to_lean(lean_first)
        text = cert.render()

        self.assertIn("__heap_list_len", text)
        self.assertIn("__heap_list_data_int", text)
        self.assertIn("theorem lean_first_vc", text)
        self.assertGreaterEqual(cert.sorry_count, 1)

    def test_user_call_vc_emits_summary_assumption(self):
        cert = vp.compile_to_lean(lean_twice)
        text = cert.render()

        self.assertIn("h_summary_lean_succ", text)
        self.assertIn("__uf_lean_succ__ans", text)
        self.assertIn("theorem lean_twice_vc", text)
        self.assertGreaterEqual(cert.sorry_count, 1)

    def test_write_and_verify_with_missing_lean_binary(self):
        cert = vp.compile_to_lean(lean_succ)

        with tempfile.TemporaryDirectory() as tmpdir:
            output = Path(tmpdir) / "lean_succ.lean"
            cert.write(output)
            self.assertTrue(output.exists())

        cert.verify_with_lean(lean_cmd="/definitely/missing/lean")
        self.assertEqual(cert.trust_level, "LEAN_UNAVAILABLE")


if __name__ == "__main__":
    unittest.main()
