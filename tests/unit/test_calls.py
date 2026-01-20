import unittest
import veripy as vp
from veripy import verify, invariant
from veripy.core.verify import STORE


class TestCalls(unittest.TestCase):
    """Test cases for function calls and recursive functions."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def tearDown(self):
        """Clean up verification state after each test."""
        # Reset the STORE to prevent cross-test contamination
        STORE.store.clear()
        STORE.scope.clear()
        STORE.func_attrs_global.clear()
        STORE.pre_states.clear()
        STORE.current_func = None
        STORE.self_call = False
    
    def test_inc(self):
        """Test simple increment function."""
        vp.scope('test_inc')
        @verify(requires=['n >= 0'], ensures=['ans == n + 1'])
        def inc(n: int) -> int:
            return n + 1
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_inc2(self):
        """Test function that calls another function twice."""
        vp.scope('test_inc2')
        @verify(requires=['n >= 0'], ensures=['ans == n + 1'])
        def inc(n: int) -> int:
            return n + 1
        
        @verify(requires=['n >= 0'], ensures=['ans == n + 2'])
        def inc2(n: int) -> int:
            x = inc(n)
            return inc(x)
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_rec_sum(self):
        """Recursive calls without decreases are rejected."""
        vp.scope('test_rec_sum')
        @verify(requires=['n >= 0'], ensures=['ans >= n'])
        def rec_sum(n: int) -> int:
            if n == 0:
                return 0
            return n + rec_sum(n - 1)
        
        with self.assertRaises(Exception):
            vp.verify_all()  # Default now raises on failure

    def test_requires_verified_callee(self):
        """Calls to specs not yet verified should fail."""
        vp.scope('test_requires_verified_callee')

        @verify(requires=[], ensures=['ans == 0'])
        def caller() -> int:
            return callee()

        @verify(requires=[], ensures=['ans == 0'])
        def callee() -> int:
            return 0

        with self.assertRaises(Exception):
            vp.verify_all()  # Default now raises on failure


if __name__ == '__main__':
    unittest.main()
