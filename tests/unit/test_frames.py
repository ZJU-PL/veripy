import unittest
import veripy as vp
from veripy import verify, invariant
from typing import List


class TestFrames(unittest.TestCase):
    """Test cases for frame conditions and modifies clauses."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_returns_old_of_n(self):
        """Test function that returns old value with modifies clause."""
        vp.scope('test_returns_old_of_n')
        @verify(requires=['n >= 0'], ensures=['ans == old(n)'], modifies=['ans'])
        def returns_old_of_n(n: int) -> int:
            ans = n
            return ans
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_inc_first(self):
        """Test function that modifies first element of array."""
        vp.scope('test_inc_first')
        @verify(requires=['len(xs) > 0'], ensures=['xs[0] == old(xs[0]) + 1'], modifies=['xs'])
        def inc_first(xs: List[int]) -> None:
            xs[0] = xs[0] + 1
        
        # Verify that the function passes verification
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
