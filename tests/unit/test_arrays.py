import unittest
import veripy as vp
from veripy import verify, invariant
from typing import List


class TestArrays(unittest.TestCase):
    """Test cases for array operations and verification."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_set_first(self):
        """Test setting the first element of an array."""
        vp.scope('test_set_first')
        @verify(requires=[], ensures=['xs[0] == v'])
        def set_first(xs: List[int], v: int) -> None:
            xs[0] = v
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_array_argmax(self):
        """Test array argmax function with invariants."""
        vp.scope('test_array_argmax')
        @verify(requires=['n >= 0'], ensures=[])
        def array_argmax(a: List[int], n: int) -> int:
            i = 0
            j = 0
            while j < n:
                invariant('0 <= j and j <= n')
                invariant('0 <= i and i <= j')
                j = j + 1
            return i
        
        # Verify that the function passes verification
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
