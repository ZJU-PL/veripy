import unittest
import veripy as vp
from veripy import verify, invariant


class TestDecreases(unittest.TestCase):
    """Test cases for functions with decreases clauses."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_countdown(self):
        """Test countdown function with decreases clause."""
        vp.scope('test_countdown')
        @verify(requires=['n >= 0'], ensures=['ans == 0'], decreases='n')
        def countdown(n: int) -> int:
            ans = 0
            while n > 0:
                invariant('n >= 0')
                n = n - 1
            return ans
        
        # Verify that the function passes verification
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
