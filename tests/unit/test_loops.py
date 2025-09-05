import unittest
import veripy as vp
from veripy import verify, invariant


class TestLoops(unittest.TestCase):
    """Test cases for loop verification with invariants."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_mul_by_addition(self):
        """Test multiplication by addition using while loop."""
        vp.scope('test_mul_by_addition')
        @verify(requires=['a >= 0', 'b >= 0'], ensures=['ans == a * b'])
        def mul_by_addition(a: int, b: int) -> int:
            ans = 0
            n = a
            while n > 0:
                invariant('n >= 0')
                invariant('ans == (a - n) * b')
                ans = ans + b
                n = n - 1
            return ans
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_summation(self):
        """Test summation using for loop."""
        vp.scope('test_summation')
        @verify(requires=['n >= 0'], ensures=['ans == ((n + 1) * n) // 2'])
        def summation(n: int) -> int:
            ans = 0
            for i in range(0, n + 1):
                invariant('i <= n + 1')
                invariant('ans == i * (i - 1) // 2')
                ans = ans + i
            return ans
        
        # Verify that the function passes verification
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
