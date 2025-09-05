import unittest
import veripy as vp
from veripy import verify, invariant


class TestCalls(unittest.TestCase):
    """Test cases for function calls and recursive functions."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
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
        """Test recursive sum function."""
        vp.scope('test_rec_sum')
        @verify(requires=['n >= 0'], ensures=['ans >= n'])
        def rec_sum(n: int) -> int:
            if n == 0:
                return 0
            return n + rec_sum(n - 1)
        
        # Verify that the function passes verification
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
