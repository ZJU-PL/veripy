import unittest
import veripy as vp


class TestCounter(unittest.TestCase):
    """Test cases for counter function with verification."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_counter(self):
        """Test counter function with invariants."""
        vp.scope('test_counter')
        @vp.verify(requires=['n >= 0'], ensures=['ans == n'])
        def counter(n: int) -> int:
            y = n
            ans = 0
            while y > 0:
                vp.invariant('ans + y == n')
                vp.invariant('y >= 0')
                ans = ans + 1
                y = y - 1
            return ans
        
        # Verify that the function passes verification
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
