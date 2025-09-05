import unittest
import veripy as vp
from veripy import verify


class TestQuantifiers(unittest.TestCase):
    """Test cases for quantifier verification."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_inc_preserves_order(self):
        """Test that increment preserves order with quantifiers."""
        vp.scope('test_inc_preserves_order')
        @verify(ensures=['forall x : int :: x > 0 ==> n + x > n'])
        def inc_preserves_order(n: int) -> int:
            return n
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_plus_comm(self):
        """Test commutativity of addition with quantifiers."""
        vp.scope('test_plus_comm')
        @verify(ensures=['forall x :: forall y :: x + y == y + x'])
        def plus_comm() -> None:
            a = 1
            b = 2
            c = a + b
            if c < 0:
                c = 0
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_exists_greater(self):
        """Test existence of greater number with quantifiers."""
        vp.scope('test_exists_greater')
        @verify(ensures=['forall x :: exists y :: y > x'])
        def exists_greater() -> None:
            z = 0
            z = z + 1
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_de_morgan(self):
        """Test De Morgan's law with quantifiers."""
        vp.scope('test_de_morgan')
        @verify(ensures=['forall x :: forall y :: not (x and y) <==> (not x) or (not y)'])
        def de_morgan() -> None:
            t: bool = True
            f: bool = False
            if t and f:
                t = False
        
        # Verify that the function passes verification
        vp.verify_all()
    
    def test_double_negation(self):
        """Test double negation law with quantifiers."""
        vp.scope('test_double_negation')
        @verify(ensures=['forall x :: (not (not x)) <==> x'])
        def double_negation() -> None:
            b: bool = True
            if not b:
                b = True
        
        # Verify that the function passes verification
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
