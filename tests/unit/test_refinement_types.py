import unittest
import veripy as vp
from veripy import verify, invariant
from veripy.refinement import Refined, PositiveInt, NonNegativeInt, EvenInt, RangeInt, NonEmptyList
from typing import List


class TestRefinementTypes(unittest.TestCase):
    """Test cases for refinement types."""
    
    def setUp(self):
        """Set up verification for each test."""
        vp.enable_verification()
    
    def test_positive_int_refinement(self):
        """Test function with positive integer refinement type."""
        vp.scope('test_positive_int')
        
        @verify(requires=[], ensures=['ans > 0'])
        def square_positive(x: Refined[int, "x > 0"]) -> int:
            return x * x
        
        vp.verify_all()
    
    def test_non_negative_int_refinement(self):
        """Test function with non-negative integer refinement type."""
        vp.scope('test_non_negative_int')
        
        @verify(requires=[], ensures=['ans >= 0'])
        def factorial(n: Refined[int, "n >= 0"]) -> int:
            if n == 0:
                return 1
            else:
                return n * factorial(n - 1)
        
        vp.verify_all()
    
    def test_even_int_refinement(self):
        """Test function with even integer refinement type."""
        vp.scope('test_even_int')
        
        @verify(requires=[], ensures=['ans % 2 == 0'])
        def double_even(x: Refined[int, "x % 2 == 0"]) -> int:
            return x * 2
        
        vp.verify_all()
    
    def test_range_int_refinement(self):
        """Test function with range refinement type."""
        vp.scope('test_range_int')
        
        @verify(requires=[], ensures=['ans >= 0 and ans < 100'])
        def process_score(score: Refined[int, "score >= 0 and score < 100"]) -> int:
            return score
        
        vp.verify_all()
    
    def test_non_empty_list_refinement(self):
        """Test function with non-empty list refinement type."""
        vp.scope('test_non_empty_list')
        
        @verify(requires=[], ensures=['len(ans) > 0'])
        def get_first_element(xs: Refined[List[int], "len(xs) > 0"]) -> int:
            return xs[0]
        
        vp.verify_all()
    
    def test_convenience_functions(self):
        """Test convenience functions for common refinement types."""
        vp.scope('test_convenience_functions')
        
        @verify(requires=[], ensures=['ans > 0'])
        def square_positive_convenience(x: PositiveInt()) -> int:
            return x * x
        
        @verify(requires=[], ensures=['ans >= 0'])
        def abs_non_negative(x: NonNegativeInt()) -> int:
            return x
        
        @verify(requires=[], ensures=['ans % 2 == 0'])
        def double_even_convenience(x: EvenInt()) -> int:
            return x * 2
        
        vp.verify_all()
    
    def test_refinement_with_loop_invariant(self):
        """Test refinement types with loop invariants."""
        vp.scope('test_refinement_with_loop')
        
        @verify(requires=[], ensures=['ans >= 0'])
        def sum_positive_numbers(n: Refined[int, "n >= 0"]) -> int:
            result = 0
            i = 0
            while i < n:
                invariant('i >= 0 and i <= n')
                invariant('result >= 0')
                result = result + i
                i = i + 1
            return result
        
        vp.verify_all()
    
    def test_refinement_subtyping(self):
        """Test that refinement types are subtypes of their base types."""
        vp.scope('test_refinement_subtyping')
        
        @verify(requires=[], ensures=['ans > 0'])
        def process_positive(x: Refined[int, "x > 0"]) -> int:
            # This should work because Refined[int, "x > 0"] <: int
            return x + 1
        
        vp.verify_all()


if __name__ == '__main__':
    unittest.main()
