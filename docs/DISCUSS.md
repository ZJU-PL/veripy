# Veripy Feature Discussion

## Current State Analysis

Veripy is an auto-active verification library for Python that currently supports:

### ✅ **Implemented Features**
- Basic verification over ints/bools (assign/if/while/assert/assume)
- Quantifiers in contracts: `forall`, `exists` (typed as `: int`/`: bool`)
- `Havoc` for `while` encoding and weakest preconditions
- Arrays via theory of arrays: `xs[i]`, `xs[i] = v` (functional `store`)
- Refinement types: `Refined[T, predicate]` with convenient syntax
- Loop invariants and weakest precondition calculus
- Function contracts (requires/ensures/modifies/reads)
- Basic type system with arrays, sets, dictionaries
- SMT solver integration (Z3)

### 🚧 **Work in Progress**
- Function calls (partial implementation)
- More AST mappings

---

## Proposed Features (Inspired by Dafny, LiquidHaskell, Viper, etc.)

### 1. **Advanced Type System**

#### 1.1 **Ghost Types and Ghost Variables**
```python
# Ghost variables for specification
@verify(requires=[], ensures=['ghost_result == x + y'])
def add_with_ghost(x: int, y: int) -> int:
    ghost_result = x + y  # Ghost variable, not in compiled code
    return x + y
```

#### 1.2 **Enhanced Type Annotations with Verification**
```python
# Use Python's existing type system with verification
@verify(ensures=['ans >= 0'])
def tree_sum(t: 'Tree') -> int:
    if hasattr(t, 'value'):  # Leaf case
        return t.value
    else:  # Node case
        return tree_sum(t.left) + tree_sum(t.right)

# Tree class using standard Python
class Tree:
    def __init__(self, value=None, left=None, right=None):
        self.value = value
        self.left = left
        self.right = right
```

#### 1.3 **Generic Types with Verification**
```python
from typing import TypeVar, Callable, List

T = TypeVar('T')

@verify(ensures=['len(ans) == len(xs)'])
def map_int(xs: List[T], f: Callable[[T], int]) -> List[int]:
    return [f(x) for x in xs]
```

#### 1.4 **Refinement Types for Complex Constraints**
```python
# Use refinement types for dependent-like properties
@verify(ensures=['len(ans) == n'])
def create_vector(n: Refined[int, "n >= 0"]) -> List[int]:
    return [0] * n
```

### 2. **Advanced Specifications**

#### 2.1 **Frame Conditions and Memory Safety**
```python
@verify(
    requires=['len(arr) > 0'],
    ensures=['arr[0] == new_val'],
    modifies=['arr[0]'],  # Only modifies arr[0]
    reads=['arr']         # Only reads from arr
)
def update_first(arr: List[int], new_val: int) -> None:
    arr[0] = new_val
```

#### 2.2 **Decreases Clauses for Termination**
```python
@verify(
    requires=['n >= 0'],
    ensures=['ans == n * (n + 1) // 2'],
    decreases='n'  # Prove termination
)
def sum_to_n(n: int) -> int:
    if n == 0:
        return 0
    else:
        return n + sum_to_n(n - 1)
```

#### 2.3 **Old Values in Postconditions**
```python
@verify(
    ensures=['ans == old(x) + old(y)']
)
def add_old(x: int, y: int) -> int:
    x = x + 1  # x changes but old(x) refers to original value
    return x + y
```

#### 2.4 **Predicates and Lemmas**
```python
@predicate
def is_sorted(xs: List[int]) -> bool:
    """Predicate defining sortedness"""
    return forall i: int :: forall j: int :: 
           (0 <= i and i < j and j < len(xs)) ==> xs[i] <= xs[j]

@lemma
def sorted_append_lemma(xs: List[int], ys: List[int]) -> None:
    """Lemma: if xs and ys are sorted, then xs + ys is sorted"""
    requires=[is_sorted(xs), is_sorted(ys)]
    ensures=[is_sorted(xs + ys)]
    # Proof body
    pass
```

### 3. **Concurrency and Concurrency Safety**

#### 3.1 **Atomic Operations**
```python
@atomic
@verify(ensures=['ans == old(x) + 1'])
def atomic_increment(x: int) -> int:
    return x + 1
```

#### 3.2 **Permission System (Inspired by Viper)**
```python
@verify(
    requires=['acc(x, write)'],  # Need write permission to x
    ensures=['acc(x, write) and x == old(x) + 1']
)
def increment_with_permission(x: int) -> None:
    x = x + 1
```

### 4. **Advanced Control Flow**

#### 4.1 **Exception Handling**
```python
@verify(
    requires=['x >= 0'],
    ensures=['ans >= 0 or raises(ValueError)']
)
def safe_sqrt(x: int) -> int:
    if x < 0:
        raise ValueError("Negative input")
    return int(x ** 0.5)
```

#### 4.2 **Break and Continue in Loops**
```python
@verify(ensures=['ans >= 0'])
def find_positive(xs: List[int]) -> int:
    for x in xs:
        if x > 0:
            break
        continue
    return x
```

#### 4.3 **Enhanced Control Flow with Standard Python**
```python
# Use Python's existing control flow with verification
@verify(ensures=['ans >= 0'])
def process_optional(opt: Optional[int]) -> int:
    if opt is not None:
        return opt
    else:
        return 0
```

### 5. **Advanced Data Structures**

#### 5.1 **Sets and Maps with Specifications**
```python
@verify(
    ensures=['ans == old(s).union({x})']
)
def set_add(s: Set[int], x: int) -> Set[int]:
    return s.union({x})
```

#### 5.2 **Mutable vs Immutable Collections**
```python
# Immutable list operations
@verify(
    ensures=['len(ans) == len(xs) + 1']
)
def cons(x: int, xs: ImmutableList[int]) -> ImmutableList[int]:
    return xs.prepend(x)
```

#### 5.3 **Custom Data Structure Specifications**
```python
# Use standard Python classes with verification
class Stack:
    def __init__(self):
        self._items: List[T] = []
    
    @verify(ensures=['ans == len(self._items) == 0'])
    def is_empty(self) -> bool:
        return len(self._items) == 0
    
    @verify(ensures=['ans == len(self._items)'])
    def size(self) -> int:
        return len(self._items)
    
    @verify(
        requires=['not self.is_empty()'],
        ensures=['ans == old(self._items[-1])']
    )
    def pop(self) -> T:
        return self._items.pop()
```

### 6. **Proof Automation and Hints**

#### 6.1 **Proof Hints and Tactics**
```python
@verify(ensures=['ans == x * x'])
def square(x: int) -> int:
    # Proof hint: use distributivity
    @hint("distributivity")
    result = x * x
    return result
```

#### 6.2 **Assert Statements for Intermediate Proofs**
```python
@verify(ensures=['ans == n * (n + 1) // 2'])
def sum_to_n(n: int) -> int:
    if n == 0:
        return 0
    else:
        # Intermediate assertion to help the prover
        assert n > 0
        return n + sum_to_n(n - 1)
```

#### 6.3 **Proof by Cases**
```python
@verify(ensures=['ans >= 0'])
def abs_value(x: int) -> int:
    if x >= 0:
        # Case 1: x >= 0
        return x
    else:
        # Case 2: x < 0
        return -x
```

### 7. **Integration and Tooling**

#### 7.1 **IDE Integration**
- Real-time verification feedback
- Error highlighting and suggestions
- Counterexample generation
- Proof visualization

#### 7.2 **Test Generation**
```python
@verify(ensures=['ans >= 0'])
def abs_value(x: int) -> int:
    return abs(x)

# Auto-generate test cases
@test_generator
def test_abs_value():
    # Generate test cases that satisfy preconditions
    # and verify postconditions
    pass
```

#### 7.3 **Documentation Generation**
```python
@verify(
    requires=['x >= 0'],
    ensures=['ans == x * x'],
    doc="Computes the square of a non-negative integer"
)
def square(x: int) -> int:
    """Squares the input value.
    
    Args:
        x: Non-negative integer to square
        
    Returns:
        The square of x
        
    Raises:
        VerificationError: If x < 0
    """
    return x * x
```

### 8. **Performance and Optimization**

#### 8.1 **Compilation to Efficient Code**
```python
@verify(ensures=['ans == x + y'])
@compile_optimize  # Generate optimized code
def add_optimized(x: int, y: int) -> int:
    return x + y
```

#### 8.2 **Resource Bounds**
```python
@verify(
    ensures=['ans == sum(xs)'],
    time_bound='O(n)',  # Time complexity
    space_bound='O(1)'  # Space complexity
)
def sum_list(xs: List[int]) -> int:
    # Implementation
    pass
```

### 9. **Advanced Verification Features**

#### 9.1 **Counterexample Generation**
```python
@verify(ensures=['ans > 0'])
def positive_square(x: int) -> int:
    return x * x  # This will fail, generate counterexample
```

#### 9.2 **Proof Certificates**
```python
@verify(ensures=['ans == x + y'], generate_certificate=True)
def add_certified(x: int, y: int) -> int:
    return x + y
```

#### 9.3 **Incremental Verification**
```python
# Verify only changed parts
@verify(incremental=True)
def complex_function(x: int) -> int:
    # Only re-verify if this function changes
    pass
```

### 10. **Domain-Specific Features**

#### 10.1 **Floating-Point Verification**
```python
@verify(
    requires=['x >= 0.0'],
    ensures=['abs(ans - sqrt(x)) < epsilon']
)
def safe_sqrt(x: float) -> float:
    return math.sqrt(x)
```

#### 10.2 **String and Text Processing**
```python
@verify(
    ensures=['len(ans) == len(s) and ans == s.upper()']
)
def to_upper(s: str) -> str:
    return s.upper()
```

#### 10.3 **Network and I/O Specifications**
```python
@verify(
    ensures=['ans.status_code == 200 or ans.status_code == 404']
)
def safe_http_get(url: str) -> HttpResponse:
    # Implementation with network error handling
    pass
```

---

## Implementation Priority

### **Phase 1: Core Language Features**
1. Ghost variables for specifications
2. Frame conditions and memory safety
3. Decreases clauses for termination
4. Old values in postconditions
5. Enhanced refinement types

### **Phase 2: Advanced Specifications**
1. Predicates and lemmas
2. Exception handling
3. Enhanced control flow verification
4. Advanced data structures with standard Python classes

### **Phase 3: Tooling and Integration**
1. IDE integration
2. Test generation
3. Documentation generation
4. Counterexample generation

### **Phase 4: Advanced Features**
1. Concurrency support
2. Performance optimization
3. Domain-specific features
4. Proof automation

---

## Comparison with Other Tools

### **Dafny**
- ✅ Similar contract syntax
- ✅ Loop invariants and decreases
- ❌ Missing: ghost variables, lemmas, Python integration

### **LiquidHaskell**
- ✅ Refinement types
- ✅ Predicate logic
- ❌ Missing: imperative features, frame conditions, Python integration

### **Viper**
- ✅ Permission system
- ✅ Memory safety
- ❌ Missing: high-level language features, Python integration

### **F* / Lean**
- ✅ Proof automation
- ✅ Advanced type theory
- ❌ Missing: Python integration, practical verification

---

## Next Steps

1. **Immediate**: Complete function call support
2. **Short-term**: Implement ghost variables and enhanced refinement types
3. **Medium-term**: Add frame conditions and termination proofs
4. **Long-term**: Full IDE integration and advanced tooling

This roadmap focuses on enhancing Python's existing capabilities with verification rather than extending the language itself, making veripy a practical and accessible verification tool that works seamlessly with standard Python code.