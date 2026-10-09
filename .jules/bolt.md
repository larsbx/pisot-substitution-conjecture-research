## 2024-05-18 - Fast Evaluation of Polynomials in Python
**Learning:** In exact Python arithmetic using `fractions.Fraction`, division is relatively slow. Precomputing and caching the inverse (e.g., `inv = Fraction(1, b[db])`) outside tight loops to replace division with multiplication yields measurable performance improvements. When evaluating fixed-size polynomials, manually unroll Horner's method. Defer Fraction instantiation to avoid overhead. Filtering out explicitly zero terms in polynomial division before computation can lead to massive speedups.

## 2024-05-18 - Recalculating polynomial degree inside a loop
**Learning:** Recalculating polynomial degree inside a loop (e.g., `degree(a)` in `_poly_rem`) causes O(N) backward scan overhead. Cache the degree variable and decrement it inline, skipping explicitly zeroed terms, to maintain optimal time complexity.

## 2024-05-18 - Unrolling Fixed-Size Matrix Multiplication
**Learning:** In Python, specifically for mathematical inner loops like matrix multiplication, unrolling fixed-size loops (e.g., sizes 2 and 3) and avoiding list comprehensions and generator overhead provides significant speedups.
**Action:** Unroll fixed-size operations where it doesn't overly compromise readability and when those operations are in a hot path.
