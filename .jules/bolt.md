## 2024-09-13 - Optimize discrepancy computation
**Learning:** Python loops over small fixed-size objects (like iterating over a list of size 3 in a list comprehension inside a zip loop) can dominate execution time compared to a constant number of direct assignments and calls like `max`. Replacing `max(abs(c) for c in diff)` inside an O(N) loop with `max(best, abs(diff[x - 1]), abs(diff[y - 1]))` yields a major speedup (about 5-6x faster in Python).
**Action:** When working in Python inner loops (like graph searches or metric accumulations in `psc_research`), look out for list comprehensions or implicit loops inside generator expressions, especially for things of constant size, and unroll/inline them directly to save overhead. Also, skip operations when state doesn't mutate (e.g. `x == y`).
## 2026-09-14 - Optimize coincidence boundary computation
**Learning:** Checking for equality of two arrays `pu == pv` or checking for non-zero differences `any(diff)` in the inner loop (like in `coincidence_boundaries`) adds significant overhead. Keeping a running count `non_zero` of the number of non-zero elements in the `diff` array allows replacing O(size) list scans with a single O(1) integer comparison `non_zero == 0`.
**Action:** When tracking multidimensional state changes sequentially (like prefix Parikh vectors), avoid O(size) vector comparisons inside loops. Maintain an active diff vector and a simple count of discrepancies.

## 2024-09-15 - Optimize inner polynomial multiplication loop
**Learning:** In Q(beta) calculations within Python (like `Field.mul` in `overlap_graph.py`), list allocations inside hot inner loops (e.g. `c = [Fraction(0)] * 5`) and nested loops evaluating small constant-size dimensions (like 3x3 matrices) cause major overhead. Evaluating unused list comprehensions inside `while` loops also tanks performance.
**Action:** Unroll fixed-size (e.g., 3x3) mathematical loops manually. Write explicit linear combinations for dimensions that are small and known at compile time to avoid loop control and array access costs. Remove all dead assignments inside loops.
## 2025-02-18 - Avoid Fraction overhead inside loops
**Learning:** Arbitrary precision `Fraction` arithmetic is heavily penalized in Python inside tight loops due to continual GCD calculations and object instantiation.
**Action:** Always compute intermediates natively as integers, replacing algorithms with equivalent native implementations like `math.comb`, and cast to `Fraction` only at the end.

## 2025-02-18 - C-delegation can break complexity
**Learning:** Moving a Python loop to a C-level function (like `list.count`) might look faster on micro-benchmarks but can silently increase algorithmic complexity (e.g., from O(N) to O(N * alphabet_size)), causing massive performance regressions on large inputs.
**Action:** Always ensure that time complexity invariants are strictly preserved before replacing loops with built-ins.
## 2026-09-17 - Fast evaluation of exact polynomials
**Learning:** Evaluating polynomials using `for c in reversed(p): acc=acc*x+c` creates overhead from the `reversed()` iterator and the loop structure itself. Because Python exact arithmetic (using `Fraction`) incurs significant object allocation overhead, loop unrolling for fixed-degree polynomials, alongside converting division to multiplication via precomputed inverses in division loops, provides major speedups. Iterating backward via a `while` loop is also faster than allocating a sequence via `range(n, -1, -1)`.
**Action:** Unroll mathematical evaluation loops manually for constant small sizes. In division algorithms, pull inverses out of inner loops.
## 2024-06-25 - Defer Fraction casting in tight mathematical evaluation loops
**Learning:** Python's `Fraction` class is notoriously slow because it performs GCD calculations on every arithmetic operation. Specifically, in `pisot_screen.evaluate`, accumulating a polynomial via Horner's method using `Fraction` instantiations resulted in significant object creation and calculation overhead.
**Action:** Defer `Fraction` instantiation to the end when evaluating polynomials with integer coefficients. We can track numerator and denominator powers separately using pure integer arithmetic within the loop, leading to a measured 10x speedup in tight paths. Always enforce strict typing bounds (`type(c) is not int` -> `TypeError`) when skipping the Fraction wrapping.
