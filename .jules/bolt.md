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
## 2024-09-26 - Unroll small fixed-size vector operations
**Learning:** In pure Python math routines, using generator expressions or `zip` for small, fixed-size mathematical operations (like 2D or 3D vector addition or 3x3 matrix multiplication) carries extreme overhead (up to 3x slower) compared to direct scalar operations and array indexing.
**Action:** Unroll fixed-size loops for mathematical functions when the size is known (e.g., `len(a) == 3`) directly, avoiding comprehensions.
