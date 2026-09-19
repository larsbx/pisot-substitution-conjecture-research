## 2024-10-27 - Fast character comparisons and flattening in Python
**Learning:** For performance-critical code in Python, using `itertools.chain.from_iterable()` to flatten lists is much faster than repeatedly calling `extend()`. For inner loops over zipped iterables, using early returns and `not variable` instead of `variable == 0` offers significant performance benefits.
**Action:** When working on array algorithms, prioritize built-in C-backed iterator functions like `itertools.chain` for flattening, and short-circuit hot loops explicitly.
