
## 2026-10-09 - Remove Generator and Built-in Overhead in Inner Python Loops
**Learning:** In tight Python metric loops, using generator expressions or passing them into built-in functions like `max()`, `abs()`, or `all()` can incur significant frame creation and iteration overhead, dramatically reducing performance (up to a ~2x slowdown).
**Action:** Replace `max(abs(x) for x in range(...))` with unrolled `for` loop logic tracking the maximum value via inline conditional logic (`if v < 0: v = -v; if v > m: m = v`). Replace `all(isinstance(x, T))` with inline `type(x) is not T` checks.
