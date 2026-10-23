
## 2024-05-18 - Fraction Generator/Bound Loop Overhead
**Learning:** In exact arithmetic arrays like Routh, replacing `all(x == 0 for x in current)` with a simple `for` loop that sets a boolean flag and `break`s avoids significant generator expression instantiation and iteration overhead in Python. Furthermore, unrolling bounds checking (e.g. `min_len`) into separate loops for the shared prefix, `above`, and `current` entirely avoids repeated `Fraction(0)` instantiations.
**Action:** Unroll lengths checks inside numeric kernel loops processing varying-length sequences. When optimizing zero checks inside tight polynomial inner-loops, replace `all(x == 0 for x in ...)` and `any(x == 0 for x in ...)` with explicit loops that break early, preventing generator expression overhead.
