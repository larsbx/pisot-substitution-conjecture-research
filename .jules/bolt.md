
## 2024-05-18 - Routh Array Fraction Inverse
**Learning:** In exact Python arithmetic using `fractions.Fraction`, constructing new objects for default/zero padding (e.g. `Fraction(0)`) and repeating division (`/ c0`) inside mathematical inner loops (like computing Routh array rows) adds massive overhead.
**Action:** Replace division by an invariant element with multiplication by its precomputed inverse (`inv = Fraction(c.denominator, c.numerator)`). Unroll inner loop bounds checking (`max(len(a), len(b))` with inline conditionals) into separate explicit loops over the shared prefix, the remainder of `a`, and the remainder of `b`, yielding ~20-30% performance improvements.
