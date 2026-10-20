
## 2024-05-15 - Fraction arithmetic hidden overheads
**Learning:** Fraction addition/subtraction of `Fraction(0)` is incredibly slow due to underlying `math.gcd` calculations and new object creation on every operation. Also, Fraction division `a / b` is noticeably slower than `a * Fraction(b.denominator, b.numerator)`.
**Action:** When implementing polynomial division loops or matrix rows over Fractions, pre-calculate the inverse of divisors and strictly skip zero terms (e.g. `b_non_zeros = [(i, val) for i, val in enumerate(b) if val != 0]`) to avoid massive accumulated GCD slowdowns.

## 2024-05-15 - Generator comprehension overhead in math loops
**Learning:** Checking `any(x == 0 for x in current)` inside an inner polynomial loop adds extreme frame and iterator overhead compared to a basic `for x in current: if x == 0: break`.
**Action:** Unroll single-line checks like `all()` and `any()` into traditional for loops inside hot mathematical routines (like Routh arrays).
