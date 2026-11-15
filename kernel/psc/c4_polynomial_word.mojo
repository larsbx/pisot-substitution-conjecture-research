"""Compressed word identities with exponents polynomial in nonnegative parameters.

For a concrete word w, attach sum(w[i] * X^i) and its length. Concatenation
shifts the right sum. Repetition multiplies by a geometric series. Sparse
terms keep the entire exponent polynomial as their key.
"""

from finite_exact.checked_int import checked_abs, checked_add, checked_mul, checked_sub
from psc.poly_line import Poly, poly_add, poly_const, poly_mul


def _norm(p: Poly) raises -> Int:
    var total = 0
    for term in p.terms.items():
        total = checked_add(total, checked_abs(term.value))
    return total


def _add(a: Poly, b: Poly) raises -> Poly:
    # The l1 bound covers every intermediate coefficient sum.
    _ = checked_add(_norm(a), _norm(b))
    return poly_add(a, b)


def _mul(a: Poly, b: Poly) raises -> Poly:
    _ = checked_mul(_norm(a), _norm(b))
    return poly_mul(a, b)


def _key(p: Poly) -> String:
    var monomials = List[Int]()
    for term in p.terms.items():
        monomials.append(term.key)
    for i in range(1, len(monomials)):
        var key = monomials[i]
        var j = i
        while j > 0 and key < monomials[j - 1]:
            monomials[j] = monomials[j - 1]
            j -= 1
        monomials[j] = key
    var code = String()
    for m in monomials:
        code += String(m) + ":" + String(p.terms.get(m, 0)) + ","
    return code^


@fieldwise_init
struct Term(Copyable, Movable):
    var exponent: Poly
    var coefficient: Int


def _add_term(mut sum: Dict[String, Term], e: Poly, c: Int) raises:
    var key = _key(e)
    var total = c
    if key in sum:
        total = checked_add(total, sum[key].coefficient)
    if total == 0:
        if key in sum:
            _ = sum.pop(key)
    else:
        sum[key] = Term(e.copy(), total)


def _multiply_geometric_numerator(mut sum: Dict[String, Term], e: Poly) raises:
    # Multiplication by (1 - X^e).
    var original = sum.copy()
    for entry in original.items():
        ref term = entry.value
        _add_term(sum, _add(term.exponent, e), checked_sub(0, term.coefficient))


def _missing_factors(have: List[Poly], need: List[Poly]) -> List[Poly]:
    var consumed = List[Bool](length=len(have), fill=False)
    var missing = List[Poly]()
    for factor in need:
        var matched = False
        var key = _key(factor)
        for j in range(len(have)):
            if not consumed[j] and _key(have[j]) == key:
                consumed[j] = True
                matched = True
                break
        if not matched:
            missing.append(factor.copy())
    return missing^


def _raise_denominator(sum: Dict[String, Term], have: List[Poly],
                       target: List[Poly]) raises -> Dict[String, Term]:
    var result = sum.copy()
    for factor in _missing_factors(have, target):
        _multiply_geometric_numerator(result, factor)
    return result^


struct Word(Copyable, Movable):
    var length: Poly
    var counts: List[Poly]
    var numerator: Dict[String, Term]
    # Each positive factor exponent e encodes a denominator (1 - X^e).
    var denominator: List[Poly]

    def __init__(out self):
        self.length = Poly()
        self.counts = [Poly(), Poly(), Poly()]
        self.numerator = Dict[String, Term]()
        self.denominator = List[Poly]()

    def then(self, rhs: Word) raises -> Word:
        var out = Word()
        out.length = _add(self.length, rhs.length)
        for a in range(3):
            out.counts[a] = _add(self.counts[a], rhs.counts[a])
        out.denominator = self.denominator.copy()
        for factor in _missing_factors(out.denominator, rhs.denominator):
            out.denominator.append(factor.copy())
        out.numerator = _raise_denominator(self.numerator, self.denominator, out.denominator)
        var right = _raise_denominator(rhs.numerator, rhs.denominator, out.denominator)
        for entry in right.items():
            ref term = entry.value
            _add_term(out.numerator, _add(self.length, term.exponent), term.coefficient)
        return out^

    def repeated(self, count: Poly) raises -> Word:
        for term in count.terms.items():
            if term.value < 0:
                raise Error("repetition count must be coefficientwise nonnegative")
        if len(count.terms) == 0:
            return Word()
        if len(count.terms) == 1 and count.terms.get(0, 0) == 1:
            return self.copy()

        var out = Word()
        out.length = _mul(self.length, count)
        for a in range(3):
            out.counts[a] = _mul(self.counts[a], count)
        if len(self.numerator) != 0:
            # Length polynomials are nonnegative by construction. Requiring
            # a positive constant ensures the denominator never vanishes
            # as an element of Q(X) after parameter specialization.
            if self.length.terms.get(0, 0) <= 0:
                raise Error("geometric denominator would lack a positive exponent")
            out.denominator = self.denominator.copy()
            out.denominator.append(self.length.copy())
            out.numerator = self.numerator.copy()
            _multiply_geometric_numerator(out.numerator, out.length)
        return out^

    def balanced_with(self, rhs: Word) -> Bool:
        for a in range(3):
            if _key(self.counts[a]) != _key(rhs.counts[a]):
                return False
        return True

    def equals(self, rhs: Word) raises -> Bool:
        if _key(self.length) != _key(rhs.length):
            return False
        var factors = self.denominator.copy()
        for factor in _missing_factors(factors, rhs.denominator):
            factors.append(factor.copy())
        var left = _raise_denominator(self.numerator, self.denominator, factors)
        var right = _raise_denominator(rhs.numerator, rhs.denominator, factors)
        if len(left) != len(right):
            return False
        for entry in left.items():
            if entry.key not in right or right[entry.key].coefficient != entry.value.coefficient:
                return False
        return True

    def nonempty_everywhere(self) -> Bool:
        return self.length.terms.get(0, 0) > 0


def letter(a: Int) raises -> Word:
    if not 0 <= a < 3:
        raise Error("letter outside the ternary alphabet")
    var out = Word()
    out.length = poly_const(1)
    out.counts[a] = poly_const(1)
    _add_term(out.numerator, Poly(), a)
    return out^
