"""Exact, occurrence-level classification of a newborn balanced cut.

This *bounded executable check* reads literal inflated words, not a quotient
packet. The uniform bilateral-birth rigidity theorem is proved in
docs/c4-bilateral-birth-rigidity-2026-11-02.md, not by enumerating inputs.

A caller must supply an irreducible balanced parent T, nonsingular incidence
matrix, and an actual interior zero-return position of sigma(T). The helper
checks these hypotheses and returns the asynchronous source addresses and
exact prefix-defect/correction relation. No global C4, BH, G1 or PSC inference.
"""

from psc.bpa import apply_substitution, coincidence_boundaries, image_prefix_lengths, substitution_incidence
from psc.words import Pair, is_balanced


struct CutBirth(Copyable, Movable):
    var cut: Int
    var top_source: Int
    var bottom_source: Int
    var top_digit: Int
    var bottom_digit: Int
    var top_boundary: Bool
    var bottom_boundary: Bool
    var source_defect: List[Int]
    var local_correction: List[Int]

    def __init__(
        out self, cut: Int, top_source: Int, bottom_source: Int,
        top_digit: Int, bottom_digit: Int,
        source_defect: List[Int], local_correction: List[Int],
    ):
        self.cut = cut
        self.top_source = top_source
        self.bottom_source = bottom_source
        self.top_digit = top_digit
        self.bottom_digit = bottom_digit
        self.top_boundary = top_digit == 0
        self.bottom_boundary = bottom_digit == 0
        self.source_defect = source_defect.copy()
        self.local_correction = local_correction.copy()


def _prefix_counts(w: List[Int], end: Int) raises -> List[Int]:
    if end < 0 or end > len(w):
        raise Error("prefix index out of range")
    var result: List[Int] = [0, 0, 0]
    for k in range(end):
        if w[k] < 0 or w[k] >= 3:
            raise Error("letter out of three-letter alphabet")
        result[w[k]] += 1
    return result^


def _address(bounds: List[Int], cut: Int) raises -> List[Int]:
    if len(bounds) == 0 or cut < 0 or cut > bounds[len(bounds) - 1]:
        raise Error("cut outside source-image boundaries")
    for i in range(len(bounds) - 1):
        if cut < bounds[i + 1]:
            var address: List[Int] = [i, cut - bounds[i]]
            return address^
    var terminal: List[Int] = [len(bounds) - 1, 0]
    return terminal^


def _det3(m: List[Int]) raises -> Int:
    if len(m) != 9:
        raise Error("three-letter incidence matrix must have nine entries")
    return (
        m[0] * (m[4] * m[8] - m[5] * m[7])
        - m[1] * (m[3] * m[8] - m[5] * m[6])
        + m[2] * (m[3] * m[7] - m[4] * m[6])
    )


def classify_irreducible_birth(
    sigma: List[List[Int]], parent: Pair, cut: Int,
) raises -> CutBirth:
    """Reconstruct one literal interior zero return, fail closed on bad input.

    Machine Int is safe in this diagnostic: three images have length <= 64;
    each parent side has <= 4096 letters. The derived incidence entries
    are <= 64, so 3x3 determinant and matrix/defect products stay bounded.
    This cap is a *runtime scope*, not a theorem's mathematical hypothesis.
    """
    if len(sigma) != 3:
        raise Error("requires exactly three substitution images")
    for a in range(3):
        if len(sigma[a]) == 0 or len(sigma[a]) > 64:
            raise Error("image length outside checked arithmetic budget")
        for j in range(len(sigma[a])):
            if sigma[a][j] < 0 or sigma[a][j] >= 3:
                raise Error("invalid substitution letter")
    if len(parent.u) == 0 or len(parent.u) > 4096 or len(parent.v) != len(parent.u):
        raise Error("parent outside checked arithmetic budget")
    if not is_balanced(parent):
        raise Error("parent is not balanced")
    var parent_cuts = coincidence_boundaries(parent.u, parent.v)
    if len(parent_cuts) != 2 or parent_cuts[0] != 0 or parent_cuts[1] != len(parent.u):
        raise Error("parent is not irreducible")

    var m = substitution_incidence(sigma)
    if _det3(m) == 0:
        raise Error("incidence matrix is singular")

    var top = apply_substitution(sigma, parent.u)
    var bottom = apply_substitution(sigma, parent.v)
    if len(top) != len(bottom) or cut <= 0 or cut >= len(top):
        raise Error("cut must be strictly interior to equally long inflated words")
    var cuts = coincidence_boundaries(top, bottom)
    var is_return = False
    for k in range(len(cuts)):
        if cuts[k] == cut:
            is_return = True
            break
    if not is_return:
        raise Error("cut is not an actual balanced zero return")

    var a = _address(image_prefix_lengths(sigma, parent.u), cut)
    var b = _address(image_prefix_lengths(sigma, parent.v), cut)
    if a[0] >= len(parent.u) or b[0] >= len(parent.v):
        raise Error("interior cut maps to terminal source")
    var pt = _prefix_counts(parent.u, a[0])
    var pb = _prefix_counts(parent.v, b[0])
    var qt = _prefix_counts(sigma[parent.u[a[0]]], a[1])
    var qb = _prefix_counts(sigma[parent.v[b[0]]], b[1])
    var defect: List[Int] = [0, 0, 0]
    var correction: List[Int] = [0, 0, 0]
    for x in range(3):
        defect[x] = pt[x] - pb[x]
        correction[x] = qt[x] - qb[x]
        var total = correction[x]
        for y in range(3):
            total += m[3 * x + y] * defect[y]
        if total != 0:
            raise Error("literal cut fails the exact asynchronous inflation law")
    if a[1] == 0 and b[1] == 0:
        # Invertibility forces equal source prefix Parikh vectors; equal
        # counts force equal indices; irreducibility forbids this interior.
        raise Error("bilaterally aligned interior return contradicts irreducibility")

    return CutBirth(cut, a[0], b[0], a[1], b[1], defect, correction)
