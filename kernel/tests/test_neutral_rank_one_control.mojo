"""A literal single-pair neutral line for a positive unit PIP matrix.

Contract: docs/c4-neutral-rank-literature-2026-11-17.md. This pins the
previously scratch-only unit control of c4-round3-2026-11-16.md, section 5.3.
The first nonzero defect of T13 is K3 and spans a ONE-dimensional neutral
line, even with a primitive irreducible Pisot unit incidence matrix.
The two-dimensional determinant eigenspace is therefore not a rank lower
bound for a single literal pair. A rank-two lower bound for a strict system
would need a new argument using literal child closure.

This is deliberately not a strict-system witness. The explicit run-length
substitution realizing the matrix starts every image with 0. Its inflation
of T13 has first irreducible factor (0,0), which is coincident. T13 is not
asserted to be a factor of the substitution language. No bigon occurrence
matrix, aligned nonproductive sink, coincidence rank or C4 conclusion is
constructed.

Arithmetic: the external fixture matrices supplied to Mat3/tensor_cube_apply
have entries at most 42,000. Before those calls the finite input bounds are checked. For
the 13-letter pair, every scattered degree-three count is at most
C(13,3)=286. Thus each partial sum in the 27-term tensor contraction has
absolute value at most 27*42,000^3*286 = 572,107,536,000,000,000 < 2^63-1.
Determinant partial sums are bounded by 6*42,000^3; Mat3 squaring and its
trace formula are smaller. These bounds certify the machine-integer
vendored kernels on this fixed fixture. Pisot root tests and ranks use
the existing unbounded exact rational kernels.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from finite_linear_algebra.mat3 import Mat3
from finite_linear_algebra.qlinalg import rank
from finite_linear_algebra.tensor3 import tensor_cube_apply, theta
from mojo_smoke.claims import require_contract
from psc.bpa import coincidence_boundaries, decompose, substitution_incidence
from psc.exact import eval_int_poly_at_q, q_int, q_sign, q_vec
from psc.pisot import is_pip
from psc.words import Pair, is_balanced, is_zero, k1, k2, k3
from psc.w3 import in_w3


def _digits(s: String) -> List[Int]:
    var result = List[Int]()
    for b in s.as_bytes():
        result.append(Int(b) - 48)
    return result^


def _unit_matrix() raises -> Mat3:
    var m0 = Mat3([5, 21, 1, 6, 26, 1, 6, 24, 1])
    # All entries <=26, so m0^2 and this quadratic expression are safe.
    for x in m0.e:
        assert_true(x > 0 and x <= 26)
    var square = m0 * m0
    var entries = List[Int]()
    for i in range(3):
        for j in range(3):
            entries.append(51 * square.at(i, j) - 7 * m0.at(i, j) - (3 if i == j else 0))
    var m = Mat3(entries)
    assert_equal(m, Mat3([7969, 34278, 1370, 9750, 41941, 1676, 9138, 39306, 1571]))
    for x in m.e:
        assert_true(x > 0 and x <= 42000)
    return m^


def _run_length_substitution(m: Mat3) -> List[List[Int]]:
    # sigma(j) = 0^M[0,j] 1^M[1,j] 2^M[2,j]. Fixed, fully specified words.
    var sigma = List[List[Int]]()
    for j in range(3):
        var word = List[Int]()
        for a in range(3):
            for _ in range(m.at(a, j)):
                word.append(a)
        sigma.append(word^)
    return sigma^


def main() raises:
    var p = Pair(_digits("1222200110120"), _digits("2201121220001"))
    assert_equal(p.length(), 13)
    assert_true(is_balanced(p))
    var expected_cuts: List[Int] = [0, 13]
    assert_equal(coincidence_boundaries(p.u, p.v), expected_cuts)
    assert_true(is_zero(k1(p)))
    assert_true(is_zero(k2(p)))
    var defect = k3(p)
    assert_false(is_zero(defect))
    assert_true(in_w3(defect))
    for x in defect:
        assert_true(abs(x) <= 286)

    var m = _unit_matrix()
    assert_equal(27 * 42000 * 42000 * 42000 * 286, 572107536000000000)
    assert_true(572107536000000000 < 9223372036854775807)
    assert_equal(m.det(), -1)
    var chi = m.charpoly()
    var expected_chi: List[Int] = [1, 30023, -51481, 1]
    assert_equal(chi, expected_chi)
    assert_true(is_pip(m))
    # Independent exact root brackets: one root in (-1,0), one in (0,1),
    # one in (1,51482); monic cubic with constant 1 has no rational root
    # because neither +1 nor -1 is a root. All entries are positive.
    assert_equal(q_sign(eval_int_poly_at_q(chi, q_int(-1))), -1)
    assert_equal(q_sign(eval_int_poly_at_q(chi, q_int(0))), 1)
    assert_equal(q_sign(eval_int_poly_at_q(chi, q_int(1))), -1)
    assert_equal(q_sign(eval_int_poly_at_q(chi, q_int(51482))), 1)

    var image = tensor_cube_apply(m, defect)
    var swapped = k3(Pair(p.v, p.u))
    for i in range(27):
        assert_equal(image[i], -defect[i])
        assert_equal(swapped[i], -defect[i])
    var columns_as_rows = List[List[Q]]()
    columns_as_rows.append(q_vec(defect))
    columns_as_rows.append(q_vec(swapped))
    assert_equal(rank(columns_as_rows), 1)
    assert_equal(theta(defect).trace(), 0)
    assert_equal(theta(defect) * m, m * theta(defect))

    var sigma = _run_length_substitution(m)
    assert_equal(Mat3(substitution_incidence(sigma)), m)
    assert_equal(len(sigma[0]), 26857)
    assert_equal(len(sigma[1]), 115525)
    assert_equal(len(sigma[2]), 4617)
    # The displayed one-letter words are actual initial prefixes of the
    # two inflated source words. A balanced length-one prefix is already
    # the first irreducible factor, irrespective of every later symbol.
    var first_top: List[Int] = [sigma[p.u[0]][0]]
    var first_bottom: List[Int] = [sigma[p.v[0]][0]]
    var zero_word: List[Int] = [0]
    assert_equal(first_top, zero_word)
    assert_equal(first_bottom, zero_word)
    var first_factor = decompose(first_top, first_bottom)
    assert_equal(len(first_factor), 1)
    assert_equal(first_factor[0], Pair(zero_word, zero_word))

    print("Neutral rank-one literal-pair control: T13; det=-1; chi=x^3-51481*x^2+30023*x+1; exact PIP; rank[K3,-K3]=1.")
    print("K3 lex coefficients:", defect)
    print("Theta(K3):", theta(defect))
    print("Explicit run-length substitution lengths: 26857,115525,4617; first literal factor=(0,0); NOT a strict component.")
    require_contract("Neutral rank-one calibration: the irreducible literal pair T13 has first defect K3 with a rank-one swap-odd span and M^(tensor3)K3=-K3 for the positive unit PIP matrix M=-3I-7M0+51M0^2; the explicit run-length substitution with that incidence has a coincident first child, so no strict-system realization or rank-two lower bound is asserted")
