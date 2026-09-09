"""The shuffle-kernel sector W_3 = ker(S) subset V^{(x)3}.

`w3_basis()` is *derived* from the shuffle functional. The certificate's printed
basis (§3) is reproduced separately so the two can be compared.
"""

from psc.rational import Rat, rat_vec
from psc.qlinalg import nullspace, in_span, rank
from psc.tensor3 import shuffle_matrix, shuffle_image, idx3, zeros27, is_zero27


def w3_basis() -> List[List[Rat]]:
    """A Q-basis of `ker(S)`, computed by exact nullspace elimination."""
    return nullspace(shuffle_matrix(), 27)


def _vec(entries: List[Int]) -> List[Int]:
    """Sparse `[a, b, c, coeff, ...]` triple-plus-coefficient form to a 27-vector."""
    var v = zeros27()
    var i = 0
    while i < len(entries):
        v[idx3(entries[i] - 1, entries[i + 1] - 1, entries[i + 2] - 1)] = entries[i + 3]
        i += 4
    return v^


def certificate_w3_basis() -> List[List[Int]]:
    """The eight vectors b_1..b_8 printed in PROOF_CERTIFICATE.md §3."""
    var out = List[List[Int]]()
    var b1: List[Int] = [1,1,2, 1, 1,2,1, -2, 2,1,1, 1]
    var b2: List[Int] = [1,2,2, 1, 2,1,2, -2, 2,2,1, 1]
    var b3: List[Int] = [1,1,3, 1, 1,3,1, -2, 3,1,1, 1]
    var b4: List[Int] = [1,3,2, -1, 2,1,3, 1, 2,3,1, -1, 3,1,2, 1]
    var b5: List[Int] = [1,2,3, 1, 1,3,2, -1, 2,3,1, -1, 3,2,1, 1]
    var b6: List[Int] = [2,2,3, 1, 2,3,2, -2, 3,2,2, 1]
    var b7: List[Int] = [1,3,3, 1, 3,1,3, -2, 3,3,1, 1]
    var b8: List[Int] = [2,3,3, 1, 3,2,3, -2, 3,3,2, 1]
    out.append(_vec(b1))
    out.append(_vec(b2))
    out.append(_vec(b3))
    out.append(_vec(b4))
    out.append(_vec(b5))
    out.append(_vec(b6))
    out.append(_vec(b7))
    out.append(_vec(b8))
    return out^


def in_w3(x: List[Int]) -> Bool:
    """Membership in `W_3`, decided directly by the defining relations."""
    return is_zero27(shuffle_image(x))


def spans_same_space(intbasis: List[List[Int]], qbasis: List[List[Rat]]) -> Bool:
    """Whether an integer family and a rational family span the same subspace."""
    var lifted = List[List[Rat]]()
    for i in range(len(intbasis)):
        lifted.append(rat_vec(intbasis[i]))
    if rank(lifted) != len(qbasis):
        return False
    for i in range(len(qbasis)):
        if not in_span(lifted, qbasis[i]):
            return False
    return True
