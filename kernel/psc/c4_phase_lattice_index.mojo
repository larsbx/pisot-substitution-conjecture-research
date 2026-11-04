"""Exact integral phase-lattice index conditions for a supplied strict Pisot SCC.

CONDITIONAL contract: caller must have independently established primitive
irreducible ternary Pisot incidence, a genuine literal complete strictly
child-closed SCC, and the actual period/class labels of its irreducible
child graph. This module checks ONLY necessary integer consequences.

Its bounded synthetic matrices do NOT certify a literal balanced-pair SCC.
"""
from psc.c4_two_generation_rank import _rank_det


struct PhaseLatticeIndex(Copyable, Movable):
    var det_M: Int
    var class_indices: List[Int]
    var transition_indices: List[Int]

    def __init__(
        out self, det_M: Int, class_indices: List[Int],
        transition_indices: List[Int],
    ):
        self.det_M = det_M
        self.class_indices = class_indices.copy()
        self.transition_indices = transition_indices.copy()


def _positive_abs(x: Int) -> Int:
    if x < 0:
        return -x
    return x


def _int_gcd(x: Int, y: Int) -> Int:
    var a = _positive_abs(x)
    var b = _positive_abs(y)
    while b != 0:
        var r = a % b
        a = b
        b = r
    return a


def _three_column_det(P: List[List[Int]], a: Int, b: Int, c: Int) raises -> Int:
    var aa: List[Int] = [P[0][a], P[1][a], P[2][a]]
    var bb: List[Int] = [P[0][b], P[1][b], P[2][b]]
    var cc: List[Int] = [P[0][c], P[1][c], P[2][c]]
    return _rank_det(aa, bb, cc)


def _phase_index(P: List[List[Int]], ids: List[Int]) raises -> Int:
    if len(ids) < 3:
        raise Error("phase has fewer than three states")
    var g = 0
    for a in range(len(ids)):
        for b in range(a + 1, len(ids)):
            for c in range(b + 1, len(ids)):
                var minor = _three_column_det(P, ids[a], ids[b], ids[c])
                g = _int_gcd(g, minor)
    if g == 0:
        raise Error("phase has rational Parikh rank below three")
    return g


def audit_phase_lattice_index(
    M: List[List[Int]],
    P: List[List[Int]],
    N: List[List[Int]],
    phases: List[Int],
    period: Int,
) raises -> PhaseLatticeIndex:
    """Exact bounded necessary conditions, not a word/spectrum constructor.

    At most 18 states and period <= 4; entries <= 64 and |det M| <=16.
    These caps keep every 3x3 minor and index product within machine Int.
    """
    var r = len(phases)
    if period < 1 or period > 4 or r < 3 * period or r > 18:
        raise Error("invalid phase period or bounded state count")
    if len(M) != 3 or len(P) != 3 or len(N) != r:
        raise Error("bad integer incidence / Parikh dimensions")
    for a in range(3):
        if len(M[a]) != 3 or len(P[a]) != r:
            raise Error("bad ternary matrix row")
        for b in range(3):
            if M[a][b] < 0 or M[a][b] > 64:
                raise Error("incidence entry outside bounded budget")
        for j in range(r):
            if P[a][j] < 0 or P[a][j] > 64:
                raise Error("Parikh entry outside bounded budget")
    for i in range(r):
        if len(N[i]) != r:
            raise Error("child-matrix row length mismatch")
        if phases[i] < 0 or phases[i] >= period:
            raise Error("cyclic class label out of range")
        for j in range(r):
            if N[i][j] < 0 or N[i][j] > 64:
                raise Error("child count outside bounded budget")

    var a0: List[Int] = [M[0][0], M[1][0], M[2][0]]
    var a1: List[Int] = [M[0][1], M[1][1], M[2][1]]
    var a2: List[Int] = [M[0][2], M[1][2], M[2][2]]
    var determinant = _rank_det(a0, a1, a2)
    var absdet = _positive_abs(determinant)
    if absdet == 0 or absdet > 16:
        raise Error("singular or over-budget incidence determinant")

    # Verify PN=MP by ALL actual integer columns, not a few sampled rows.
    for j in range(r):
        var has_mass = False
        var children = 0
        for a in range(3):
            if P[a][j] > 0:
                has_mass = True
            var lhs = 0
            var rhs = 0
            for i in range(r):
                lhs += P[a][i] * N[i][j]
            for i in range(3):
                rhs += M[a][i] * P[i][j]
            if lhs != rhs:
                raise Error("exact P N = M P identity fails")
        if not has_mass:
            raise Error("zero-mass state is invalid")
        for i in range(r):
            if N[i][j] > 0:
                children += N[i][j]
                if phases[i] != (phases[j] + 1) % period:
                    raise Error("child leaves the asserted cyclic phase")
        if children == 0:
            raise Error("missing complete child row")

    var classes = List[List[Int]]()
    var indices = List[Int]()
    for k in range(period):
        var ids = List[Int]()
        for j in range(r):
            if phases[j] == k:
                ids.append(j)
        var idx = _phase_index(P, ids)
        classes.append(ids.copy())
        indices.append(idx)

    var transitions = List[Int]()
    var product = 1
    for k in range(period):
        var next = (k + 1) % period
        var numerator = absdet * indices[k]
        if numerator % indices[next] != 0:
            raise Error("nonintegral phase-lattice transition index")
        var t = numerator // indices[next]
        if t <= 0:
            raise Error("nonpositive phase transition")
        var residual = t
        var shared = _int_gcd(residual, absdet)
        while shared > 1:
            residual //= shared
            shared = _int_gcd(residual, absdet)
        if residual != 1:
            raise Error("transition index has unexpected prime support")
        transitions.append(t)
        product *= t

    var expected_product = 1
    for _ in range(period):
        expected_product *= absdet
    if product != expected_product:
        raise Error("cyclic index determinant budget violated")

    if absdet == 1:
        for k in range(period):
            if indices[k] != indices[0] or transitions[k] != 1:
                raise Error("unimodular phase lattice leakage")

    # Equality case |C|=3h: every one-step phase transition MUST be
    # nonsingular, with |det block| equal to the exact lattice index.
    if r == 3 * period:
        var signed_product = 1
        for k in range(period):
            var src = classes[k]
            var dst = classes[(k + 1) % period]
            var block = List[List[Int]]()
            for i in range(3):
                var row = List[Int]()
                for j in range(3):
                    row.append(N[dst[i]][src[j]])
                block.append(row)
            var c0: List[Int] = [block[0][0],block[1][0],block[2][0]]
            var c1: List[Int] = [block[0][1],block[1][1],block[2][1]]
            var c2: List[Int] = [block[0][2],block[1][2],block[2][2]]
            var detA = _rank_det(c0, c1, c2)
            if detA == 0 or _positive_abs(detA) != transitions[k]:
                raise Error("equality-size phase child block determinant invalid")
            signed_product *= detA
        var expected_signed = 1
        for _ in range(period):
            expected_signed *= determinant
        if signed_product != expected_signed:
            raise Error("one-step signed determinant product invalid")

    return PhaseLatticeIndex(determinant, indices, transitions)
