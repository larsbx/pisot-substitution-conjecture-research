"""Bounded EXACT integer necessary-condition audit for Pisot periodic SCC phases.

For a SUPPLIED complete strictly child-closed balanced-pair SCC, the
integral Parikh intertwiner P N = M P and primitive irreducible cubic
Pisot incidence imply that every cyclic class of N has rank 3.

This validator checks only the algebraic premise/conclusion for a given
finite matrix packet and phase labelling. It does NOT construct a genuine
word-derived SCC, verify graph irreducibility, or establish a Pisot spectrum.
The theorem is in docs/c4-periodic-parikh-phase-rigidity-2026-11-04.md.
"""
from psc.c4_two_generation_rank import _rank_det


def audit_periodic_parikh_phase_rank(
    M: List[List[Int]],
    P: List[List[Int]],
    N: List[List[Int]],
    phases: List[Int],
    period: Int,
) raises -> List[Int]:
    """Fail closed on bad dimensions, missing mass/child, PN!=MP,
    incorrect phase edges, or a rational rank-deficient cyclic class.

    A caller must *separately* certify M is ternary irreducible Pisot,
    N is the entire literal strict child matrix, and phase labels are
    the actual periodic classes of its irreducible occurrence graph.
    Integer entries <=1000, at most 30 states; safe 64-bit minors.
    """
    var r = len(phases)
    if period < 1 or period > 8 or r < 3 * period or r > 30:
        raise Error("invalid periodic class size/period budget")
    if len(M) != 3 or len(P) != 3 or len(N) != r:
        raise Error("invalid 3-letter or child matrix shape")
    for i in range(3):
        if len(M[i]) != 3 or len(P[i]) != r:
            raise Error("invalid incidence/Parikh row")
        for j in range(3):
            if M[i][j] < 0 or M[i][j] > 1000:
                raise Error("incidence coordinate budget")
        for j in range(r):
            if P[i][j] < 0 or P[i][j] > 1000:
                raise Error("Parikh coordinate budget")
    for i in range(r):
        if len(N[i]) != r:
            raise Error("invalid child row length")
        if phases[i] < 0 or phases[i] >= period:
            raise Error("invalid cyclic class label")
        for j in range(r):
            if N[i][j] < 0 or N[i][j] > 1000:
                raise Error("invalid child multiplicity")
    for j in range(r):
        var nonempty_mass = 0
        var children = 0
        for a in range(3):
            nonempty_mass += P[a][j]
            var lhs = 0
            var rhs = 0
            for i in range(r):
                lhs += P[a][i] * N[i][j]
            for i in range(3):
                rhs += M[a][i] * P[i][j]
            if lhs != rhs:
                raise Error("exact Parikh intertwiner P N = M P fails")
        if nonempty_mass == 0:
            raise Error("empty balanced state mass")
        for i in range(r):
            if N[i][j] > 0:
                children += N[i][j]
                if phases[i] != (phases[j] + 1) % period:
                    raise Error("child violates supplied phase transition")
        if children == 0:
            raise Error("missing outgoing complete children")

    var sizes = List[Int]()
    for k in range(period):
        var ids = List[Int]()
        for i in range(r):
            if phases[i] == k:
                ids.append(i)
        if len(ids) < 3:
            raise Error("period class has fewer than three Parikh states")
        var rank_three = False
        for ai in range(len(ids)):
            for bi in range(ai + 1, len(ids)):
                for ci in range(bi + 1, len(ids)):
                    var a: List[Int] = [
                        P[0][ids[ai]], P[1][ids[ai]], P[2][ids[ai]],
                    ]
                    var b: List[Int] = [
                        P[0][ids[bi]], P[1][ids[bi]], P[2][ids[bi]],
                    ]
                    var c: List[Int] = [
                        P[0][ids[ci]], P[1][ids[ci]], P[2][ids[ci]],
                    ]
                    if _rank_det(a, b, c) != 0:
                        rank_three = True
        if not rank_three:
            raise Error("period class has rational Parikh rank less than three")
        sizes.append(len(ids))
    return sizes^
