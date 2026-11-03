"""Literal two-generation Parikh rank witnesses for a balanced word pair.

If the ternary incidence characteristic polynomial is Q-irreducible, every
nonempty balanced pair has three independent *actual* irreducible descendant
Parikh columns among its own factor words at depths 0, 1 and 2.
This module searches and records a concrete witness; it does not decide
irreducibility, construct a strict SCC, or prove C4/G1/PSC.

Uses only actual ordered zero-return factorization, retaining both child
ordinals. No invented target/quotient edges or first-child-only shortcut.
"""

from psc.bpa import apply_substitution, decompose
from psc.words import ALPHABET, Pair, is_balanced, parikh
from substitution_dynamics.substitution import validate_word
from psc.c4_cut_alignment import _det3


struct LiteralParikhOccurrence(Copyable, Movable):
    var depth: Int
    var first_ordinal: Int
    var second_ordinal: Int
    var counts: List[Int]

    def __init__(
        out self, depth: Int, first_ordinal: Int,
        second_ordinal: Int, counts: List[Int],
    ):
        self.depth = depth
        self.first_ordinal = first_ordinal
        self.second_ordinal = second_ordinal
        self.counts = counts.copy()


struct TwoGenerationRank(Copyable, Movable):
    var rank: Int
    var occurrences: List[LiteralParikhOccurrence]
    var independent_ids: List[Int]

    def __init__(
        out self, rank: Int, occurrences: List[LiteralParikhOccurrence],
        independent_ids: List[Int],
    ):
        self.rank = rank
        self.occurrences = occurrences.copy()
        self.independent_ids = independent_ids.copy()


def _cross_nonzero(x: List[Int], y: List[Int]) raises -> Bool:
    if len(x) != 3 or len(y) != 3:
        raise Error("rank test requires ternary Parikh vectors")
    return (
        x[1] * y[2] != x[2] * y[1]
        or x[2] * y[0] != x[0] * y[2]
        or x[0] * y[1] != x[1] * y[0]
    )


def _rank_det(a: List[Int], b: List[Int], c: List[Int]) raises -> Int:
    if len(a) != 3 or len(b) != 3 or len(c) != 3:
        raise Error("rank determinant requires three ternary columns")
    var matrix: List[Int] = [
        a[0], b[0], c[0],
        a[1], b[1], c[1],
        a[2], b[2], c[2],
    ]
    return _det3(matrix)


def _add(
    mut records: List[LiteralParikhOccurrence],
    mut pivots: List[Int],
    depth: Int, i: Int, j: Int, p: List[Int],
    node_cap: Int,
) raises:
    if len(records) >= node_cap:
        raise Error("two-generation rank enumeration exceeded node cap")
    if len(p) != 3:
        raise Error("unexpected Parikh dimension")
    var index = len(records)
    records.append(LiteralParikhOccurrence(depth, i, j, p))
    if len(pivots) == 0:
        if p[0] != 0 or p[1] != 0 or p[2] != 0:
            pivots.append(index)
    elif len(pivots) == 1:
        if _cross_nonzero(records[pivots[0]].counts, p):
            pivots.append(index)
    elif len(pivots) == 2:
        if _rank_det(
            records[pivots[0]].counts, records[pivots[1]].counts, p
        ) != 0:
            pivots.append(index)


def literal_two_generation_parikh_rank(
    sigma: List[List[Int]], seed: Pair, node_cap: Int = 10000,
) raises -> TwoGenerationRank:
    """Exhaust the literal depth-0/1/2 balanced child forest.

    The result is a *bounded exact certificate* or a bounded negative
    observation, never a universal verdict. Source words <=256,
    image lengths <=16; all intermediate inflation words <=65536
    symbols. Each coordinate is <=65536, so the greedy 3x3 minor
    is safe in signed 64-bit machine Int independently of node_cap.
    The mathematical rank theorem has no such length restrictions.
    """
    if len(sigma) != 3 or node_cap < 1:
        raise Error("invalid alphabet or node cap")
    for a in range(3):
        if len(sigma[a]) == 0 or len(sigma[a]) > 16:
            raise Error("substitution image outside safe rank budget")
        for k in range(len(sigma[a])):
            if sigma[a][k] < 0 or sigma[a][k] >= 3:
                raise Error("substitution letter outside alphabet")
    if seed.length() <= 0 or seed.length() > 256 or len(seed.u) != len(seed.v):
        raise Error("rank source lengths must be equal and within cap")
    validate_word(seed.u, ALPHABET)
    validate_word(seed.v, ALPHABET)
    if not is_balanced(seed):
        raise Error("rank source must be a nonempty balanced pair within cap")

    var records = List[LiteralParikhOccurrence]()
    var pivots = List[Int]()
    _add(records, pivots, 0, -1, -1, parikh(seed.u), node_cap)

    var first = decompose(
        apply_substitution(sigma, seed.u),
        apply_substitution(sigma, seed.v),
    )
    for i in range(len(first)):
        _add(records, pivots, 1, i, -1, parikh(first[i].u), node_cap)
    # Retain *each* first child and all its actual second-generation
    # descendants, including coincidence blocks and repeat occurrences.
    for i in range(len(first)):
        var parent = first[i].copy()
        var second = decompose(
            apply_substitution(sigma, parent.u),
            apply_substitution(sigma, parent.v),
        )
        for j in range(len(second)):
            _add(records, pivots, 2, i, j, parikh(second[j].u), node_cap)
    return TwoGenerationRank(len(pivots), records, pivots)
