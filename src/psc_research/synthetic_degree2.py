"""A near-realizable three-state degree-2 obstruction template.

This module deliberately constructs an abstract signed derived substitution that
passes the current linear-algebra, orientation, endpoint-signature, and
per-state balanced-word tests for the Tribonacci cubic.  It then exposes the
missing constraint: no ordering of the actual substitution images with that
incidence matrix realizes two nonsynchronizing endpoint maps.

The object is a falsification artifact for proof strategies, not a PSC
counterexample.
"""

from __future__ import annotations

from itertools import permutations

from .bpa import State, Substitution, endpoint_maps, normalize_state, parikh
from .defect_intertwiner import exterior_square, k2_wedge
from .endpoint_core import class_of, synchronizes
from .intertwiner import IntMatrix, matmul, substitution_incidence


N: IntMatrix = (
    (1, 1, 1),
    (1, 0, 0),
    (0, 1, 0),
)

S: IntMatrix = (
    (-1, -1, -1),
    (1, 0, 0),
    (0, -1, 0),
)

A: IntMatrix = (
    (0, 0, 0),
    (1, 0, 0),
    (0, 0, 0),
)

B: IntMatrix = (
    (1, 1, 1),
    (0, 0, 0),
    (0, 1, 0),
)

P: IntMatrix = (
    (3, 3, 2),
    (2, 1, 1),
    (1, 1, 0),
)

Q: IntMatrix = (
    (2, 2, 2),
    (-2, 2, 0),
    (-2, 0, 0),
)

STATES: tuple[State, ...] = (
    ((1, 3, 1, 2, 1, 2), (2, 1, 1, 1, 2, 3)),
    ((1, 1, 2, 1, 3), (2, 1, 3, 1, 1)),
    ((1, 1, 2), (2, 1, 1)),
)

# Ordered signed child words for the abstract derived substitution.
# Each pair is (child_index, orientation_sign).
SIGNED_CHILDREN: tuple[tuple[tuple[int, int], ...], ...] = (
    ((0, -1), (1, 1)),
    ((0, -1), (2, -1)),
    ((0, -1),),
)

# Zero-based endpoint maps used only by the abstract template.
PLUS_F = (1, 0, 0)
MINUS_G = (1, 2, 0)


def _add(a: IntMatrix, b: IntMatrix) -> IntMatrix:
    return tuple(tuple(x + y for x, y in zip(ra, rb)) for ra, rb in zip(a, b))


def _sub(a: IntMatrix, b: IntMatrix) -> IntMatrix:
    return tuple(tuple(x - y for x, y in zip(ra, rb)) for ra, rb in zip(a, b))


def _scale2(a: IntMatrix) -> IntMatrix:
    return tuple(tuple(2 * x for x in row) for row in a)


def _columns(matrix: IntMatrix) -> tuple[tuple[int, ...], ...]:
    return tuple(tuple(matrix[i][j] for i in range(len(matrix))) for j in range(len(matrix[0])))


def state_parikh_matrix() -> IntMatrix:
    cols = tuple(parikh(state[0], 3) for state in STATES)
    return tuple(tuple(col[i] for col in cols) for i in range(3))


def state_k2_matrix() -> IntMatrix:
    cols = tuple(k2_wedge(state) for state in STATES)
    return tuple(tuple(col[i] for col in cols) for i in range(3))


def states_are_irreducible() -> bool:
    """No state has a proper balanced prefix cut."""
    for u, v in STATES:
        for k in range(1, len(u)):
            if parikh(u[:k], 3) == parikh(v[:k], 3):
                return False
    return True


def signed_counts_from_words() -> tuple[IntMatrix, IntMatrix]:
    positive = [[0] * 3 for _ in range(3)]
    negative = [[0] * 3 for _ in range(3)]
    for parent, word in enumerate(SIGNED_CHILDREN):
        for child, sign in word:
            if sign == 1:
                positive[child][parent] += 1
            else:
                negative[child][parent] += 1
    return (
        tuple(tuple(row) for row in positive),
        tuple(tuple(row) for row in negative),
    )


def abstract_endpoint_constraints_hold() -> bool:
    """The F/G endpoint quotient phases fit the synthetic child selectors."""
    # first-letter pairs are all {0,1}; F keeps that unordered pair off-diagonal
    plus_pairs = tuple((state[0][0] - 1, state[1][0] - 1) for state in STATES)
    if any(synchronizes(PLUS_F, a, b) for a, b in plus_pairs):
        return False
    if len({frozenset(pair) for pair in plus_pairs}) != 1:
        return False

    minus_pairs = tuple((state[0][-1] - 1, state[1][-1] - 1) for state in STATES)
    if any(synchronizes(MINUS_G, a, b) for a, b in minus_pairs):
        return False

    first_child = tuple(word[0][0] for word in SIGNED_CHILDREN)
    last_child = tuple(word[-1][0] for word in SIGNED_CHILDREN)

    for parent in range(3):
        a, b = plus_pairs[parent]
        target_pair = frozenset((PLUS_F[a], PLUS_F[b]))
        if target_pair != frozenset(plus_pairs[first_child[parent]]):
            return False

        a, b = minus_pairs[parent]
        target_pair = frozenset((MINUS_G[a], MINUS_G[b]))
        if target_pair != frozenset(minus_pairs[last_child[parent]]):
            return False
    return True


def tribonacci_incidence_variants() -> tuple[Substitution, ...]:
    """All word orderings with incidence N.

    Column 1 has letters {1,2}, column 2 has {1,3}, and column 3 is the
    singleton letter 1, so there are exactly four substitutions.
    """
    out: list[Substitution] = []
    for image1 in permutations((1, 2)):
        for image2 in permutations((1, 3)):
            sigma: Substitution = {1: tuple(image1), 2: tuple(image2), 3: (1,)}
            if substitution_incidence(sigma) != N:
                raise AssertionError("incidence variant does not recover N")
            out.append(sigma)
    return tuple(out)


def endpoint_type_pair(sigma: Substitution) -> tuple[tuple[int, ...], tuple[int, ...]]:
    plus, minus = endpoint_maps(sigma)
    plus0 = tuple(plus[a] - 1 for a in sorted(plus))
    minus0 = tuple(minus[a] - 1 for a in sorted(minus))
    return class_of(plus0).representative, class_of(minus0).representative


def every_incidence_variant_has_global_endpoint_sync() -> bool:
    for sigma in tribonacci_incidence_variants():
        plus, minus = endpoint_type_pair(sigma)
        if not (class_of(plus).globally_synchronizing or class_of(minus).globally_synchronizing):
            return False
    return True


def verify_synthetic_template() -> bool:
    """Check every algebraic/per-state constraint claimed by this artifact."""
    if _add(A, B) != N or _sub(A, B) != S:
        return False
    pos, neg = signed_counts_from_words()
    if pos != A or neg != B:
        return False
    if state_parikh_matrix() != P or state_k2_matrix() != Q:
        return False
    if not states_are_irreducible():
        return False
    if matmul(P, N) != matmul(N, P):
        return False
    if matmul(Q, S) != matmul(exterior_square(N), Q):
        return False
    if not abstract_endpoint_constraints_hold():
        return False
    return every_incidence_variant_has_global_endpoint_sync()
