"""Exact finite-map classification for the C4 endpoint-core program.

The boundary synchronization mechanism depends only on the endpoint maps
``sigma_+`` and ``sigma_-``.  For a three-letter alphabet each endpoint map is
one of only ``3^3 = 27`` functions.  This module classifies those functions up
to alphabet relabeling and computes the recurrent off-diagonal core of the
product map ``h x h``.

A pair ``(a,b)`` is synchronizing when the two forward orbits eventually meet.
A recurrent nonsynchronizing pair is an off-diagonal periodic point of
``h x h``.  These finite cores are the obstruction templates used by C4; the
module proves no Pisot-specific existence or exclusion theorem by itself.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations, product
from typing import Iterable, Iterator, Sequence

FiniteMap = tuple[int, ...]
Pair = tuple[int, int]


@dataclass(frozen=True)
class EndpointMapClass:
    """One conjugacy class of finite maps under alphabet relabeling."""

    representative: FiniteMap
    members: tuple[FiniteMap, ...]
    nonsynchronizing_pairs: tuple[Pair, ...]
    recurrent_core: tuple[Pair, ...]

    @property
    def size(self) -> int:
        return len(self.members)

    @property
    def globally_synchronizing(self) -> bool:
        return not self.nonsynchronizing_pairs


def validate_map(h: Sequence[int]) -> FiniteMap:
    """Return ``h`` as a tuple after checking ``h:{0,...,n-1}->{0,...,n-1}``."""
    out = tuple(h)
    n = len(out)
    if n == 0:
        raise ValueError("finite map must have a nonempty domain")
    if any(x < 0 or x >= n for x in out):
        raise ValueError(f"map values must lie in 0..{n - 1}")
    return out


def all_maps(size: int = 3) -> Iterator[FiniteMap]:
    """Enumerate every self-map of ``size`` letters in lexicographic order."""
    if size < 1:
        raise ValueError("size must be positive")
    yield from product(range(size), repeat=size)


def conjugate(h: Sequence[int], permutation: Sequence[int]) -> FiniteMap:
    """Return ``p o h o p^{-1}`` for a permutation ``p`` of the alphabet."""
    h = validate_map(h)
    p = tuple(permutation)
    n = len(h)
    if tuple(sorted(p)) != tuple(range(n)):
        raise ValueError("permutation must contain every alphabet element once")
    inverse = [0] * n
    for old, new in enumerate(p):
        inverse[new] = old
    return tuple(p[h[inverse[x]]] for x in range(n))


def conjugacy_orbit(h: Sequence[int]) -> tuple[FiniteMap, ...]:
    """All relabelings of ``h``, sorted and deduplicated."""
    h = validate_map(h)
    return tuple(sorted({conjugate(h, p) for p in permutations(range(len(h))) }))


def canonical_map(h: Sequence[int]) -> FiniteMap:
    """Lexicographically least conjugate of ``h``."""
    return conjugacy_orbit(h)[0]


def synchronizes(h: Sequence[int], a: int, b: int) -> bool:
    """Whether the two forward orbits of ``a`` and ``b`` ever meet.

    The decision is exact: iterate the product map until reaching the diagonal
    or repeating an ordered pair.  Repetition off the diagonal proves that the
    two deterministic forward orbits will never meet.
    """
    h = validate_map(h)
    n = len(h)
    if not (0 <= a < n and 0 <= b < n):
        raise ValueError("pair lies outside the map domain")
    seen: set[Pair] = set()
    x, y = a, b
    while x != y:
        pair = (x, y)
        if pair in seen:
            return False
        seen.add(pair)
        x, y = h[x], h[y]
    return True


def nonsynchronizing_pairs(h: Sequence[int]) -> tuple[Pair, ...]:
    """All ordered distinct pairs whose forward orbits never coalesce."""
    h = validate_map(h)
    n = len(h)
    return tuple(
        (a, b)
        for a in range(n)
        for b in range(n)
        if a != b and not synchronizes(h, a, b)
    )


def is_recurrent_pair(h: Sequence[int], pair: Pair) -> bool:
    """Whether ``pair`` is periodic under ``h x h`` and stays off diagonal."""
    h = validate_map(h)
    a, b = pair
    if a == b or synchronizes(h, a, b):
        return False
    start = (a, b)
    x, y = h[a], h[b]
    while (x, y) != start:
        # A deterministic finite orbit that repeats somewhere other than the
        # start has entered a cycle not containing the start, so the start is
        # transient rather than recurrent.
        if x == y:
            return False
        x, y = h[x], h[y]
        # At most n^2 product states exist.  The synchronizes check above has
        # already established an off-diagonal eventual cycle, so termination
        # is guaranteed.
        if (x, y) == start:
            break
    return True


def recurrent_nonsynchronizing_core(h: Sequence[int]) -> tuple[Pair, ...]:
    """Periodic off-diagonal points of the product map ``h x h``."""
    h = validate_map(h)
    return tuple(pair for pair in nonsynchronizing_pairs(h) if is_recurrent_pair(h, pair))


def classify_maps(size: int = 3) -> tuple[EndpointMapClass, ...]:
    """Classify all self-maps of ``size`` letters up to conjugacy."""
    groups: dict[FiniteMap, list[FiniteMap]] = {}
    for h in all_maps(size):
        groups.setdefault(canonical_map(h), []).append(h)

    out: list[EndpointMapClass] = []
    for representative in sorted(groups):
        members = tuple(sorted(groups[representative]))
        out.append(
            EndpointMapClass(
                representative=representative,
                members=members,
                nonsynchronizing_pairs=nonsynchronizing_pairs(representative),
                recurrent_core=recurrent_nonsynchronizing_core(representative),
            )
        )
    return tuple(out)


def class_of(h: Sequence[int]) -> EndpointMapClass:
    """Return the conjugacy class descriptor containing ``h``."""
    h = validate_map(h)
    representative = canonical_map(h)
    members = conjugacy_orbit(h)
    return EndpointMapClass(
        representative=representative,
        members=members,
        nonsynchronizing_pairs=nonsynchronizing_pairs(representative),
        recurrent_core=recurrent_nonsynchronizing_core(representative),
    )


def functional_cycle_lengths(h: Sequence[int]) -> tuple[int, ...]:
    """Sorted cycle lengths of the functional graph of ``h``.

    This is a readable invariant for reports.  It is not used as the canonical
    classifier because distinct rooted-tree attachments can share cycle data.
    """
    h = validate_map(h)
    n = len(h)
    cycle_nodes: set[int] = set()
    lengths: list[int] = []
    globally_seen: set[int] = set()

    for start in range(n):
        if start in globally_seen:
            continue
        path: list[int] = []
        position: dict[int, int] = {}
        x = start
        while x not in position and x not in globally_seen:
            position[x] = len(path)
            path.append(x)
            x = h[x]
        globally_seen.update(path)
        if x in position:
            cycle = path[position[x] :]
            cycle_nodes.update(cycle)
            lengths.append(len(cycle))
    return tuple(sorted(lengths))
