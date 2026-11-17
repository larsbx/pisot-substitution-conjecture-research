"""Exact one-track seam correction for a literal overlap component.

The overlap graph keeps spatially ordered occurrences. Adjacent cell types
are born inside a row or inherited across the last/first boundary of a
previous adjacent pair. Rotation periods of these seams and of the two
endpoint maps give the cyclotomic correction without a common-period scan.
"""

from finite_exact.checked_int import checked_add, checked_mul
from finite_exact.rat_q import Q
from finite_linear_algebra.faddeev_leverrier import charpoly
from finite_linear_algebra.qpoly import divide
from psc.exact import q_int, q_poly
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables, cached_sign
from psc.periodic_overlap_returns import PeriodicOverlapGraph
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_sub_checked


comptime TOP = 1
comptime BOTTOM = 2
comptime BOTH = TOP | BOTTOM


struct CellBoundaryMasks(Copyable, Movable):
    var left: List[Int]
    var right: List[Int]

    def __init__(out self, var left: List[Int], var right: List[Int]):
        self.left = left^
        self.right = right^


def overlap_boundary_masks(
    tables: SeedOverlapTables, states: List[OverlapState],
) raises -> CellBoundaryMasks:
    """Track ownership of the later start and the earlier end."""
    var cache = Dict[CubicElt, Int]()
    var left = List[Int]()
    var right = List[Int]()
    for state in states:
        var start_order = cached_sign(tables, cache, state.shift)
        left.append(TOP if start_order < 0 else BOTTOM if start_order > 0 else BOTH)
        var bottom_end = cubic_add_checked(state.shift, tables.lengths.at(state.bottom))
        var end_order = cached_sign(tables, cache, cubic_sub_checked(bottom_end, tables.lengths.at(state.top)))
        right.append(TOP if end_order > 0 else BOTTOM if end_order < 0 else BOTH)
    return CellBoundaryMasks(left^, right^)


struct AdjacentCellOccurrence(ImplicitlyCopyable, Copyable, Movable):
    var left: Int
    var right: Int
    # Birth: source row and ordinal. Inheritance: previous adjacent-pair index.
    var source: Int
    var ordinal: Int
    var previous: Int

    def __init__(out self, left: Int, right: Int, source: Int, ordinal: Int, previous: Int):
        self.left = left
        self.right = right
        self.source = source
        self.ordinal = ordinal
        self.previous = previous


struct SeamCycleProfile(Copyable, Movable):
    var first: List[Int]
    var last: List[Int]
    var seam: List[Int]
    var occurrences: List[AdjacentCellOccurrence]

    def __init__(
        out self, var first: List[Int], var last: List[Int], var seam: List[Int],
        var occurrences: List[AdjacentCellOccurrence],
    ):
        self.first = first^
        self.last = last^
        self.seam = seam^
        self.occurrences = occurrences^

    def cyclotomic_correction(self, order: Int) raises -> Int:
        """Additive multiplicity correction at each primitive root of order d."""
        if order <= 0:
            raise Error("one-track seams: cyclotomic order must be positive")
        var multiplicity = 0
        for length in self.seam:
            multiplicity += Int(length % order == 0)
        for length in self.first:
            multiplicity -= Int(length % order == 0)
        for length in self.last:
            multiplicity -= Int(length % order == 0)
        return multiplicity

    def fixed_counts(self, power: Int) raises -> List[Int]:
        """Top-only first endpoint, last endpoint and adjacent seam counts."""
        if power <= 0:
            raise Error("one-track seams: power must be positive")
        return [_fixed_count(self.first, power), _fixed_count(self.last, power), _fixed_count(self.seam, power)]


def _fixed_count(lengths: List[Int], power: Int) -> Int:
    var count = 0
    for length in lengths:
        if power % length == 0:
            count += length
    return count


def _cycle_lengths(next: List[Int]) -> List[Int]:
    # Positive marks are positions in the current walk plus one.
    # Negative marks belong to settled walks. -1 is also the exit sentinel.
    var mark = List[Int](length=len(next), fill=0)
    var lengths = List[Int]()
    for root in range(len(next)):
        if mark[root] != 0:
            continue
        var path = List[Int]()
        var v = root
        while v >= 0 and mark[v] == 0:
            path.append(v)
            mark[v] = len(path)
            v = next[v]
        if v >= 0 and mark[v] > 0:
            lengths.append(len(path) - mark[v] + 1)
        for u in path:
            mark[u] = -1
    return lengths^


def _intern(
    occurrence: AdjacentCellOccurrence, size: Int, max_seams: Int,
    mut index: Dict[Int, Int], mut occurrences: List[AdjacentCellOccurrence],
) raises -> Int:
    var key = checked_add(checked_mul(occurrence.left, size), occurrence.right)
    if key not in index:
        if len(occurrences) >= max_seams:
            raise Error("one-track seams: adjacency cap reached; inconclusive")
        index[key] = len(occurrences)
        occurrences.append(occurrence)
    return index[key]


def one_track_seam_cycles(
    rows: List[List[Int]], masks: CellBoundaryMasks, max_seams: Int = 100000,
) raises -> SeamCycleProfile:
    """Close the top-track-only boundary types under literal subdivision.

    Child multiplicity is preserved in rows. Legal adjacent pair types
    are deduplicated. A seam becoming shared leaves the one-track map
    permanently. Empty rows may stand for terminal shared coincidences.
    """
    var size = len(rows)
    if max_seams <= 0:
        raise Error("one-track seams: adjacency cap must be positive")
    if len(masks.left) != size or len(masks.right) != size:
        raise Error("one-track seams: boundary masks disagree with alphabet size")
    for v in range(size):
        if masks.left[v] < TOP or masks.left[v] > BOTH or masks.right[v] < TOP or masks.right[v] > BOTH:
            raise Error("one-track seams: invalid track mask")

    var first = List[Int](length=size, fill=-1)
    var last = List[Int](length=size, fill=-1)
    var occurrences = List[AdjacentCellOccurrence]()
    var index = Dict[Int, Int]()
    for source in range(size):
        ref row = rows[source]
        if len(row) == 0:
            if masks.left[source] != BOTH or masks.right[source] != BOTH:
                raise Error("one-track seams: missing row for a one-track cell")
            continue
        for v in row:
            if v < 0 or v >= size:
                raise Error("one-track seams: child outside cell alphabet")
        var a = row[0]
        var b = row[len(row) - 1]
        if (masks.left[a] & masks.left[source]) != masks.left[source] or (
            masks.right[b] & masks.right[source]
        ) != masks.right[source]:
            raise Error("one-track seams: inflation lost an existing track boundary")
        if masks.left[source] == TOP and masks.left[a] == TOP:
            first[source] = a
        if masks.right[source] == TOP and masks.right[b] == TOP:
            last[source] = b

        for k in range(len(row) - 1):
            var u = row[k]
            var v = row[k + 1]
            if masks.right[u] != masks.left[v]:
                raise Error("one-track seams: adjacent cells disagree about their common boundary")
            if masks.right[u] == TOP:
                _ = _intern(AdjacentCellOccurrence(u, v, source, k, -1), size, max_seams, index, occurrences)

    var next = List[Int]()
    var head = 0
    while head < len(occurrences):
        var pair = occurrences[head]
        var u = last[pair.left]
        var v = first[pair.right]
        if (u < 0) != (v < 0):
            raise Error("one-track seams: two cells disagree about the inherited boundary")
        var successor = -1
        if u >= 0:
            successor = _intern(AdjacentCellOccurrence(u, v, -1, -1, head), size, max_seams, index, occurrences)
        next.append(successor)
        head += 1

    return SeamCycleProfile(_cycle_lengths(first), _cycle_lengths(last), _cycle_lengths(next), occurrences^)


struct UnitMultiplicities(ImplicitlyCopyable, Copyable, Movable):
    var plus: Int
    var minus: Int

    def __init__(out self, plus: Int, minus: Int):
        self.plus = plus
        self.minus = minus


def _require_coefficients(coeffs: List[Q]) raises:
    for c in coeffs:
        if c.rejected:
            raise Error("one-track seams: exact characteristic polynomial arithmetic was rejected")


def _linear_factor_order(poly: List[Q], sign: Int) raises -> Int:
    var p = poly.copy()
    var divisor = q_poly([-sign, 1])
    var order = 0
    while len(p) > 1:
        var result = divide(p, divisor)
        if result.rejected:
            raise Error("one-track seams: exact linear factor division was rejected")
        _require_coefficients(result.quotient)
        _require_coefficients(result.remainder)
        if len(result.remainder) != 0:
            break
        p = result.quotient.copy()
        order += 1
    return order


def odd_unit_multiplicities(
    rows: List[List[Int]], swap: List[Int], max_dimension: Int = 48,
) raises -> UnitMultiplicities:
    """Algebraic multiplicities at +1 and -1 on the swap-odd sector.

    Parent columns use one signed basis vector per swap orbit. Every
    occurrence is included, even if another occurrence has the same head.
    """
    var size = len(rows)
    if max_dimension <= 0 or size // 2 > max_dimension:
        raise Error("one-track seams: odd matrix dimension cap reached; inconclusive")
    if len(swap) != size:
        raise Error("one-track seams: swap disagrees with alphabet size")
    var orbit = List[Int](length=size, fill=-1)
    var representatives = List[Int]()
    for s in range(size):
        var t = swap[s]
        if t < 0 or t >= size or t == s or swap[t] != s:
            raise Error("one-track seams: cell swap must be a free involution")
        if s < t:
            orbit[s] = len(representatives)
            orbit[t] = orbit[s]
            representatives.append(s)
    var dimension = len(representatives)
    var matrix = List[List[Q]]()
    for _ in range(dimension):
        var row = List[Q]()
        for _ in range(dimension):
            row.append(Q.zero())
        matrix.append(row^)
    for j in range(dimension):
        var s = representatives[j]
        ref row = rows[s]
        ref mate = rows[swap[s]]
        if len(row) == 0 or len(row) != len(mate):
            raise Error("one-track seams: swapped rows are not complete")
        for k in range(len(row)):
            var v = row[k]
            if v < 0 or v >= size or swap[v] != mate[k]:
                raise Error("one-track seams: swap does not preserve child occurrences")
            var i = orbit[v]
            matrix[i][j] = matrix[i][j].add(q_int(1 if v < swap[v] else -1))
    var poly = charpoly(matrix)
    _require_coefficients(poly)
    return UnitMultiplicities(_linear_factor_order(poly, 1), _linear_factor_order(poly, -1))


struct NeutralSinkSpectrum(Copyable, Movable):
    var overlap: UnitMultiplicities
    var correction: UnitMultiplicities
    var bigon: UnitMultiplicities
    var seams: SeamCycleProfile

    def __init__(out self, overlap: UnitMultiplicities, var seams: SeamCycleProfile) raises:
        self.overlap = overlap
        self.correction = UnitMultiplicities(seams.cyclotomic_correction(1), seams.cyclotomic_correction(2))
        self.bigon = UnitMultiplicities(
            checked_add(overlap.plus, self.correction.plus), checked_add(overlap.minus, self.correction.minus),
        )
        self.seams = seams^


def neutral_spectrum_for_sink(
    graph: PeriodicOverlapGraph, component: Int, max_seams: Int = 100000, max_dimension: Int = 48,
) raises -> NeutralSinkSpectrum:
    """Conditional bigon spectrum for the unique strict carrier at rank two.

    Occurrence state and row indices use the order in graph.components[component].
    Child ordinals refer to the original physical order on each row.
    """
    if component < 0 or component >= len(graph.components) or not graph.aligned_sink[component]:
        raise Error("one-track seams: expected an aligned nonproductive sink")
    ref members = graph.components[component]
    var index = Dict[Int, Int]()
    for k in range(len(members)):
        index[members[k]] = k
    var rows = List[List[Int]]()
    var swap = List[Int]()
    var states = List[OverlapState]()
    for v in members:
        var other = graph.swap_vertex[v]
        if other not in index:
            raise Error("one-track seams: strict rank-two sink must be invariant under swap")
        swap.append(index[other])
        states.append(graph.graph.states[v])
        var row = List[Int]()
        for u in graph.graph.adj[v]:
            if u not in index:
                raise Error("one-track seams: sink row leaves its component")
            row.append(index[u])
        rows.append(row^)
    var overlap = odd_unit_multiplicities(rows, swap, max_dimension)
    var seams = one_track_seam_cycles(rows, overlap_boundary_masks(graph.tables, states), max_seams)
    return NeutralSinkSpectrum(overlap, seams^)
