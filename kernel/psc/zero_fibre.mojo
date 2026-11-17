"""Literal patch comparisons in the legal BBK zero fibre for PIP3.

`compare_zero_fibre` compares the first periodic legal seam with every based
seam and interior state. The catalogue uses the eventual legal bigram range
and the complete certified periodic-state box. A comparison searches for a
common labelled descendant of the two initial patches. It needs a hit from
one of their overlapping edge pairs. Consult the zero-fibre theorem for the
geometric and spectral implications of these finite comparisons.
"""

from psc.c4_geometric_f import (
    GEOMETRIC_F_STATE_CAP,
    PrototileMap,
    PrototileState,
    StableRadiiCache,
    decide_geometric_f_with,
)
from psc.h1_census import eventual_range, legal_two_words
from psc.overlap_seed_patch import (
    OverlapState,
    build_overlap_graph_from_seeds,
    first_coincidence_depths,
    interior_overlap_cached,
)
from psc.perron_field3 import CubicElt, cubic_sub_checked


struct OriginPatch(ImplicitlyCopyable, Copyable, Movable, Writable):
    """An edge covering zero, and its predecessor when zero is a vertex.

    For an interior cut `before = -1`. For a seam `cut` is a vertex state
    and `before` labels the edge ending at zero.
    """

    var before: Int
    var cut: PrototileState
    var period: Int

    def __init__(out self, before: Int, cut: PrototileState, period: Int):
        self.before = before
        self.cut = cut
        self.period = period

    def write_to[W: Writer](self, mut w: W):
        w.write("[", self.before, ",", self.cut, ", period ", self.period, "]")


struct ZeroFibreComparison(Copyable, Movable):
    var patches: List[OriginPatch]
    var depths: List[Int]
    var overlap_states: Int

    def __init__(out self, patches: List[OriginPatch], depths: List[Int], overlap_states: Int):
        self.patches = patches.copy()
        self.depths = depths.copy()
        self.overlap_states = overlap_states

    def all_meet_reference(self) -> Bool:
        for depth in self.depths:
            if depth < 0:
                return False
        return True


def _seam_period(sigma: List[List[Int]], a: Int, b: Int) raises -> Int:
    var x = a
    var y = b
    for period in range(1, 10):
        x = sigma[x][len(sigma[x]) - 1]
        y = sigma[y][0]
        if x == a and y == b:
            return period
    raise Error("eventual legal bigram did not return")


def _origin_patches(mut m: PrototileMap, max_prototile_states: Int) raises -> List[OriginPatch]:
    var sigma = m.tables.sigma.copy()
    var seams = eventual_range(sigma, legal_two_words(sigma))
    var out = List[OriginPatch]()
    for a in range(3):
        for b in range(3):
            if seams[3 * a + b]:
                out.append(OriginPatch(a, PrototileState(b, 0, 0, 0), _seam_period(sigma, a, b)))
    if len(out) == 0:
        raise Error("primitive expanding substitution has no periodic legal seam")
    var boxes = StableRadiiCache()
    var verdict = decide_geometric_f_with(m, boxes, max_prototile_states)
    for c in range(len(verdict.cycles)):
        ref cycle = verdict.cycles[c]
        for k in range(cycle.period()):
            out.append(OriginPatch(-1, cycle.states[k], cycle.period()))
    return out^


def _edge_labels(patch: OriginPatch) -> List[Int]:
    if patch.before < 0:
        return [patch.cut.letter]
    return [patch.before, patch.cut.letter]


def _edge_starts(m: PrototileMap, patch: OriginPatch) raises -> List[CubicElt]:
    var cut_start = cubic_sub_checked(CubicElt(), m.position(patch.cut))
    if patch.before < 0:
        return [cut_start]
    return [cubic_sub_checked(CubicElt(), m.tables.lengths.at(patch.before)), cut_start]


def compare_zero_fibre(
    sigma: List[List[Int]],
    max_prototile_states: Int = GEOMETRIC_F_STATE_CAP,
    max_overlap_states: Int = 20000,
) raises -> ZeroFibreComparison:
    """Minimum descendant depth against patch 0, or `-1` on a complete miss.

    Arithmetic and incomplete graph or box limits raise. Each successful
    depth may use a different labelled edge. The field encodes integral
    displacements injectively for the admitted irreducible cubics.
    """
    var m = PrototileMap(sigma)
    var patches = _origin_patches(m, max_prototile_states)
    var reference_labels = _edge_labels(patches[0])
    var reference_starts = _edge_starts(m, patches[0])
    var seed_rows = List[List[OverlapState]]()
    var roots = List[OverlapState]()
    var signs = Dict[CubicElt, Int]()
    for patch in patches:
        var labels = _edge_labels(patch)
        var starts = _edge_starts(m, patch)
        var row = List[OverlapState]()
        for i in range(len(reference_labels)):
            for j in range(len(labels)):
                var shift = cubic_sub_checked(starts[j], reference_starts[i])
                var pair = OverlapState(reference_labels[i], labels[j], shift)
                if interior_overlap_cached(m.tables, signs, pair):
                    row.append(pair)
                    roots.append(pair)
        if len(row) == 0:
            raise Error("two patches through the origin lost their overlapping cut edges")
        seed_rows.append(row^)
    var graph = build_overlap_graph_from_seeds(m.tables, roots, signs, max_overlap_states)
    var dist = first_coincidence_depths(graph)
    var index = Dict[OverlapState, Int]()
    for k in range(len(graph.states)):
        index[graph.states[k]] = k
    var depths = List[Int]()
    for row in seed_rows:
        var least = -1
        for seed in row:
            var depth = dist[index[seed]]
            if depth >= 0 and (least < 0 or depth < least):
                least = depth
        depths.append(least)
    return ZeroFibreComparison(patches, depths, len(graph.states))
