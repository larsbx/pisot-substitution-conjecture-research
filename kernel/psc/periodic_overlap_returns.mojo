"""Ordinary and exchanged interior pair returns in the unit PIP3 box graph.

The indexed overlap rows are in spatial order. Count returning occurrence
walks in recurrent SCCs, removing the two paths at the *physical* endpoints.
A return whose start is in a closed, nonproductive aligned SCC is the
capacity of a strict joining at coincidence rank two. The computation does
not assume or determine rank two.
"""

from finite_exact.checked_int import checked_add
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.overlap_obstruction import recurrent_sccs
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    SeedOverlapTables,
    build_seed_overlap_tables_screened,
    first_coincidence_depths,
    interior_overlap_cached,
    selected_overlap_child,
)
from psc.perron_field3 import CubicElt, cubic_scale_checked
from psc.vertex_coincidence import build_box_graph


struct InteriorPairCounts(ImplicitlyCopyable, Copyable, Movable):
    var distinct: Int
    var noncoincident: Int
    var aligned_sink: Int

    def __init__(out self):
        self.distinct = 0
        self.noncoincident = 0
        self.aligned_sink = 0

    def record(mut self, count: Int, noncoincident: Bool, aligned_sink: Bool) raises:
        if count < 0:
            raise Error("periodic overlaps: endpoint corrections exceed occurrence count")
        self.distinct = checked_add(self.distinct, count)
        if noncoincident:
            self.noncoincident = checked_add(self.noncoincident, count)
        if aligned_sink:
            self.aligned_sink = checked_add(self.aligned_sink, count)


struct OverlapReturnCounts(ImplicitlyCopyable, Copyable, Movable):
    var ordinary: InteriorPairCounts
    var exchanged: InteriorPairCounts

    def __init__(out self):
        self.ordinary = InteriorPairCounts()
        self.exchanged = InteriorPairCounts()


struct PeriodicOverlapGraph(Copyable, Movable):
    var tables: SeedOverlapTables
    var graph: SeedOverlapAutomaton
    var components: List[List[Int]]
    var owner: List[Int]
    var swap_vertex: List[Int]
    var noncoincident: List[Bool]
    var aligned_sink: List[Bool]
    var nonproductive_sinks: Int
    var aligned_sinks: Int

    def __init__(out self, sigma: List[List[Int]], max_states: Int = 400000) raises:
        var tables = build_seed_overlap_tables_screened(sigma)
        var det = Mat3(substitution_incidence(sigma)).det()
        if det != 1 and det != -1:
            raise Error("periodic overlaps: incidence matrix must be unimodular")
        var graph = build_box_graph(tables, max_states)
        if graph.capped:
            raise Error("periodic overlaps: state cap reached; inconclusive")
        self.tables = tables^
        self.graph = graph^
        self.components = recurrent_sccs(self.graph)
        self.owner = List[Int](length=self.graph.size(), fill=-1)
        self.swap_vertex = List[Int]()
        self.noncoincident = List[Bool]()
        self.aligned_sink = List[Bool]()
        self.nonproductive_sinks = 0
        self.aligned_sinks = 0

        var index = Dict[OverlapState, Int]()
        for v in range(self.graph.size()):
            index[self.graph.states[v]] = v
        for v in range(self.graph.size()):
            var state = self.graph.states[v]
            var other = OverlapState(state.bottom, state.top, cubic_scale_checked(state.shift, -1))
            if other not in index:
                raise Error("periodic overlaps: the complete box lost a swapped vertex")
            self.swap_vertex.append(index[other])
        for v in range(self.graph.size()):
            ref row = self.graph.adj[v]
            ref swapped = self.graph.adj[self.swap_vertex[v]]
            if len(row) != len(swapped):
                raise Error("periodic overlaps: swap changed the number of child occurrences")
            for i in range(len(row)):
                if self.swap_vertex[row[i]] != swapped[i]:
                    raise Error("periodic overlaps: swap changed physical child order")

        for c in range(len(self.components)):
            for v in self.components[c]:
                self.owner[v] = c
        var depths = first_coincidence_depths(self.graph)
        for c in range(len(self.components)):
            ref comp = self.components[c]
            var sterile = depths[comp[0]] < 0
            var closed = True
            var aligned = False
            for v in comp:
                aligned = aligned or self.graph.states[v].shift.is_zero()
                for u in self.graph.adj[v]:
                    closed = closed and self.owner[u] == c
            self.noncoincident.append(sterile)
            self.aligned_sink.append(sterile and closed and aligned)
            self.nonproductive_sinks += Int(sterile and closed)
            self.aligned_sinks += Int(sterile and closed and aligned)

    def occurrence_indices(self, source: Int, ordinal: Int) raises -> List[Int]:
        """Replay one graph edge as the two local image indices.

        Enumerate position pairs independently of the streaming graph
        builder. Ordinals select an occurrence even for repeated edge heads.
        """
        if source < 0 or source >= self.graph.size():
            raise Error("periodic overlaps: invalid occurrence source")
        if ordinal < 0 or ordinal >= len(self.graph.adj[source]):
            raise Error("periodic overlaps: invalid occurrence ordinal")
        var state = self.graph.states[source]
        var cache = Dict[CubicElt, Int]()
        var k = 0
        for i in range(len(self.tables.sigma[state.top])):
            for j in range(len(self.tables.sigma[state.bottom])):
                var child = selected_overlap_child(self.tables, state, i, j)
                if interior_overlap_cached(self.tables, cache, child):
                    if k == ordinal:
                        if child != self.graph.states[self.graph.adj[source][ordinal]]:
                            raise Error("periodic overlaps: occurrence replay disagrees with the graph")
                        return [i, j]
                    k += 1
        raise Error("periodic overlaps: occurrence missing from the substituted words")

    def _endpoint(self, root: Int, power: Int, right: Bool) -> Int:
        var c = self.owner[root]
        var v = root
        for _ in range(power):
            ref row = self.graph.adj[v]
            # A recurrent vertex always has a child. Use the full row
            # before the SCC filter. An endpoint that exits cannot return.
            v = row[len(row) - 1 if right else 0]
            if self.owner[v] != c:
                return -1
        return v

    def count(self, power: Int, max_work: Int = 20000000) raises -> OverlapReturnCounts:
        """All ordered pairs with the origin strictly inside both tiles.

        The work budget bounds per-root state and edge scans. Arithmetic
        overflow and exhausted budgets raise before issuing counts.
        """
        if power <= 0 or max_work <= 0:
            raise Error("periodic overlaps: power and work cap must be positive")
        var current = List[Int](length=self.graph.size(), fill=0)
        var next = List[Int](length=self.graph.size(), fill=0)
        var work_left = max_work
        var result = OverlapReturnCounts()
        for c in range(len(self.components)):
            ref comp = self.components[c]
            var scan = len(comp)
            for v in comp:
                scan = checked_add(scan, len(self.graph.adj[v]))
            if len(comp) > work_left // power // scan:
                raise Error("periodic overlaps: work cap reached; inconclusive")
            work_left -= power * len(comp) * scan
            for root in comp:
                for v in comp:
                    current[v] = 0
                current[root] = 1
                for _ in range(power):
                    for v in comp:
                        next[v] = 0
                    for v in comp:
                        var count = current[v]
                        if count == 0:
                            continue
                        for u in self.graph.adj[v]:
                            if self.owner[u] == c:
                                next[u] = checked_add(next[u], count)
                    var work = current^
                    current = next^
                    next = work^
                var first = self._endpoint(root, power, False)
                var last = self._endpoint(root, power, True)
                result.ordinary.record(
                    current[root] - Int(first == root) - Int(last == root),
                    self.noncoincident[c], self.aligned_sink[c],
                )
                var other = self.swap_vertex[root]
                # A walk to the swap followed by its swapped walk returns.
                if self.owner[other] == c:
                    result.exchanged.record(
                        current[other] - Int(first == other) - Int(last == other),
                        self.noncoincident[c], self.aligned_sink[c],
                    )
        return result
