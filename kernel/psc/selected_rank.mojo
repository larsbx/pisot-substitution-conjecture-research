"""Proof-carrying selected coincidence ranks on exact overlap graphs.

The checker never searches for a path or computes a rank; it validates one
selected actual successor at each listed nonterminal state. A valid witness
proves selected coincidence reachability for LISTED states only.
An independently COMPLETE forward-closure certificate is still required
before promoting an all-descendants or boundary-hitting statement.

This is the canonical Mojo rank-verification layer. The separate reference
Python reversal quotient is a research oracle, not the source of truth.
"""

from psc.overlap_seed_patch import (
    SeedOverlapAutomaton,
    SeedOverlapTables,
    selected_overlap_child,
    interior_overlap,
)


def verify_rank_forest(
    adj: List[List[Int]],
    typed_terminal: List[Bool],
    rank: List[Int],
    chosen_edge_position: List[Int],
) raises -> Int:
    """Verify a selected rank forest on an *enumerated* finite graph.

    Each nonterminal has one selected indexed adjacency position leading
    to rank exactly one less. Terminal states have rank zero and chosen=-1.
    The result is max rank; it does NOT assert complete source coverage.
    All adjacency target IDs are checked, including unchosen edges.
    """
    var n = len(adj)
    if n == 0 or len(typed_terminal) != n or len(rank) != n or len(chosen_edge_position) != n:
        raise Error("incomplete rank witness arrays")
    var highest = 0
    for v in range(n):
        for e in range(len(adj[v])):
            var dest = adj[v][e]
            if dest < 0 or dest >= n:
                raise Error("malformed graph adjacency target")
        if rank[v] < 0:
            raise Error("negative rank")
        if typed_terminal[v]:
            if rank[v] != 0 or chosen_edge_position[v] != -1:
                raise Error("typed coincidence must have zero rank and no selected edge")
        else:
            if rank[v] == 0:
                raise Error("noncoincident state has zero rank")
            var pos = chosen_edge_position[v]
            if pos < 0 or pos >= len(adj[v]):
                raise Error("noncoincident state lacks actual selected child")
            var target = adj[v][pos]
            # Avoid overflow in rank[target]+1.
            if rank[target] != rank[v] - 1:
                raise Error("selected edge does not decrease exact rank by one")
        if rank[v] > highest:
            highest = rank[v]
    return highest


def verify_overlap_rank_witness(
    tables: SeedOverlapTables,
    a: SeedOverlapAutomaton,
    rank: List[Int],
    chosen_edge_position: List[Int],
    chosen_top_occurrence: List[Int],
    chosen_bottom_occurrence: List[Int],
) raises -> Int:
    """Bind the forest to literal occurrence indices and cubic-field states.

    For every listed state, the selected child is independently recomputed
    from the actual substituted word and both exact proper prefixes.
    This is LOCAL soundness: an arbitrary caller-built a.capped=False
    does not prove that all possible overlap descendants were enumerated.
    """
    var n = a.size()
    if len(chosen_top_occurrence) != n or len(chosen_bottom_occurrence) != n:
        raise Error("incomplete ordered occurrence witness arrays")
    var terminals = List[Bool]()
    for v in range(n):
        terminals.append(a.states[v].is_coincidence())
    var maximum = verify_rank_forest(a.adj, terminals, rank, chosen_edge_position)
    for v in range(n):
        if not interior_overlap(tables, a.states[v]):
            raise Error("listed source state is not a strict overlap")
        if terminals[v]:
            if chosen_top_occurrence[v] != -1 or chosen_bottom_occurrence[v] != -1:
                raise Error("typed terminal has a forged occurrence")
            continue
        var top = chosen_top_occurrence[v]
        var bottom = chosen_bottom_occurrence[v]
        if top < 0 or bottom < 0:
            raise Error("missing actual occurrence address")
        # SeedOverlapTables.prefix and selected_overlap_child reject a
        # nonexistent index before any image/field arithmetic.
        var exact = selected_overlap_child(tables, a.states[v], top, bottom)
        var dest = a.adj[v][chosen_edge_position[v]]
        if exact != a.states[dest] or not interior_overlap(tables, exact):
            raise Error("selected indexed child disagrees with exact geometry")
    return maximum


def verify_complete_overlap_rank(
    tables: SeedOverlapTables,
    a: SeedOverlapAutomaton,
    rank: List[Int],
    chosen_edge_position: List[Int],
    chosen_top_occurrence: List[Int],
    chosen_bottom_occurrence: List[Int],
) raises -> Int:
    """A complete-graph wrapper, refusing truncated automata.

    The completeness of a noncapped automaton must originate from the
    trusted exact closure builder. Merely setting a.capped=False on a
    fabricated partial graph is NOT a completeness certificate.
    """
    if a.capped:
        raise Error("rank audit cannot certify a capped overlap graph")
    return verify_overlap_rank_witness(
        tables, a, rank, chosen_edge_position,
        chosen_top_occurrence, chosen_bottom_occurrence
    )


def verify_exact_closed_carrier(
    tables: SeedOverlapTables,
    a: SeedOverlapAutomaton,
    required_seeds: List[OverlapState],
) raises -> Int:
    """Independently re-enumerate ALL actual strict children and prove closure.

    This verifier deliberately uses the exhaustive ordered top/bottom loop
    rather than trusting a.capped=False or an optimized child sweep.
    Typed coincidence states may be terminalized only at full shift zero.

    If each required seed occurs, every overlap reachable from those seeds
    lies in the finite state table by induction over path length.
    This is a finite exact closure certificate, not a uniform parameter
    theorem or a realized-overlap coverage certificate.
    """
    if a.capped:
        raise Error("cannot prove closure from a capped automaton")
    var n = a.size()
    if n == 0 or len(a.adj) != n:
        raise Error("missing states or adjacency arrays")
    var index = Dict[OverlapState, Int](capacity=n)
    for v in range(n):
        var state = a.states[v]
        if state in index:
            raise Error("duplicate exact overlap state")
        if not interior_overlap(tables, state):
            raise Error("non-strict state in proposed complete carrier")
        index[state] = v
    for j in range(len(required_seeds)):
        if required_seeds[j] not in index:
            raise Error("required actual seed is outside the proposed carrier")
    for v in range(n):
        var state = a.states[v]
        if state.is_coincidence():
            if len(a.adj[v]) != 0:
                raise Error("typed terminal was not terminalized")
            continue
        var position = 0
        # Exhaustive literal occurrence loops: this duplicates neither
        # the optimized overlap_children sweep nor its skip heuristics.
        for i in range(len(tables.sigma[state.top])):
            for j in range(len(tables.sigma[state.bottom])):
                var child = selected_overlap_child(tables, state, i, j)
                if not interior_overlap(tables, child):
                    continue
                if child not in index:
                    raise Error("strict child escapes the proposed closed carrier")
                if position >= len(a.adj[v]):
                    raise Error("indexed adjacency omitted a strict child")
                if a.adj[v][position] != index[child]:
                    raise Error("actual strict occurrence ordering or child ID differs")
                position += 1
        if position != len(a.adj[v]):
            raise Error("adjacency has extra or duplicate indexed child entries")
    return n


def verify_closed_ranked_carrier(
    tables: SeedOverlapTables,
    a: SeedOverlapAutomaton,
    required_seeds: List[OverlapState],
    rank: List[Int],
    chosen_edge_position: List[Int],
    chosen_top_occurrence: List[Int],
    chosen_bottom_occurrence: List[Int],
) raises -> Int:
    """Coverage plus selected rank: every listed seed descendant is productive.

    Independent ALL-child closure is checked before selected path soundness.
    This proves the scoped finite carrier claim only: complete literature
    realized-overlap coverage and a uniform k,t symbolic carrier remain open.
    """
    _ = verify_exact_closed_carrier(tables, a, required_seeds)
    return verify_overlap_rank_witness(
        tables, a, rank, chosen_edge_position,
        chosen_top_occurrence, chosen_bottom_occurrence
    )
