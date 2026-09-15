"""Finite obstruction extraction for the seed-patch overlap graph.

This module is deliberately structural.  It does not prove overlap
productivity.  If productivity fails on a complete finite overlap graph, it
extracts the closed recurrent noncoincidence SCCs in which any counterexample
must eventually live.

All queries fail closed on a capped graph: a capped graph is an incomplete
prefix and cannot certify either productivity or a recurrent obstruction.
"""

from psc.overlap_seed_patch import SeedOverlapAutomaton, nonproductive_overlap_states


def overlap_sccs(a: SeedOverlapAutomaton) raises -> List[List[Int]]:
    """Strongly connected components of a complete overlap graph.

    Iterative Tarjan implementation, mirroring the BPA kernel but keeping the
    overlap obstruction layer independent of balanced-pair finiteness.
    """
    if a.capped:
        raise Error("overlap SCCs are undefined for a capped partial graph")

    var n = a.size()
    var idx = List[Int]()
    var low = List[Int]()
    var on = List[Bool]()
    for _ in range(n):
        idx.append(-1)
        low.append(0)
        on.append(False)

    var stack = List[Int]()
    var out = List[List[Int]]()
    var counter = 0

    for root in range(n):
        if idx[root] != -1:
            continue
        var call = List[Int]()
        var pos = List[Int]()
        call.append(root)
        pos.append(0)
        idx[root] = counter
        low[root] = counter
        counter += 1
        stack.append(root)
        on[root] = True

        while len(call) > 0:
            var v = call[len(call) - 1]
            var p = pos[len(pos) - 1]
            if p < len(a.adj[v]):
                pos[len(pos) - 1] = p + 1
                var w = a.adj[v][p]
                if idx[w] == -1:
                    idx[w] = counter
                    low[w] = counter
                    counter += 1
                    stack.append(w)
                    on[w] = True
                    call.append(w)
                    pos.append(0)
                elif on[w]:
                    if idx[w] < low[v]:
                        low[v] = idx[w]
            else:
                _ = call.pop()
                _ = pos.pop()
                if len(call) > 0:
                    var parent = call[len(call) - 1]
                    if low[v] < low[parent]:
                        low[parent] = low[v]
                if low[v] == idx[v]:
                    var comp = List[Int]()
                    while True:
                        var w = stack.pop()
                        on[w] = False
                        comp.append(w)
                        if w == v:
                            break
                    out.append(comp^)
    return out^


def _has_cycle(a: SeedOverlapAutomaton, comp: List[Int]) -> Bool:
    if len(comp) > 1:
        return True
    if len(comp) == 0:
        return False
    var v = comp[0]
    for j in range(len(a.adj[v])):
        if a.adj[v][j] == v:
            return True
    return False


def nonproductive_sink_sccs(a: SeedOverlapAutomaton) raises -> List[List[Int]]:
    """Closed recurrent SCCs consisting entirely of nonproductive overlaps.

    A nonproductive vertex cannot have a productive child: a coincidence
    reachable from that child would also be reachable from the parent.  Hence
    the nonproductive set is forward closed.  In a finite complete graph, any
    infinite child path from a nonproductive vertex eventually enters a sink
    SCC of the nonproductive subgraph.  Those sink SCCs are exactly the
    components returned here.

    For a genuine overlap graph every noncoincidence overlap has at least one
    child occurrence (the inflated intersection is nonempty), so nonempty
    nonproductivity implies that at least one returned component exists.
    Synthetic graph tests may omit that geometric out-degree invariant; this
    function therefore reports what is present rather than silently inventing
    a recurrent component.
    """
    if a.capped:
        raise Error("overlap obstruction is undefined for a capped partial graph")

    var bad_indices = nonproductive_overlap_states(a)
    var bad = List[Bool]()
    for _ in range(a.size()):
        bad.append(False)
    for i in range(len(bad_indices)):
        bad[bad_indices[i]] = True

    var all = overlap_sccs(a)
    var out = List[List[Int]]()
    for k in range(len(all)):
        ref comp = all[k]
        if len(comp) == 0 or not _has_cycle(a, comp):
            continue

        var member = List[Bool]()
        for _ in range(a.size()):
            member.append(False)
        var all_bad = True
        for i in range(len(comp)):
            member[comp[i]] = True
            if not bad[comp[i]]:
                all_bad = False
        if not all_bad:
            continue

        var closed = True
        for i in range(len(comp)):
            var v = comp[i]
            for j in range(len(a.adj[v])):
                if not member[a.adj[v][j]]:
                    closed = False
        if closed:
            out.append(comp.copy())
    return out^
