"""Independent finite selected-rank soundness oracle (not graph closure).

The Mojo implementation at kernel/psc/selected_rank.mojo is canonical.
This Python reference is a small, separately written fail-closed checker.
A selected witness proves productivity for the LISTED vertices only.
"""
from __future__ import annotations


class BadRankWitness(ValueError):
    pass


def verify_selected_rank(adj, typed, ranks, choices):
    """Return max certified rank; refuse every malformed or cyclic witness.

    A choice is an integer index *into its source's actual adjacency*.
    This checker does not treat incomplete adjacency as complete coverage.
    """
    n = len(adj)
    if not n or any(len(x) != n for x in (typed, ranks, choices)):
        raise BadRankWitness("shape mismatch")
    if any(type(r) is not int or r < 0 for r in ranks):
        raise BadRankWitness("negative/noninteger rank")
    for v, edges in enumerate(adj):
        if any(type(w) is not int or not 0 <= w < n for w in edges):
            raise BadRankWitness("malformed adjacency")
        if type(typed[v]) is not bool:
            raise BadRankWitness("unverified terminal marker")
        if type(choices[v]) is not int:
            raise BadRankWitness("malformed child address")
        if typed[v]:
            if ranks[v] != 0 or choices[v] != -1:
                raise BadRankWitness("terminal rank/choice mismatch")
        else:
            if ranks[v] == 0 or not 0 <= choices[v] < len(edges):
                raise BadRankWitness("nonterminal missing ranked choice")
            target = edges[choices[v]]
            if ranks[target] != ranks[v] - 1:
                raise BadRankWitness("nondecreasing actual successor")
    return max(ranks)


def replay_selected(adj, typed, ranks, choices, start):
    """Independently replay the claimed path with a finite fuel budget."""
    verify_selected_rank(adj, typed, ranks, choices)
    if type(start) is not int or not 0 <= start < len(adj):
        raise BadRankWitness("unknown vertex")
    v, walk = start, []
    for _ in range(ranks[start]):
        if typed[v]:
            raise BadRankWitness("terminal before the claimed rank")
        pos = choices[v]
        v = adj[v][pos]
        walk.append(v)
    if not typed[v] or ranks[v] != 0:
        raise BadRankWitness("selected walk did not hit typed coincidence")
    return walk
