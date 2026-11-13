"""Literal ordered terminal-child carriers for the finite Lean checker.

The existing bounded BPA engine supplies candidates. This adapter expands
track swaps and replays every raw child row; it implements no new search.
The native row contract is stronger than the Lean states-only upper bound:
unique irreducible words, complete ordered rows, and terminal coincidences.
Pre-code decision: docs/c4-forward-carrier-literature-2026-11-12.md.
"""

from substitution_dynamics.balanced_pair_algorithm import build_bounded
from substitution_dynamics.balanced_pairs import decompose, normalise, seed_states
from substitution_dynamics.substitution import Substitution
from substitution_dynamics.words import Pair, is_balanced


struct ForwardCarrier(Copyable, Movable):
    var states: List[Pair]
    var rows: List[List[Int]]

    def __init__(out self, var states: List[Pair], var rows: List[List[Int]]):
        self.states = states^
        self.rows = rows^


def check_carrier(images: List[List[Int]], carrier: ForwardCarrier) raises -> Bool:
    """Replay literal rows; no supplied completeness flag is trusted.

    A finite closed superset is permitted. Native words must be unique and
    irreducible, but no discovery order or productivity rank is assumed.
    """
    var sigma = Substitution.checked(images)
    if len(carrier.states) != len(carrier.rows):
        return False
    var index = Dict[String, Int]()
    for i in range(len(carrier.states)):
        ref p = carrier.states[i]
        if len(p.u) == 0 or len(p.u) != len(p.v):
            return False
        for j in range(len(p.u)):
            if p.u[j] < 0 or p.u[j] >= sigma.size or p.v[j] < 0 or p.v[j] >= sigma.size:
                return False
        if not is_balanced(p, sigma.size) or p.key() in index:
            return False
        if len(decompose(p.u, p.v, sigma.size)) != 1:
            return False
        index[p.key()] = i
    var seeds = seed_states(sigma.size)
    for i in range(len(seeds)):
        if seeds[i].key() not in index:
            return False
        var swapped = Pair(seeds[i].v, seeds[i].u)
        if swapped.key() not in index:
            return False
    for i in range(len(carrier.states)):
        ref p = carrier.states[i]
        if p.is_coincidence():
            if len(carrier.rows[i]) != 0:
                return False
            continue
        var raw = decompose(sigma.apply(p.u), sigma.apply(p.v), sigma.size)
        if len(raw) != len(carrier.rows[i]):
            return False
        for j in range(len(raw)):
            var destination = carrier.rows[i][j]
            if destination < 0 or destination >= len(carrier.states):
                return False
            if carrier.states[destination] != raw[j]:
                return False
    return True


def build_forward_carrier(
    images: List[List[Int]], max_states: Int, max_length: Int
) raises -> ForwardCarrier:
    """Expand a complete canonical normalized carrier to ordered words.

    State or length exhaustion raises before any certificate is returned.
    The state budget applies to normalized states, as in build_bounded.
    """
    var sigma = Substitution.checked(images)
    var bounded = build_bounded(sigma, max_states, max_length)
    if not bounded.complete():
        raise Error("forward BPA budget exhausted (kind=" + String(bounded.exhausted) + "); no carrier certificate")

    var normalized = Dict[String, Int]()
    var ordered = Dict[String, Int]()
    var states = List[Pair]()
    for i in range(bounded.graph.size()):
        ref p = bounded.graph.states[i]
        if p != normalise(p) or p.key() in normalized:
            raise Error("canonical BPA has a repeated or unnormalized state")
        normalized[p.key()] = i
        ordered[p.key()] = len(states)
        states.append(p.copy())
        if not p.is_coincidence():
            var swapped = Pair(p.v, p.u)
            ordered[swapped.key()] = len(states)
            states.append(swapped^)

    # Independently bind every existing normalized row to the complete raw
    # factorization, including repeated factors and their physical order.
    for i in range(bounded.graph.size()):
        ref p = bounded.graph.states[i]
        if p.is_coincidence():
            if len(bounded.graph.adj[i]) != 0:
                raise Error("canonical BPA coincidence has outgoing children")
            continue
        var raw = decompose(sigma.apply(p.u), sigma.apply(p.v), sigma.size)
        if len(raw) != len(bounded.graph.adj[i]):
            raise Error("canonical BPA row omits or adds a child occurrence")
        for j in range(len(raw)):
            var key = normalise(raw[j]).key()
            if key not in normalized or bounded.graph.adj[i][j] != normalized[key]:
                raise Error("canonical BPA row disagrees with actual child order")

    var rows = List[List[Int]]()
    for i in range(len(states)):
        var row = List[Int]()
        if not states[i].is_coincidence():
            var raw = decompose(sigma.apply(states[i].u), sigma.apply(states[i].v), sigma.size)
            for j in range(len(raw)):
                var key = raw[j].key()
                if key not in ordered:
                    raise Error("ordered carrier omits an actual child")
                row.append(ordered[key])
        rows.append(row^)
    var result = ForwardCarrier(states^, rows^)
    if not check_carrier(images, result):
        raise Error("literal forward carrier failed complete row replay")
    return result^


def normalized_count(carrier: ForwardCarrier) -> Int:
    var keys = Dict[String, Bool]()
    for i in range(len(carrier.states)):
        keys[normalise(carrier.states[i]).key()] = True
    return len(keys)


def longest_state(carrier: ForwardCarrier) -> Int:
    var longest = 0
    for i in range(len(carrier.states)):
        longest = max(longest, carrier.states[i].length())
    return longest
