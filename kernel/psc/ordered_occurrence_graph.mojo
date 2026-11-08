"""Raw ordered BPA closure, with one record per child interval."""

from finite_exact.checked_int import checked_mul
from psc.bpa import coincidence_boundaries, normalise
from psc.words import Pair, is_balanced
from substitution_dynamics.substitution import Substitution, validate_word

# Each edge is [source, target, ordinal, start, end, top parent, top offset,
# bottom parent, bottom offset, sign]. Sign compares the raw child with its
# lexicographic normalization; coincidences use +1.


struct OrderedGraph(Movable):
    var states: List[Pair]
    var edges: List[List[Int]]
    var complete: Bool

    def __init__(out self, var states: List[Pair], var edges: List[List[Int]], complete: Bool):
        self.states = states^
        self.edges = edges^
        self.complete = complete


def _index(states: List[Pair], pair: Pair) -> Int:
    for i in range(len(states)):
        if states[i] == pair:
            return i
    return -1


def _fits(sigma: Substitution, word: List[Int], limit: Int) -> Bool:
    var size = 0
    for a in word:
        var width = len(sigma.images[a])
        if width > limit - size:
            return False
        size += width
    return True


def ordered_graph(images: List[List[Int]], seed: Pair, max_states: Int,
                  max_edges: Int, max_word: Int) raises -> OrderedGraph:
    """Explore the child closure of one literal seed; keep coincidences and exits.

    An incomplete result contains only a prefix of the traversal and is never
    eligible for potential checking. Word budgets apply before inflation.
    """
    var sigma = Substitution.checked(images)
    if sigma.size != 3 or max_states < 1 or max_edges < 0 or max_word < 1:
        raise Error("invalid ordered occurrence graph domain")
    validate_word(seed.u, 3)
    validate_word(seed.v, 3)
    if len(seed.u) == 0 or not is_balanced(seed):
        raise Error("ordered graph requires a nonempty balanced seed")

    var states: List[Pair] = [seed.copy()]
    var edges = List[List[Int]]()
    var src = 0
    while src < len(states):
        var pair = states[src].copy()
        if not _fits(sigma, pair.u, max_word) or not _fits(sigma, pair.v, max_word):
            return OrderedGraph(states^, edges^, False)
        var top = sigma.apply(pair.u)
        var bottom = sigma.apply(pair.v)
        var cuts = coincidence_boundaries(top, bottom)
        var top_starts = sigma.image_prefix_lengths(pair.u)
        var bottom_starts = sigma.image_prefix_lengths(pair.v)
        var ti = 0
        var bi = 0
        for ordinal in range(len(cuts) - 1):
            if len(edges) == max_edges:
                return OrderedGraph(states^, edges^, False)
            var start = cuts[ordinal]
            var end = cuts[ordinal + 1]
            while top_starts[ti + 1] <= start:
                ti += 1
            while bottom_starts[bi + 1] <= start:
                bi += 1
            var u = List[Int]()
            var v = List[Int]()
            for i in range(start, end):
                u.append(top[i])
                v.append(bottom[i])
            var child = Pair(u, v)
            var dst = _index(states, child)
            if dst < 0:
                if len(states) == max_states:
                    return OrderedGraph(states^, edges^, False)
                dst = len(states)
                states.append(child.copy())
            var sign = 1 if normalise(child) == child else -1
            edges.append([src, dst, ordinal, start, end, ti,
                          start - top_starts[ti], bi, start - bottom_starts[bi], sign])
        src += 1
    return OrderedGraph(states^, edges^, True)


def replay_ordered_graph(images: List[List[Int]], seed: Pair, packet: OrderedGraph,
                         max_states: Int, max_edges: Int, max_word: Int) raises -> Bool:
    """Compare ordered rows including parallel edges. Exhaustion always refuses."""
    if not packet.complete:
        return False
    var expected = ordered_graph(images, seed, max_states, max_edges, max_word)
    if not expected.complete or len(expected.states) != len(packet.states) or len(expected.edges) != len(packet.edges):
        return False
    for i in range(len(expected.states)):
        if expected.states[i] != packet.states[i]:
            return False
    for i in range(len(expected.edges)):
        if expected.edges[i] != packet.edges[i]:
            return False
    return True


def ordered_parent_residuals(images: List[List[Int]], seed: Pair, graph: OrderedGraph,
                             max_states: Int, max_edges: Int, max_word: Int) raises -> List[List[Int]]:
    """Rows [source, target, r0, r1, r2] in canonical occurrence order."""
    if not replay_ordered_graph(images, seed, graph, max_states, max_edges, max_word):
        raise Error("parent residuals require a complete canonical occurrence packet")
    var rows = List[List[Int]]()
    for edge in graph.edges:
        ref parent = graph.states[edge[0]]
        var delta: List[Int] = [0, 0, 0]
        for i in range(edge[5]):
            delta[parent.u[i]] += 1
        for i in range(edge[7]):
            delta[parent.v[i]] -= 1
        var scale = edge[9] - 1
        rows.append([edge[0], edge[1], checked_mul(scale, delta[0]),
                     checked_mul(scale, delta[1]), checked_mul(scale, delta[2])])
    return rows^
