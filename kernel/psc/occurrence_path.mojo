"""Finite occurrence witnesses; no graph-closure or universal-productivity verdict.

Public checkers rebuild exact tables from sigma, never trust supplied geometry.
Addresses are zero-based, ordered top/bottom, from the root toward descendants.
"""
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, build_seed_overlap_tables,
    interior_overlap, selected_overlap_child,
)
from psc.perron_field3 import CubicElt, cubic_sub_checked
from psc.words import Pair, is_balanced
from psc.bpa import coincidence_boundaries
from substitution_dynamics.substitution import Substitution, validate_word

comptime CERTIFIED_LIFTABLE_TARGET_PATH = 0
comptime BUDGET_EXHAUSTED = 1
comptime DEPTH_COMPLETE_NO_CLOSURE = 2
comptime NO_MATCHED_TARGET_WITHIN_BUDGET = 3


struct SwapOccurrence(ImplicitlyCopyable, Copyable, Movable):
    var a: Int
    var b: Int
    var top_index: Int
    var bottom_index: Int

    def __init__(out self, a: Int, b: Int, top_index: Int, bottom_index: Int):
        self.a = a
        self.b = b
        self.top_index = top_index
        self.bottom_index = bottom_index

    def state(self, tables: SeedOverlapTables) raises -> OverlapState:
        if self.a < 0 or self.a >= self.b or self.b >= 3:
            raise Error("swap occurrence requires 0 <= a < b < 3")
        if self.top_index < 0 or self.top_index > 1 or self.bottom_index < 0 or self.bottom_index > 1:
            raise Error("swap occurrence read heads must be 0 or 1")
        var top = self.a if self.top_index == 0 else self.b
        var bottom = self.b if self.bottom_index == 0 else self.a
        var x = CubicElt() if self.top_index == 0 else tables.lengths.at(self.a)
        var y = CubicElt() if self.bottom_index == 0 else tables.lengths.at(self.b)
        var out = OverlapState(top, bottom, cubic_sub_checked(y, x))
        if not interior_overlap(tables, out):
            raise Error("seed occurrence has no interior overlap")
        return out


struct OccurrenceEdge(ImplicitlyCopyable, Copyable, Movable):
    var source: OverlapState
    var top_index: Int
    var bottom_index: Int
    var target: OverlapState

    def __init__(out self, source: OverlapState, top_index: Int, bottom_index: Int, target: OverlapState):
        self.source = source
        self.top_index = top_index
        self.bottom_index = bottom_index
        self.target = target


def _replay(tables: SeedOverlapTables, seed: SwapOccurrence, edges: List[OccurrenceEdge], max_steps: Int) raises -> OverlapState:
    if max_steps < 0 or len(edges) > max_steps:
        raise Error("occurrence replay step budget exhausted")
    var state = seed.state(tables)
    for k in range(len(edges)):
        var edge = edges[k]
        if edge.source != state:
            raise Error("occurrence path sources do not compose")
        var child = selected_overlap_child(tables, state, edge.top_index, edge.bottom_index)
        if not interior_overlap(tables, child) or child != edge.target:
            raise Error("selected child is not the claimed interior occurrence")
        state = child
    return state


def replay_overlap_path(sigma: List[List[Int]], seed: SwapOccurrence, edges: List[OccurrenceEdge], max_steps: Int = 10000) raises -> OverlapState:
    """Validate every edge, including paths that finish off target."""
    return _replay(build_seed_overlap_tables(sigma), seed, edges, max_steps)


def certify_overlap_path(sigma: List[List[Int]], seed: SwapOccurrence, edges: List[OccurrenceEdge], max_steps: Int = 10000) raises:
    if not replay_overlap_path(sigma, seed, edges, max_steps).is_coincidence():
        raise Error("replayed endpoint is not an equal-letter zero-offset target")


struct PathSearch(Copyable, Movable):
    var status: Int
    var edges: List[OccurrenceEdge]
    var states_seen: Int
    var choices_checked: Int

    def __init__(out self, status: Int, edges: List[OccurrenceEdge], states_seen: Int, choices_checked: Int):
        self.status = status
        self.edges = edges.copy()
        self.states_seen = states_seen
        self.choices_checked = choices_checked


def search_overlap_path(sigma: List[List[Int]], seed: SwapOccurrence, max_depth: Int, max_states: Int, max_choices: Int) raises -> PathSearch:
    """Deterministic BFS, interned by full overlap type, retaining one lift.

    A successful witness is replayed. Other outcomes carry no mathematical
    absence/closure verdict, even if this local queue happened to empty.
    """
    if max_depth < 0 or max_states < 1 or max_choices < 0:
        raise Error("invalid occurrence search budgets")
    var tables = build_seed_overlap_tables(sigma)
    var root = seed.state(tables)
    var states: List[OverlapState] = [root]
    var depths: List[Int] = [0]
    var parents: List[Int] = [-1]
    var incoming = List[OccurrenceEdge]()
    incoming.append(OccurrenceEdge(root, -1, -1, root))
    var index = Dict[OverlapState, Int]()
    index[root] = 0
    var head = 0
    var choices = 0
    var depth_limited = False
    var empty = List[OccurrenceEdge]()
    while head < len(states):
        var state = states[head]
        if state.is_coincidence():
            var reverse = List[OccurrenceEdge]()
            var cursor = head
            while parents[cursor] >= 0:
                reverse.append(incoming[cursor])
                cursor = parents[cursor]
            var path = List[OccurrenceEdge]()
            for k in range(len(reverse)):
                path.append(reverse[len(reverse) - 1 - k])
            if not _replay(tables, seed, path, max_depth).is_coincidence():
                raise Error("internal search witness failed replay")
            return PathSearch(CERTIFIED_LIFTABLE_TARGET_PATH, path, len(states), choices)
        if depths[head] >= max_depth:
            depth_limited = True
            head += 1
            continue
        for i in range(len(tables.sigma[state.top])):
            for j in range(len(tables.sigma[state.bottom])):
                if choices >= max_choices:
                    return PathSearch(BUDGET_EXHAUSTED, empty, len(states), choices)
                choices += 1
                var child = selected_overlap_child(tables, state, i, j)
                if not interior_overlap(tables, child) or child in index:
                    continue
                if len(states) >= max_states:
                    return PathSearch(BUDGET_EXHAUSTED, empty, len(states), choices)
                index[child] = len(states)
                states.append(child)
                depths.append(depths[head] + 1)
                parents.append(head)
                incoming.append(OccurrenceEdge(state, i, j, child))
        head += 1
    var status = DEPTH_COMPLETE_NO_CLOSURE if depth_limited else NO_MATCHED_TARGET_WITHIN_BUDGET
    return PathSearch(status, empty, len(states), choices)


def _validate_pair(pair: Pair) raises:
    validate_word(pair.u, 3)
    validate_word(pair.v, 3)
    if not is_balanced(pair):
        raise Error("matched-target context must be balanced")


def matched_target(pair: Pair, q: Int) raises -> Bool:
    """Delta(q)=0 AND equal next letters, with q strictly before the end."""
    _validate_pair(pair)
    if q < 0 or q >= len(pair.u):
        return False
    if pair.u[q] != pair.v[q]:
        return False
    var delta: List[Int] = [0, 0, 0]
    for k in range(q):
        delta[pair.u[k]] += 1
        delta[pair.v[k]] -= 1
    return delta[0] == 0 and delta[1] == 0 and delta[2] == 0


struct ImageHead(ImplicitlyCopyable, Copyable, Movable):
    var parent_index: Int
    var child_index: Int

    def __init__(out self, parent_index: Int, child_index: Int):
        self.parent_index = parent_index
        self.child_index = child_index


def _head_cut(sigma: Substitution, word: List[Int], head: ImageHead, max_word: Int) raises -> Int:
    if head.parent_index < 0 or head.parent_index >= len(word):
        raise Error("image head has no parent occurrence")
    if head.child_index < 0 or head.child_index >= len(sigma.images[word[head.parent_index]]):
        raise Error("image head has no child occurrence")
    var cut = 0
    for k in range(head.parent_index):
        var n = len(sigma.images[word[k]])
        if n > max_word - cut:
            raise Error("word replay budget exhausted")
        cut += n
    if head.child_index > max_word - cut:
        raise Error("word replay budget exhausted")
    return cut + head.child_index


struct WordEdge(Copyable, Movable):
    var source: Pair
    var top_head: ImageHead
    var bottom_head: ImageHead
    var end: Int
    var target: Pair

    def __init__(out self, source: Pair, top_head: ImageHead, bottom_head: ImageHead, end: Int, target: Pair):
        self.source = source.copy()
        self.top_head = top_head
        self.bottom_head = bottom_head
        self.end = end
        self.target = target.copy()


def _bounded_image(sigma: Substitution, word: List[Int], max_word: Int) raises -> List[Int]:
    var total = 0
    for k in range(len(word)):
        var n = len(sigma.images[word[k]])
        if n > max_word - total:
            raise Error("word replay budget exhausted")
        total += n
    return sigma.apply(word)


def replay_word_path(images: List[List[Int]], seed: Pair, edges: List[WordEdge], max_steps: Int = 10000, max_word: Int = 1000000) raises -> Pair:
    """Inflate, select an actual irreducible balanced child, repeat.

    Full source/target words forbid splicing equal-imbalance contexts. Heads
    locate the selected child in each (possibly unequal-length) image stream.
    """
    if len(images) != 3 or max_steps < 0 or max_word < 1 or len(edges) > max_steps:
        raise Error("invalid word replay domain or exhausted step budget")
    var sigma = Substitution.checked(images)
    _validate_pair(seed)
    if len(seed.u) > max_word:
        raise Error("word replay seed exceeds budget")
    var state = seed.copy()
    for k in range(len(edges)):
        ref edge = edges[k]
        if edge.source != state:
            raise Error("word occurrence path sources do not compose")
        var u = _bounded_image(sigma, state.u, max_word)
        var v = _bounded_image(sigma, state.v, max_word)
        var start = _head_cut(sigma, state.u, edge.top_head, max_word)
        if start != _head_cut(sigma, state.v, edge.bottom_head, max_word):
            raise Error("paired image heads are not aligned")
        if edge.end <= start or edge.end > len(u) or edge.end > len(v):
            raise Error("invalid balanced child interval")
        var cuts = coincidence_boundaries(u, v)
        var found = False
        for c in range(len(cuts) - 1):
            if cuts[c] == start and cuts[c + 1] == edge.end:
                found = True
        if not found:
            raise Error("interval is not an irreducible balanced child")
        var child_u = List[Int]()
        var child_v = List[Int]()
        for q in range(start, edge.end):
            child_u.append(u[q])
            child_v.append(v[q])
        var child = Pair(child_u, child_v)
        if child != edge.target:
            raise Error("word child differs from claimed occurrence")
        state = child^
    return state^


def certify_word_path(images: List[List[Int]], seed: Pair, edges: List[WordEdge], max_steps: Int = 10000, max_word: Int = 1000000) raises:
    var end = replay_word_path(images, seed, edges, max_steps, max_word)
    if len(end.u) != 1 or not matched_target(end, 0):
        raise Error("word path does not finish in a single matched-letter child")
