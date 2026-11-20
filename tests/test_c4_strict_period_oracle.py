"""Independent literal child rows, complete cut replays, and simple-cycle periods."""

from collections import Counter
from itertools import combinations, product
from math import gcd


def expand(sigma, word, depth=1):
    for _ in range(depth):
        word = "".join(sigma[int(a)] for a in word)
    return word


def cuts(top, bottom):
    assert len(top) == len(bottom)
    diff = [0, 0, 0]
    yield 0
    for i, (a, b) in enumerate(zip(top, bottom, strict=True), 1):
        diff[int(a)] += 1
        diff[int(b)] -= 1
        if diff == [0, 0, 0]:
            yield i


def row(sigma, pair, depth=1):
    top, bottom = (expand(sigma, word, depth) for word in pair)
    positions = list(cuts(top, bottom))
    assert positions[-1] == len(top)
    return [(a, b, (top[a:b], bottom[a:b])) for a, b in zip(positions, positions[1:])]


def graph(sigma, states, ordered):
    vertices = set(states)
    if ordered:
        vertices.update((b, a) for a, b in states)
    children = {}
    for parent in vertices:
        assert list(cuts(*parent)) == [0, len(parent[0])]
        assert parent[0] != parent[1]
        children[parent] = {pair if ordered else tuple(sorted(pair))
                            for _, _, pair in row(sigma, parent)}
        assert children[parent] and children[parent] <= vertices
    return children


def periods(children):
    def reachable(root):
        queue = [root]
        seen = {root}
        for v in queue:
            for w in children[v] - seen:
                seen.add(w)
                queue.append(w)
        return seen

    def simple_cycles(root, path):
        for w in children[path[-1]]:
            if w == root:
                yield len(path)
            elif w not in path:
                yield from simple_cycles(root, (*path, w))

    remaining = set(children)
    result = []
    while remaining:
        root = min(remaining)
        component = {v for v in reachable(root) if root in reachable(v)}
        assert all(children[v] <= component for v in component)
        result.append(gcd(*(n for v in component for n in simple_cycles(v, (v,)))))
        remaining -= component
    return sorted(result)


def test_cross_pair_cycle_has_a_common_enclosed_factor_and_period_one():
    sigma = ("01", "201", "112")
    states = (("012", "201"), ("01112", "20111"), ("01201112", "11201201"),
              ("01201201201112", "11201201201201"))
    first, second = states[0], states[2]
    assert row(sigma, first)[0][2] == second
    assert row(sigma, second)[0][2] == first
    first_leaf, second_leaf = (expand(sigma, c, 4) for c in "12")
    assert first_leaf[7] == second_leaf[7] == "1"
    assert Counter(first_leaf[:7]) == Counter(second_leaf[:7])
    start = len(expand(sigma, first_leaf[:7], 3))
    end = start + len(expand(sigma, "1", 3))
    assert (start, end) == (142, 164)
    assert end < len(expand(sigma, "0", 7))
    for pair in (first, second):
        assert (145, 150, states[1]) in row(sigma, pair, 7)
    assert periods(graph(sigma, states, False)) == [1]
    assert periods(graph(sigma, states, True)) == [1, 1]


def test_phase_one_has_primitive_normalized_and_period_two_ordered_rows():
    sigma = ("1", "012", "1")
    states = (("01", "10"), ("12", "21"))
    assert sigma[0] == sigma[2] == "1"  # Witnessed on both ends.
    normalized = graph(sigma, states, False)
    ordered = graph(sigma, states, True)
    assert periods(normalized) == [1]
    assert periods(ordered) == [2]
    for (u, v), children in ordered.items():
        for a, b in children:
            for i in (0, -1):
                assert (a[i] == "1", b[i] == "1") == (v[i] == "1", u[i] == "1")


def test_every_viable_cyclic_endpoint_pair_and_good_edge():
    counts = Counter()
    for f in product(range(3), repeat=3):
        for good in combinations(range(3), 2):
            for root in combinations(range(3), 2):
                pair = root
                visited = set()
                while (pair not in visited and pair[0] != pair[1]
                       and tuple(sorted(pair)) != good):
                    visited.add(pair)
                    pair = tuple(f[a] for a in pair)
                if pair != root or not visited:
                    continue
                ordered = len(visited)
                unordered = len({tuple(sorted(p)) for p in visited})
                counts[unordered, ordered] += 1
                if unordered == 2:
                    hub = next(a for a in range(3) if a not in good)
                    assert f[hub] == hub and f[good[0]] == good[1] and f[good[1]] == good[0]
    assert counts == {(1, 1): 18, (1, 2): 18, (2, 2): 6}


def overlap_periods(sigma, states, widths, ordered):
    """Generate actual positive overlaps in Q(sqrt(3)) with full integer keys."""
    from itertools import accumulate

    def positive(vector):
        a, b = (sum(c * width[i] for c, width in zip(vector, widths, strict=True))
                for i in range(2))
        if b == 0:
            return a > 0
        if b < 0:
            return a > 0 and a * a > 3 * b * b
        return a >= 0 or 3 * b * b > a * a

    def add_letter(vector, letter, sign):
        return tuple(x + sign * (str(i) == letter) for i, x in enumerate(vector))

    def minus(u, v):
        return tuple(a - b for a, b in zip(u, v, strict=True))

    def keys(top, bottom, shift):
        prefixes = [list(accumulate(word, add_letter_positive, initial=(0, 0, 0)))
                    for word in (top, bottom)]
        for i, a in enumerate(top):
            for j, b in enumerate(bottom):
                w = minus(prefixes[1][j], prefixes[0][i])
                w = tuple(a + b for a, b in zip(w, shift, strict=True))
                if positive(add_letter(w, b, 1)) and positive(add_letter(tuple(-x for x in w), a, 1)):
                    key = a, b, w
                    yield key if ordered else min(key, (b, a, tuple(-x for x in w)))

    def add_letter_positive(vector, letter):
        return add_letter(vector, letter, 1)

    pairs = set(states)
    if ordered:
        pairs |= {(b, a) for a, b in states}
    vertices = {key for u, v in pairs for key in keys(u, v, (0, 0, 0))}
    columns = [Counter(word) for word in sigma]
    children = {}
    for a, b, w in vertices:
        shift = tuple(sum(x * counts[str(c)] for x, counts in zip(w, columns, strict=True))
                      for c in range(3))
        children[a, b, w] = set(keys(sigma[int(a)], sigma[int(b)], shift))
        assert children[a, b, w] and children[a, b, w] <= vertices

    parents = {v: set() for v in vertices}
    for v, targets in children.items():
        for t in targets:
            parents[t].add(v)
    result = []
    while vertices:
        root = min(vertices)
        depth = {root: 0}
        queue = [root]
        for v in queue:
            for t in children[v]:
                if t not in depth:
                    depth[t] = depth[v] + 1
                    queue.append(t)
        reverse = [root]
        reverse_seen = {root}
        for v in reverse:
            for p in parents[v] - reverse_seen:
                reverse_seen.add(p)
                reverse.append(p)
        assert depth.keys() == reverse_seen and reverse_seen <= vertices
        result.append(gcd(*(depth[v] + 1 - depth[t] for v in depth for t in children[v])))
        vertices -= depth.keys()
    return sorted(result)


def test_actual_overlap_graphs_have_their_literal_child_periods():
    cross = (("01", "201", "112"),
             (("012", "201"), ("01112", "20111"), ("01201112", "11201201"),
              ("01201201201112", "11201201201201")),
             ((1, 0), (0, 1), (2, 0)))
    flip = (("1", "012", "1"), (("01", "10"), ("12", "21")),
            ((1, 0), (2, 0), (1, 0)))
    for case in (cross, flip):
        for ordered in (False, True):
            sigma, states, _ = case
            assert overlap_periods(*case, ordered) == periods(graph(sigma, states, ordered))
