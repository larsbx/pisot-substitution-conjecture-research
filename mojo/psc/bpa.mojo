"""The balanced-pair automaton B_sigma and its strongly connected components.

States are balanced pairs; the transition is: inflate by sigma, then cut at every
coincidence boundary. Seeds are the length-2 pairs `(ab, ba)`, `a < b`.

Hypothesis G1 (finiteness of `B_sigma`) is *not* proved here: `build` returns a
`capped` flag and callers must treat a capped run as inconclusive, never as a
counterexample or a proof.

The boundary-lineage helpers instrument conjecture C3. They distinguish a
zero-return boundary inherited from the previous inflation from a genuinely
newborn boundary, and test synchronization through the finite prefix/suffix
endpoint maps. These are exact finite diagnostics, not a proof of C3.
"""

from psc.words import Pair, parikh


def apply_substitution(sigma: List[List[Int]], w: List[Int]) -> List[Int]:
    var out = List[Int]()
    for i in range(len(w)):
        ref img = sigma[w[i]]
        for j in range(len(img)):
            out.append(img[j])
    return out^


def inflate_pair(sigma: List[List[Int]], p: Pair) -> Pair:
    """Inflate both sides without cutting into irreducible balanced blocks."""
    return Pair(apply_substitution(sigma, p.u), apply_substitution(sigma, p.v))


def coincidence_boundaries(u: List[Int], v: List[Int]) -> List[Int]:
    """Positions `0 = k_0 < ... < k_m = |u|` where the Parikh prefixes agree."""
    var out: List[Int] = [0]
    var pu: List[Int] = [0, 0, 0]
    var pv: List[Int] = [0, 0, 0]
    for i in range(len(u)):
        pu[u[i]] += 1
        pv[v[i]] += 1
        if pu == pv:
            out.append(i + 1)
    return out^


def _contains_int(xs: List[Int], x: Int) -> Bool:
    for i in range(len(xs)):
        if xs[i] == x:
            return True
    return False


def image_prefix_lengths(sigma: List[List[Int]], w: List[Int]) -> List[Int]:
    """Image length of every prefix `w[:k]`, for `0 <= k <= |w|`."""
    var out: List[Int] = [0]
    for i in range(len(w)):
        out.append(out[len(out) - 1] + len(sigma[w[i]]))
    return out^


def inherited_boundary_positions(
    sigma: List[List[Int]], u: List[Int], v: List[Int]
) -> List[Int]:
    """Next-step zero-return positions inherited from current zero-return cuts."""
    var old = coincidence_boundaries(u, v)
    var upos = image_prefix_lengths(sigma, u)
    var vpos = image_prefix_lengths(sigma, v)
    var out = List[Int]()
    for i in range(len(old)):
        var k = old[i]
        # Balanced prefixes have the same Parikh vector, hence equal image length.
        if upos[k] != vpos[k]:
            print("INTERNAL ERROR: inherited boundary image lengths disagree")
            return List[Int]()
        out.append(upos[k])
    return out^


def newborn_boundary_positions(sigma: List[List[Int]], p: Pair) -> List[Int]:
    """Zero-return cuts created by one inflation rather than inherited."""
    var q = inflate_pair(sigma, p)
    var current = coincidence_boundaries(q.u, q.v)
    var inherited = inherited_boundary_positions(sigma, p.u, p.v)
    var out = List[Int]()
    for i in range(len(current)):
        if not _contains_int(inherited, current[i]):
            out.append(current[i])
    return out^


def prefix_endpoint_map(sigma: List[List[Int]]) -> List[Int]:
    """`sigma_+(a)`: first letter of `sigma(a)`."""
    var out = List[Int]()
    for a in range(len(sigma)):
        out.append(sigma[a][0])
    return out^


def suffix_endpoint_map(sigma: List[List[Int]]) -> List[Int]:
    """`sigma_-(a)`: last letter of `sigma(a)`."""
    var out = List[Int]()
    for a in range(len(sigma)):
        out.append(sigma[a][len(sigma[a]) - 1])
    return out^


def sync_after(h: List[Int], a: Int, b: Int) -> Int:
    """Least endpoint-map iterate at which `a,b` coalesce, or -1 if never.

    For a finite map on `n` letters, `2n+1` transitions are enough to decide
    whether two forward orbits ever meet.
    """
    var x = a
    var y = b
    var bound = 2 * len(h) + 1
    for m in range(bound + 1):
        if x == y:
            return m
        x = h[x]
        y = h[y]
    return -1


def synchronizing_boundary_positions(
    sigma: List[List[Int]], u: List[Int], v: List[Int], positions: List[Int]
) -> List[Int]:
    """Subset of zero-return positions caught by prefix/suffix synchronization."""
    var plus = prefix_endpoint_map(sigma)
    var minus = suffix_endpoint_map(sigma)
    var out = List[Int]()
    for i in range(len(positions)):
        var k = positions[i]
        var hit = False
        if k < len(u) and sync_after(plus, u[k], v[k]) >= 0:
            hit = True
        if k > 0 and sync_after(minus, u[k - 1], v[k - 1]) >= 0:
            hit = True
        if hit:
            out.append(k)
    return out^


def newborn_sync_positions(sigma: List[List[Int]], p: Pair) -> List[Int]:
    """Newborn zero-return cuts whose adjacent endpoint pair synchronizes."""
    var q = inflate_pair(sigma, p)
    var newborn = newborn_boundary_positions(sigma, p)
    return synchronizing_boundary_positions(sigma, q.u, q.v, newborn)


def inherited_sync_positions(sigma: List[List[Int]], p: Pair) -> List[Int]:
    """Inherited zero-return cuts whose adjacent endpoint pair synchronizes."""
    var q = inflate_pair(sigma, p)
    var current = coincidence_boundaries(q.u, q.v)
    var inherited = inherited_boundary_positions(sigma, p.u, p.v)
    var inherited_current = List[Int]()
    for i in range(len(current)):
        if _contains_int(inherited, current[i]):
            inherited_current.append(current[i])
    return synchronizing_boundary_positions(sigma, q.u, q.v, inherited_current)


def _slice(w: List[Int], lo: Int, hi: Int) -> List[Int]:
    var out = List[Int]()
    for i in range(lo, hi):
        out.append(w[i])
    return out^


def decompose(u: List[Int], v: List[Int]) -> List[Pair]:
    """Cut a balanced pair into its irreducible balanced blocks."""
    var bd = coincidence_boundaries(u, v)
    var out = List[Pair]()
    for i in range(len(bd) - 1):
        out.append(Pair(_slice(u, bd[i], bd[i + 1]), _slice(v, bd[i], bd[i + 1])))
    return out^


def normalise(p: Pair) -> Pair:
    """Order the two sides so that `(u, v)` and `(v, u)` are the same state."""
    for i in range(len(p.u)):
        if p.u[i] < p.v[i]:
            return p.copy()
        if p.u[i] > p.v[i]:
            return Pair(p.v, p.u)
    return p.copy()


def children(sigma: List[List[Int]], p: Pair) -> List[Pair]:
    var su = apply_substitution(sigma, p.u)
    var sv = apply_substitution(sigma, p.v)
    var raw = decompose(su, sv)
    var out = List[Pair]()
    for i in range(len(raw)):
        out.append(normalise(raw[i]))
    return out^


def seed_states() -> List[Pair]:
    var out = List[Pair]()
    for a in range(3):
        for b in range(a + 1, 3):
            var u: List[Int] = [a, b]
            var v: List[Int] = [b, a]
            out.append(Pair(u, v))
    return out^


struct Automaton(Copyable, Movable):
    """Reachable part of `B_sigma`: states plus an adjacency list of indices."""

    var states: List[Pair]
    var adj: List[List[Int]]
    var capped: Bool

    def __init__(out self, states: List[Pair], adj: List[List[Int]], capped: Bool):
        self.states = states.copy()
        self.adj = adj.copy()
        self.capped = capped

    def size(self) -> Int:
        return len(self.states)


def build(sigma: List[List[Int]], max_states: Int = 20000) raises -> Automaton:
    var states = List[Pair]()
    var adj = List[List[Int]]()
    var index = Dict[String, Int]()
    var queue = List[Pair]()
    var capped = False

    var seeds = seed_states()
    for i in range(len(seeds)):
        queue.append(normalise(seeds[i]))

    var head = 0
    while head < len(queue):
        var s = queue[head].copy()
        head += 1
        var k = s.key()
        if k in index:
            continue
        if len(states) >= max_states:
            capped = True
            break
        index[k] = len(states)
        states.append(s.copy())
        adj.append(List[Int]())
        if s.is_coincidence():
            continue
        var cs = children(sigma, s)
        for i in range(len(cs)):
            queue.append(cs[i].copy())

    if capped:
        return Automaton(states, adj, True)

    # second pass: edges, now that every reachable state has an index
    for i in range(len(states)):
        if states[i].is_coincidence():
            continue
        var cs = children(sigma, states[i])
        for j in range(len(cs)):
            var ck = cs[j].key()
            if ck in index:
                adj[i].append(index[ck])
    return Automaton(states, adj, False)


def sccs(a: Automaton) -> List[List[Int]]:
    """Tarjan's algorithm, iterative (no recursion-depth limit)."""
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


def has_cycle(a: Automaton, comp: List[Int]) -> Bool:
    if len(comp) > 1:
        return True
    var v = comp[0]
    for i in range(len(a.adj[v])):
        if a.adj[v][i] == v:
            return True
    return False


def is_noncoincident(a: Automaton, comp: List[Int]) -> Bool:
    for i in range(len(comp)):
        if a.states[comp[i]].is_coincidence():
            return False
    return True


def recurrent_noncoincident_sccs(a: Automaton) -> List[List[Int]]:
    var all = sccs(a)
    var out = List[List[Int]]()
    for i in range(len(all)):
        if has_cycle(a, all[i]) and is_noncoincident(a, all[i]):
            out.append(all[i].copy())
    return out^


def nonproductive_states(a: Automaton) -> List[Int]:
    """Indices of states from which no coincidence pair is reachable.

    Emptiness of this list is the SCC Producer property (`conj:producer`) for
    the reachable part of `B_sigma`. It is a conjecture in general: an empty
    result for one sigma eliminates counterexamples, it does not prove the
    conjecture.
    """
    var n = a.size()
    var good = List[Bool]()
    for i in range(n):
        good.append(a.states[i].is_coincidence())
    # backwards closure over the reverse graph, to a fixpoint
    var changed = True
    while changed:
        changed = False
        for i in range(n):
            if good[i]:
                continue
            for j in range(len(a.adj[i])):
                if good[a.adj[i][j]]:
                    good[i] = True
                    changed = True
    var out = List[Int]()
    for i in range(n):
        if not good[i]:
            out.append(i)
    return out^


def substitution_incidence(sigma: List[List[Int]]) -> List[Int]:
    """`M[i][j]` = number of occurrences of letter `i` in `sigma(j)`, row-major."""
    var e = List[Int]()
    for i in range(3):
        for j in range(3):
            var c = 0
            for p in range(len(sigma[j])):
                if sigma[j][p] == i:
                    c += 1
            e.append(c)
    return e^
