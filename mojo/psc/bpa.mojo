"""The balanced-pair automaton B_sigma and its strongly connected components.

States are balanced pairs; the transition is: inflate by sigma, then cut at every
coincidence boundary. Seeds are the length-2 pairs `(ab, ba)`, `a < b`.

Hypothesis G1 (finiteness of `B_sigma`) is *not* proved here: `build` returns a
`capped` flag and callers must treat a capped run as inconclusive, never as a
counterexample or a proof.
"""

from psc.words import Pair, parikh


def apply_substitution(sigma: List[List[Int]], w: List[Int]) -> List[Int]:
    var out = List[Int]()
    for i in range(len(w)):
        ref img = sigma[w[i]]
        for j in range(len(img)):
            out.append(img[j])
    return out^


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
