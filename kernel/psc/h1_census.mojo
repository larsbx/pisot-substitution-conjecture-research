"""Rank of the first Cech cohomology of a one-dimensional substitution tiling
space, through the Barge-Diamond complex, and its census over the PIP corpus.

Barge-Diamond 2008 (Theorem 4; Barge 2015 writes it as the exact sequence
(4.1) `0 -> G0 -> G1 -> G2 -> G3 -> 0`): for a primitive aperiodic
substitution, `G1 = lim M^T`, `G2 = H^1(Omega_sigma; Q)`, `G0 = Q^{k-1}` where
`k` is the number of connected components of the eventual range `ER` of the
induced map `f` on the vertex-edge graph `S`, and `G3 = lim H^1(S) = H^1(ER)`.
The vertex-edge graph has vertices `x^+` (right end of the tile `x`) and `y^-`
(left end of `y`), one edge `e_{xy}: x^+ -> y^-` per legal two-letter word
`xy`, and `f(e_{xy}) = e_{last(sigma x) first(sigma y)}`. `G3 = H^1(ER)` is the
step of the Barge-Diamond proof in which `f` permutes the edges of `ER`, so a
power of `f` is homotopic to the identity on `ER` and the eventual range of
`f*` on `H^1(S)` is `H^1(ER)`. Over `Q`, with `b1(ER) = E - V + k`,

    dim H^1(Omega_sigma; Q) = evrank(M^T) + E(ER) - V(ER) + 1,

for any number `k` of components. Legal two-letter words are the closure of
the two-factors of the images under `xy -> last(sigma x) first(sigma y)`, which
equals the set of legal two-letter words of a primitive substitution. On the
corpus every incidence matrix is nonsingular (irreducible cubic), so
`evrank = 3` and `dim H^1 = 3 + l` with `l = b1(ER)` the asymptotic-cycle rank.

Everything is integer arithmetic on finite graphs plus one exact rational
rank. A malformed substitution, a one-letter alphabet or a non-primitive
incidence matrix raises (the theorem needs primitivity; aperiodicity holds on
the corpus because the Perron root is an irrational cubic). The check that
`f` permutes the edges of `ER` is a defensive invariant: on a finite set the
stable set of a self-map is always permuted, so it cannot fail.

What the census means (docs/c4-h1-census-2026-11-05.md): by Barge 2015
Theorem 22 (norm odd and coincidence rank 2 imply `dim H^1 >= 2d - 1 = 5`),
a unimodular specimen with `dim H^1 <= 4` has coincidence rank different
from 2; the determinant-2 specimens have even norm and Theorem 22 says
nothing about them. The census certifies no pure discrete spectrum, bounds no
coincidence rank from above, and changes no claim status.
"""

from finite_exact.rat_q import Q
from finite_linear_algebra.integer_matrix import is_primitive, matmul
from finite_linear_algebra.qlinalg import rank
from finite_linear_algebra.scalar import q_int
from psc.corpus import Specimen
from psc.endpoint_core import ENDPOINT_TYPE_COUNT, endpoint_type, prefix_endpoint_map, suffix_endpoint_map
from psc.histogram import Histogram
from substitution_dynamics.substitution import Substitution

comptime MAX_LETTERS = 8
comptime MAX_DIMENSION = 32


def _validate(sigma: List[List[Int]]) raises:
    var n = len(sigma)
    if n < 2 or n > MAX_LETTERS:
        raise Error("alphabet size must lie in 2..8")
    for a in range(n):
        if len(sigma[a]) == 0:
            raise Error("substitution image is empty")
        for k in range(len(sigma[a])):
            if sigma[a][k] < 0 or sigma[a][k] >= n:
                raise Error("substitution letter outside the alphabet")


def _first(sigma: List[List[Int]], x: Int) -> Int:
    return sigma[x][0]


def _last(sigma: List[List[Int]], x: Int) -> Int:
    return sigma[x][len(sigma[x]) - 1]


def incidence_rows(sigma: List[List[Int]]) raises -> List[Int]:
    """Row-major incidence `M[i][j]` = occurrences of `i` in `sigma(j)`, after
    validation and the primitivity guard the theorem requires."""
    _validate(sigma)
    var n = len(sigma)
    var m = Substitution(sigma.copy(), n).incidence()
    if not is_primitive(m, n):
        raise Error("incidence matrix is not primitive: the Barge-Diamond theorem does not apply")
    return m^


def legal_two_words(sigma: List[List[Int]]) raises -> List[Bool]:
    """Membership mask, index `n * x + y`, of the legal two-letter words."""
    _validate(sigma)
    var n = len(sigma)
    var legal = List[Bool](length=n * n, fill=False)
    for x in range(n):
        for k in range(len(sigma[x]) - 1):
            legal[n * sigma[x][k] + sigma[x][k + 1]] = True
    var changed = True
    while changed:
        changed = False
        for x in range(n):
            for y in range(n):
                if legal[n * x + y]:
                    var j = n * _last(sigma, x) + _first(sigma, y)
                    if not legal[j]:
                        legal[j] = True
                        changed = True
    return legal^


def eventual_range(sigma: List[List[Int]], legal: List[Bool]) raises -> List[Bool]:
    """Edges of the eventual range of `f(e_{xy}) = e_{last(sigma x) first(sigma y)}`:
    the stable set of the decreasing chain `f^n(legal)`."""
    var n = len(sigma)
    var current = legal.copy()
    for _ in range(n * n + 1):
        var following = List[Bool](length=n * n, fill=False)
        for x in range(n):
            for y in range(n):
                if current[n * x + y]:
                    following[n * _last(sigma, x) + _first(sigma, y)] = True
        if following == current:
            return current^
        current = following^
    raise Error("eventual range did not stabilise")


def _count(mask: List[Bool]) -> Int:
    var c = 0
    for k in range(len(mask)):
        if mask[k]:
            c += 1
    return c


def _find(mut parent: List[Int], v: Int) -> Int:
    var r = v
    while parent[r] != r:
        r = parent[r]
    var w = v
    while parent[w] != r:
        var next = parent[w]
        parent[w] = r
        w = next
    return r


def graph_shape(mask: List[Bool], n: Int) -> List[Int]:
    """`[edges, vertices, components]` of the subgraph of `S` with the given
    edges; vertices `x^+` are `x`, vertices `y^-` are `n + y`."""
    var edges = 0
    var used = List[Bool](length=2 * n, fill=False)
    var parent = List[Int](capacity=2 * n)
    for v in range(2 * n):
        parent.append(v)
    for x in range(n):
        for y in range(n):
            if mask[n * x + y]:
                edges += 1
                used[x] = True
                used[n + y] = True
                var a = _find(parent, x)
                var b = _find(parent, n + y)
                if a != b:
                    parent[a] = b
    var vertices = 0
    var components = 0
    for v in range(2 * n):
        if used[v]:
            vertices += 1
            if _find(parent, v) == v:
                components += 1
    return [edges, vertices, components]


def eventual_rank(sigma: List[List[Int]]) raises -> Int:
    """Rank over `Q` of `M^n`, `n` the alphabet size: the eventual rank of the
    incidence matrix, which equals that of its transpose."""
    var n = len(sigma)
    var m = incidence_rows(sigma)
    var power = m.copy()
    for _ in range(n - 1):
        power = matmul(power, m, n)
    var rows = List[List[Q]]()
    for i in range(n):
        var row = List[Q]()
        for j in range(n):
            row.append(q_int(power[n * i + j]))
        rows.append(row^)
    return rank(rows)


struct H1Profile(Copyable, Movable):
    var dimension: Int
    var eventual_rank: Int
    var edges: Int
    var vertices: Int
    var components: Int
    var legal_words: Int

    def __init__(out self, dimension: Int, eventual_rank: Int, edges: Int, vertices: Int, components: Int, legal_words: Int):
        self.dimension = dimension
        self.eventual_rank = eventual_rank
        self.edges = edges
        self.vertices = vertices
        self.components = components
        self.legal_words = legal_words


def h1_profile(sigma: List[List[Int]]) raises -> H1Profile:
    """`dim H^1(Omega_sigma; Q)` with the data it is computed from."""
    var ev = eventual_rank(sigma)
    var n = len(sigma)
    var legal = legal_two_words(sigma)
    var er = eventual_range(sigma, legal)
    var image = List[Bool](length=n * n, fill=False)
    for x in range(n):
        for y in range(n):
            if er[n * x + y]:
                var j = n * _last(sigma, x) + _first(sigma, y)
                if image[j]:
                    raise Error("f is not injective on the eventual range (impossible for a stable set)")
                image[j] = True
    var shape = graph_shape(er, n)
    return H1Profile(ev + shape[0] - shape[1] + 1, ev, shape[0], shape[1], shape[2], _count(legal))


def endpoint_cell(sigma: List[List[Int]]) -> Int:
    """`7 * type(sigma_+) + type(sigma_-)`, the joint endpoint-type cell A..G x A..G."""
    return ENDPOINT_TYPE_COUNT * endpoint_type(prefix_endpoint_map(sigma)) + endpoint_type(suffix_endpoint_map(sigma))


struct H1Census(Copyable, Movable):
    """Per-specimen `dim H^1` over a corpus, folded into order-independent
    tables: all specimens; by determinant (`determinant_dimension`, key
    `32 * (det + 8) + dim`, so `det` in `-8..7`); by joint endpoint-type cell
    (`endpoint_dimension`, key `32 * cell + dim`); the `(edges, vertices)`
    shape of the eventual range (`shapes`, key `16 * edges + vertices`)."""

    var dimensions: Histogram
    var unimodular: Histogram
    var determinant_dimension: Histogram
    var endpoint_dimension: Histogram
    var shapes: Histogram
    var disconnected: Int
    var total: Int

    def __init__(out self):
        self.dimensions = Histogram(MAX_DIMENSION)
        self.unimodular = Histogram(MAX_DIMENSION)
        self.determinant_dimension = Histogram(16 * MAX_DIMENSION)
        self.endpoint_dimension = Histogram(ENDPOINT_TYPE_COUNT * ENDPOINT_TYPE_COUNT * MAX_DIMENSION)
        self.shapes = Histogram(512)
        self.disconnected = 0
        self.total = 0

    def determinant_count(self, det: Int, dimension: Int) -> Int:
        return self.determinant_dimension.count(MAX_DIMENSION * (det + 8) + dimension)

    def endpoint_count(self, plus: Int, minus: Int, dimension: Int) -> Int:
        return self.endpoint_dimension.count(MAX_DIMENSION * (ENDPOINT_TYPE_COUNT * plus + minus) + dimension)


def h1_census(corpus: List[Specimen]) raises -> H1Census:
    var out = H1Census()
    for s in range(len(corpus)):
        var profile = h1_profile(corpus[s].sigma)
        out.dimensions.record(profile.dimension)
        var det = corpus[s].incidence.det()
        if det < -8 or det > 7:
            raise Error("determinant outside the census table")
        if det == 1 or det == -1:
            out.unimodular.record(profile.dimension)
        out.determinant_dimension.record(MAX_DIMENSION * (det + 8) + profile.dimension)
        out.endpoint_dimension.record(MAX_DIMENSION * endpoint_cell(corpus[s].sigma) + profile.dimension)
        out.shapes.record(16 * profile.edges + profile.vertices)
        if profile.components != 1:
            out.disconnected += 1
        out.total += 1
    return out^
