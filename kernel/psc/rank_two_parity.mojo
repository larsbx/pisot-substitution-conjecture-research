"""The divisor condition of Theorem P+ (rank-two parity), decided exactly,
and its census over the PIP corpus.

docs/c4-rank-two-wall-2026-11-16.md, Lemma S+ and Theorem P+ (§7);
docs/c4-geometric-f-class-2026-11-16.md, Lemma 7 (§5.1). Standing class
PIP3: a primitive substitution `sigma` on `{0,1,2}` whose incidence matrix
`M` (`M[a][b] = |sigma(b)|_a`) has an irreducible characteristic polynomial
`chi_M` with a Pisot Perron root (nonunit allowed). `g` and `g_R` are the
first- and last-letter maps; a word is *legal* if it is a factor of some
`sigma^k(c)`.

What the note defines, and what is computed here
------------------------------------------------
- *The eventual range and the action.* Barge--Diamond's complex has one
  transition edge `e_ab: a^+ -> b^-` per legal two-letter word `ab`, and the
  map `g_K(e_ab) = e_{g_R(a) g(b)}`. `ER` is its eventual range; by Lemma 7(1)
  it consists of the `e_ab` with `ab` legal, `a` periodic under `g_R` and `b`
  periodic under `g`, and `g_K` permutes it. `ERGraphMap` is `f := g_K|ER` as
  a graph map: the edges and vertices of `ER` exactly as
  `psc.h1_census.legal_two_words`, `eventual_range` and `graph_shape` compute
  them (on `k` letters an edge `e_ab` has code `k a + b`; the vertex `a^+`
  has code `a`, the vertex `b^-` has code `k + b`; `k = 3` for PIP3; the
  graph level accepts the 2..8 letters of `psc.h1_census`, so that
  Thue--Morse and the singular controls can be computed), and the images
  `a^+ -> g_R(a)^+`,
  `b^- -> g(b)^-`, `e_ab -> e_{g_R(a) g(b)}`.
- `c_n` is the characteristic polynomial of `(g_K^n)*` on `H^1(ER; Q)`, of
  degree `l = dim H^1(Omega; Q) - 3` (Lemma 7(3)): `er_charpoly`.
- `n >= 1` is *admissible* if some legal word `ba` has `g_R^n(b) = b` and
  `g^n(a) = a` (the note, §1): `is_admissible`, from that definition.
- `h_n` is the part prime to `t` of `chi_{M^n} mod 2`: `h_polynomial`.
  `d_2 = 3 - ord_t(chi_M mod 2) = deg h_n` for every `n`.
- *The divisor condition* (Theorem P+, item 2): for every admissible `n`
  there are monic `r, q_1` in `Z[t]` with `r q_1 | c_n` and
  `h_n rbar = (t + 1) q_1bar` in `F_2[t]` (a bar is reduction mod 2).
  `divisor_profile` decides it for one substitution; `divisor_search` is the
  search at one `n`.

Proposition C (the formula for `c_n`, with its proof)
-----------------------------------------------------
Let `Gamma` be a finite connected graph with vertex set `V` and oriented edge
set `E`, and `f` a graph automorphism preserving orientations: bijections
`f_V`, `f_E` with `source(f_E e) = f_V(source e)` and
`target(f_E e) = f_V(target e)`. Then for every `n >= 1`

    charpoly((f^n)* | H^1(Gamma; Q))  =  (t - 1) charpoly(P_E^n) / charpoly(P_V^n)
                                      =  (t - 1) prod_{edge cycles of f^n} (t^L - 1)
                                                 / prod_{vertex cycles of f^n} (t^L - 1),

where `P_E`, `P_V` are the permutation matrices of `f_E`, `f_V`.

*Proof.* Cellular cochains `C^0 = Q^V`, `C^1 = Q^E`,
`(delta phi)(e) = phi(target e) - phi(source e)`; the pull-back
`(f^# phi)(x) = phi(f(x))` commutes with `delta` because `f` preserves
sources and targets. So `0 -> H^0 -> C^0 -> C^1 -> H^1 -> 0` is an exact
sequence of `Q[f^#]`-modules. Characteristic polynomials multiply along short
exact sequences (a block-triangular matrix in an adapted basis); splitting
at `B = delta(C^0)` gives `chi_{C^0} = chi_{H^0} chi_B` and
`chi_{C^1} = chi_B chi_{H^1}`, so `chi_{H^1} = chi_{H^0} chi_{C^1} / chi_{C^0}`.
`Gamma` is connected, so `H^0` is the constants, on which `f^#` is the
identity: `chi_{H^0} = t - 1`. On `C^0` and `C^1` the pull-back is a
permutation matrix (of `f^{-1}` in the standard basis), whose characteristic
polynomial is `prod over cycles (t^L - 1)`, the same for a permutation and
its inverse. Apply this to `f^n`; a cycle of length `L` of `f` splits into
`gcd(L, n)` cycles of length `L / gcd(L, n)` of `f^n`. QED.

`f = g_K|ER` satisfies the hypotheses when `ER` is connected (Lemma 7(2), for
PIP3) and `f` permutes its edges and vertices (Lemma 7(1)); it preserves
orientations because it maps `^+` vertices to `^+` vertices and `^-` to `^-`.
`graph_map_on` refuses a disconnected edge set and a map that is not a
permutation of the edges or of the vertices: on a disconnected graph
`H^0` is not `Q` and the formula is false (Barge--Diamond's `G_0 != 0`; every
reducible control of the brief is refused this way). Since
`t^L - 1 = prod_{d | L} Phi_d`, the factorisation into cyclotomic
polynomials is read off the cycle type: the exponent of `Phi_d` in `c_n` is

    [d = 1] + #{edge cycles of f^n of length divisible by d}
            - #{vertex cycles of f^n of length divisible by d},

which is never negative (unique factorisation; a negative value raises).
`er_charpoly` computes `c_n` by exact polynomial division (a nonzero
remainder raises), `cyclotomic_exponents` from the cycle type, and
`cyclotomic_factorisation` by trial division of `c_n` by `Phi_d` for every
`d` with `phi(d) <= deg` (`phi(d) >= sqrt(d / 2)`, so `d <= 2 deg^2`), with
no cycle type; `divisor_profile` requires the three to agree. The regression
recomputes `c_n` once more from the Lefschetz traces
`1 - #Fix_V(f^m) + #Fix_E(f^m)` by Newton's identities.

The search is exhaustive
------------------------
`c_n = prod_d Phi_d^{e_d}` is monic. In the unique factorisation domain
`Z[t]` the `Phi_d` are irreducible (irreducible over `Q` and primitive) and
the units are `+-1`. If `r, q_1` are monic and `r q_1 s = c_n` in `Z[t]`,
then `r = +-prod Phi_d^{a_d}`, `q_1 = +-prod Phi_d^{b_d}` with
`a_d + b_d <= e_d`, and monic fixes the sign `+`; conversely every such pair
is a pair of monic divisors with `r q_1 | c_n` (and their roots are roots of
unity, as Lemma S+(4) adds). Divisibility of monic polynomials over `Q` and
over `Z` agree (Gauss). So `divisor_search` enumerates exactly the candidates
of the theorem: every pair of sub-multisets `(a_d), (b_d)` with
`a_d + b_d <= e_d`, in a fixed order (support `d` increasing, the options of
one `d` in lexicographic order of `(a_d, b_d)`, the last `d` varying
fastest), and tests `h_n rbar = (t + 1) q_1bar` in `F_2[t]`. It returns the
first witness, or none after `prod_d (e_d + 1)(e_d + 2)/2` candidates.

Which `n` (the finite set, with its proof)
------------------------------------------
*Lemma N.* For `sigma` in PIP3 and `n >= 1`, admissibility of `n`, `c_n` and
`h_n` depend only on `n mod 42`.

*Proof.* (i) A legal `ba` with `g_R^n(b) = b`, `g^n(a) = a` has `b`, `a`
periodic, so `e_ba` is an edge of `ER` (Lemma 7(1)) fixed by `f^n`;
conversely an edge of `ER` fixed by `f^n` is such a word. So `n` is
admissible iff `f^n` fixes an edge of `ER`. The order `p` of `f` on `ER`
divides 6 (Lemma 7(1): on three letters the periodic parts of `g`, `g_R` have
cycles of length 1, 2 or 3; `divisor_profile` checks `p | 6` and raises
otherwise). So `f^{n + 42} = f^n` on `ER`: the fixed edges and, by
Proposition C, `c_n` agree at `n` and `n + 42`. (ii) `chi_{M^n} mod 2` is the
characteristic polynomial of `A^n`, `A = M mod 2` (reduction commutes with
products and with the determinant). Over an algebraic closure of `F_2`, `A`
is triangularisable with eigenvalues `mu_1, mu_2, mu_3`, and `A^n` has the
eigenvalues `mu_i^n`. A nonzero `mu_i` has a minimal polynomial over `F_2` of
degree `k` in `{1, 2, 3}` (a factor of a cubic), so `mu_i^{2^k - 1} = 1` and
its order divides 1, 3 or 7, hence 21; and `0^n = 0` for `n >= 1`. So
`chi_{A^{n + 21}} = chi_{A^n}` for `n >= 1`, and `h_n` with it. QED.

So "for every admissible `n`" is decided exactly by `n = 1, ..., 42`
(`ADMISSIBLE_PERIOD`), every residue mod 42 once, and the least failing `n`
in that range is the least failing admissible `n` overall. `n = 6` is always
admissible (Lemma 7(1)). The regression checks Lemma N on every corpus
specimen (the data at `n` and `n + 42` agree for `n = 1..42`); it does not
replace the proof.

Elementary consequences, checked by the regression on every specimen
---------------------------------------------------------------------
(i) *Degree count* (the note's proof of item 1): a witness has
`d_2 + deg r = 1 + deg q_1` and `deg r + deg q_1 <= l`, so `l >= |d_2 - 1|`;
if `dim H^1 < 3 + |d_2 - 1|`, every admissible `n` fails. (ii) `d_2 = 1`:
`chi_M = t^2 (t + 1) mod 2`, `h_n = t + 1`, and `r = q_1 = 1` is a witness at
every `n`: the condition never fails. (iii) Odd determinant, `n = 6`:
`c_6 = (t - 1)^l` (Lemma 7(3)), and the condition fails iff `l <= 1` or
`tr M != e_2(M) mod 2`: this is the proof of Theorem P of the (F)-class
note. So for odd determinant the content beyond Theorem P and Barge 2015
Thm 22 comes from the admissible `n` not divisible by 6.

`F_2[t]` arithmetic
-------------------
A polynomial over `F_2` is a bit mask, bit `i` the coefficient of `t^i`
(`f2_mul` is the carry-less product, `f2_strip_t` removes the factors `t`).
`A^n` is computed over `F_2` (entries in `{0, 1}`, products are AND, sums
are XOR) and `chi_A = t^3 + tr(A) t^2 + e_2(A) t + det(A)`: the signs of
`chi = t^3 - tr t^2 + e_2 t - det` vanish mod 2, and `tr`, `e_2`, `det` are
integer polynomials in the entries, so their values mod 2 are the parities
of `tr M`, `e_2(M)`, `det M` at `n = 1`. The regression compares `h_n` with
the vendored `Mat3.charpoly` of the checked integer power `M^n`, reduced mod
2, on every specimen for `n = 1..8` (every residue mod 3 and mod 7).

The census
----------
`rank_two_parity_census` walks `pip_corpus()` once and folds per-specimen
facts into `psc.histogram` tables keyed by the `CELL_*` bits: the divisor
condition fails (`CELL_FAILS`); `det M` odd; (F) holds
(`psc.c4_geometric_f.decide_geometric_f_with`, the canonical exact
decision); both endpoint maps have at least two periodic letters
(`CELL_TWO_PERIODIC`, clause (a') of Theorem FC3 fails); the dimension bound
of Theorem P+ holds (`dim H^1 >= 3 + |d_2 - 1|`); the hypotheses of the
recorded conditional theorems *without* the divisor condition hold
(`CELL_PRIOR`, `FC3Profile.rank_two_hypotheses_hold`: odd determinant and
`dim H^1 <= 4` or `tr M != e_2(M) mod 2`; even determinant and
`dim H^1 = 3`); `tr M != e_2(M) mod 2`. `d_2` and `dim H^1` are recomputed by
`psc.c4_geometric_f.fc3_profile_of` and must agree (else raise). The open
classes of §15.3 item 1 of the closure-attempt note are (F), two periodic
letters on both sides, and not `CELL_PRIOR`.

What the counts mean
--------------------
These are class counts under a recorded conditional theorem. Theorem P+ is a
written proof conditional on its imports (Barge 2015 as printed: the proper
version, Thm 4(5), Thm 5, Thm 12, Lemmas 13--14, Prop. 19, Lemma 20 and the
count of periodic words in the proof of Thm 22; Barge--Diamond 2008 Thm 4
with its proof and Thm 4'; the identification of the two coincidence ranks),
single prover plus independent adversarial re-derivation within one session,
not machine-checked, independent human review pending. A specimen on which
the divisor condition fails is one on which that theorem, if its imports
hold, excludes coincidence rank 2. It is not a certificate of a coincidence
rank: no coincidence rank, strong coincidence or spectrum is computed here,
and no claim status changes. On the corpus no strict system exists by other
means (`C4StandingCorpus`), so these counts locate the classes the theorem
reaches; they are not open cases.

Fail closed
-----------
Refuse to conclude, with a message: a substitution that is not PIP3
(`divisor_profile`: not three letters, not primitive, reducible
characteristic polynomial, non-Pisot Perron root; malformed images through
`psc.h1_census`); a disconnected edge set; an edge set that `f` leaves or
does not permute; a power below one; an inexact polynomial division; a
negative cyclotomic exponent; a polynomial that is not a product of
cyclotomic polynomials, or whose trial division would need an index beyond
`MAX_CYCLOTOMIC_INDEX`; an `F_2` product beyond 62 bits; disagreement between
the cycle-type and trial-division factorisations, between admissibility from
the definition and from the fixed edges of `f^n`, between `deg c_n` and
`dim H^1 - 3`, between `deg h_n` and `d_2`, or between this module's and
`psc.c4_geometric_f`'s `d_2` and `dim H^1`; an order of `f` on `ER` that does
not divide 6. Every integer polynomial operation is checked
(`finite_exact.checked_int`). No floating point is used. `Mat3.charpoly`
(unchecked) is used only in the PIP3 gate, on the incidence matrix itself.
"""

from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from finite_exact.integer_gcd import gcd_int
from finite_linear_algebra.mat3 import Mat3
from psc.c4_geometric_f import (
    PrototileMap,
    StableRadiiCache,
    decide_geometric_f_with,
    fc3_profile_of,
)
from psc.corpus import Specimen
from psc.endpoint_core import prefix_endpoint_map, suffix_endpoint_map
from psc.h1_census import eventual_range, graph_shape, h1_profile, incidence_rows, legal_two_words
from psc.histogram import Histogram
from psc.pisot import is_irreducible_cubic, is_pisot_charpoly

comptime ADMISSIBLE_PERIOD = 42
comptime MAX_CYCLOTOMIC_INDEX = 512
comptime F2_BITS = 62

comptime CELL_FAILS = 1
comptime CELL_DET_ODD = 2
comptime CELL_F = 4
comptime CELL_TWO_PERIODIC = 8
comptime CELL_DIMENSION_BOUND = 16
comptime CELL_PRIOR = 32
comptime CELL_PARITY = 64
comptime CELL_COUNT = 128


# ----------------------------------------------------------------------------
# Small exact helpers.


def _require_power(n: Int) raises:
    if n < 1:
        raise Error("rank-two parity: the power n of f is at least one")


def _sorted(var values: List[Int]) -> List[Int]:
    for i in range(1, len(values)):
        var v = values[i]
        var j = i - 1
        while j >= 0 and values[j] > v:
            values[j + 1] = values[j]
            j -= 1
        values[j + 1] = v
    return values^


def _lcm(a: Int, b: Int) raises -> Int:
    return checked_mul(a // gcd_int(a, b), b)


def _cycles(perm: List[Int]) -> List[Int]:
    """Cycle lengths of a permutation of `0..len-1`, in order of their least
    element."""
    var seen = List[Bool](length=len(perm), fill=False)
    var out = List[Int]()
    for start in range(len(perm)):
        if seen[start]:
            continue
        var length = 0
        var x = start
        while not seen[x]:
            seen[x] = True
            x = perm[x]
            length += 1
        out.append(length)
    return out^


def _power_cycle_type(perm: List[Int], n: Int) raises -> List[Int]:
    """Cycle type of `perm^n`, increasing: a cycle of length `L` splits into
    `gcd(L, n)` cycles of length `L / gcd(L, n)`."""
    _require_power(n)
    var lengths = _cycles(perm)
    var out = List[Int]()
    for k in range(len(lengths)):
        var g = gcd_int(lengths[k], n)
        for _ in range(g):
            out.append(lengths[k] // g)
    return _sorted(out^)


# ----------------------------------------------------------------------------
# The graph map f = g_K | ER.


struct ERGraphMap(Copyable, Movable):
    """`f = g_K` restricted to an `f`-invariant connected edge set on which it
    is a permutation. `edges` are codes `letters * a + b` of `e_ab`,
    increasing; `vertices` are codes `a` (for `a^+`) and `letters + b` (for
    `b^-`), increasing; `edge_image[k]` and `vertex_image[k]` are indices
    into those lists."""

    var letters: Int
    var edges: List[Int]
    var vertices: List[Int]
    var edge_image: List[Int]
    var vertex_image: List[Int]

    def __init__(
        out self,
        letters: Int,
        var edges: List[Int],
        var vertices: List[Int],
        var edge_image: List[Int],
        var vertex_image: List[Int],
    ):
        self.letters = letters
        self.edges = edges^
        self.vertices = vertices^
        self.edge_image = edge_image^
        self.vertex_image = vertex_image^

    def edge_count(self) -> Int:
        return len(self.edges)

    def vertex_count(self) -> Int:
        return len(self.vertices)

    def betti(self) -> Int:
        """`b_1 = |E| - |V| + 1` of the connected graph: `deg c_n`."""
        return len(self.edges) - len(self.vertices) + 1

    def edge_cycle_type(self, n: Int) raises -> List[Int]:
        return _power_cycle_type(self.edge_image, n)

    def vertex_cycle_type(self, n: Int) raises -> List[Int]:
        return _power_cycle_type(self.vertex_image, n)

    def order(self) raises -> Int:
        """The least `p >= 1` with `f^p` the identity on edges and vertices."""
        var p = 1
        var e = _cycles(self.edge_image)
        for k in range(len(e)):
            p = _lcm(p, e[k])
        var v = _cycles(self.vertex_image)
        for k in range(len(v)):
            p = _lcm(p, v[k])
        return p

    def fixed_edges(self, n: Int) raises -> Int:
        """Edges fixed by `f^n`: the cycles of `f^n` of length one."""
        var t = self.edge_cycle_type(n)
        var c = 0
        for k in range(len(t)):
            if t[k] == 1:
                c += 1
        return c


def graph_map_on(sigma: List[List[Int]], mask: List[Bool]) raises -> ERGraphMap:
    """The map `e_ab -> e_{g_R(a) g(b)}` on the edge set `mask` (index
    `letters * a + b`) of a primitive `sigma`. Raises unless the edge set is
    nonempty and connected and the map permutes its edges and its vertices."""
    _ = incidence_rows(sigma)  # validation and primitivity
    var n = len(sigma)
    if len(mask) != n * n:
        raise Error("rank-two parity: an edge mask has one entry per two-letter word")
    var first = prefix_endpoint_map(sigma)
    var last = suffix_endpoint_map(sigma)
    var edges = List[Int]()
    var edge_index = List[Int](length=n * n, fill=-1)
    var used = List[Bool](length=2 * n, fill=False)
    for code in range(n * n):
        if mask[code]:
            edge_index[code] = len(edges)
            edges.append(code)
            used[code // n] = True
            used[n + code % n] = True
    if len(edges) == 0:
        raise Error("rank-two parity: the edge set is empty")
    var shape = graph_shape(mask, n)
    if shape[2] != 1:
        raise Error(
            "rank-two parity: the eventual range is disconnected (G_0 != 0): the formula"
            " c_n = (t - 1) chi(P_E^n) / chi(P_V^n) needs a connected graph"
        )
    var vertices = List[Int]()
    var vertex_index = List[Int](length=2 * n, fill=-1)
    for v in range(2 * n):
        if used[v]:
            vertex_index[v] = len(vertices)
            vertices.append(v)
    var edge_image = List[Int]()
    var hit = List[Bool](length=len(edges), fill=False)
    for k in range(len(edges)):
        var a = edges[k] // n
        var b = edges[k] % n
        var j = edge_index[n * last[a] + first[b]]
        if j < 0:
            raise Error("rank-two parity: f maps an edge outside the edge set: not a self-map of the graph")
        if hit[j]:
            raise Error("rank-two parity: f is not injective on the edges: not a permutation")
        hit[j] = True
        edge_image.append(j)
    var vertex_image = List[Int]()
    var vhit = List[Bool](length=len(vertices), fill=False)
    for k in range(len(vertices)):
        var v = vertices[k]
        var image = last[v] if v < n else n + first[v - n]
        var j = vertex_index[image]
        if j < 0:
            raise Error("rank-two parity: f maps a vertex outside the vertex set: not a self-map of the graph")
        if vhit[j]:
            raise Error("rank-two parity: f is not injective on the vertices: not a permutation")
        vhit[j] = True
        vertex_image.append(j)
    return ERGraphMap(n, edges^, vertices^, edge_image^, vertex_image^)


def er_graph_map(sigma: List[List[Int]]) raises -> ERGraphMap:
    """`f = g_K|ER` for a primitive `sigma` on 2..8 letters, with `ER` as
    `psc.h1_census.eventual_range` computes it. Raises when `ER` is
    disconnected (Lemma 7(2) fails; every reducible control of the brief)."""
    var legal = legal_two_words(sigma)
    var er = eventual_range(sigma, legal)
    return graph_map_on(sigma, er)


# ----------------------------------------------------------------------------
# Integer polynomials, low-to-high coefficients, no trailing zeros; the zero
# polynomial is the empty list. Every operation is checked.


def _trim(var p: List[Int]) -> List[Int]:
    while len(p) > 0 and p[len(p) - 1] == 0:
        _ = p.pop()
    return p^


def poly_mul(a: List[Int], b: List[Int]) raises -> List[Int]:
    if len(a) == 0 or len(b) == 0:
        return List[Int]()
    var out = List[Int](length=len(a) + len(b) - 1, fill=0)
    for i in range(len(a)):
        if a[i] == 0:
            continue
        for j in range(len(b)):
            out[i + j] = checked_add(out[i + j], checked_mul(a[i], b[j]))
    return _trim(out^)


struct PolyDivision(Copyable, Movable):
    var quotient: List[Int]
    var remainder: List[Int]

    def __init__(out self, var quotient: List[Int], var remainder: List[Int]):
        self.quotient = quotient^
        self.remainder = remainder^


def poly_divide(a: List[Int], b: List[Int]) raises -> PolyDivision:
    """Euclidean division by a monic `b`; exact over `Z`."""
    if len(b) == 0 or b[len(b) - 1] != 1:
        raise Error("rank-two parity: polynomial division needs a monic divisor")
    var rest = _trim(a.copy())
    var db = len(b) - 1
    if len(rest) < len(b):
        return PolyDivision(List[Int](), rest^)
    var quotient = List[Int](length=len(rest) - db, fill=0)
    while len(rest) >= len(b):
        var shift = len(rest) - len(b)
        var factor = rest[len(rest) - 1]
        quotient[shift] = factor
        for k in range(len(b)):
            rest[shift + k] = checked_sub(rest[shift + k], checked_mul(factor, b[k]))
        rest = _trim(rest^)
    return PolyDivision(_trim(quotient^), rest^)


def poly_exact_quotient(a: List[Int], b: List[Int]) raises -> List[Int]:
    var d = poly_divide(a, b)
    if len(d.remainder) != 0:
        raise Error("rank-two parity: an exact polynomial division left a remainder")
    return d.quotient.copy()


def _t_power_minus_one(length: Int) -> List[Int]:
    var p = List[Int](length=length + 1, fill=0)
    p[0] = -1
    p[length] = 1
    return p^


def cycle_charpoly(lengths: List[Int]) raises -> List[Int]:
    """`prod (t^L - 1)`: the characteristic polynomial of a permutation matrix
    of cycle type `lengths`."""
    var out: List[Int] = [1]
    for k in range(len(lengths)):
        out = poly_mul(out, _t_power_minus_one(lengths[k]))
    return out^


def er_charpoly(map: ERGraphMap, n: Int) raises -> List[Int]:
    """`c_n = (t - 1) chi(P_E^n) / chi(P_V^n)` (Proposition C), by exact
    division."""
    var numerator = poly_mul(_t_power_minus_one(1), cycle_charpoly(map.edge_cycle_type(n)))
    return poly_exact_quotient(numerator, cycle_charpoly(map.vertex_cycle_type(n)))


# ----------------------------------------------------------------------------
# F_2[t] as bit masks.


def _bit_length(x: Int) -> Int:
    var b = 0
    var y = x
    while y != 0:
        y >>= 1
        b += 1
    return b


def f2_reduce(poly: List[Int]) raises -> Int:
    """An integer polynomial reduced mod 2, as a bit mask."""
    if len(poly) > F2_BITS:
        raise Error("rank-two parity: an F_2 polynomial beyond 62 bits")
    var bits = 0
    for i in range(len(poly)):
        if poly[i] & 1 == 1:
            bits |= 1 << i
    return bits


def f2_mul(a: Int, b: Int) raises -> Int:
    """Carry-less product in `F_2[t]`."""
    if a < 0 or b < 0:
        raise Error("rank-two parity: an F_2 polynomial is a non-negative bit mask")
    if _bit_length(a) + _bit_length(b) > F2_BITS:
        raise Error("rank-two parity: an F_2 product beyond 62 bits")
    var out = 0
    var x = a
    var shift = 0
    while x != 0:
        if x & 1 == 1:
            out ^= b << shift
        x >>= 1
        shift += 1
    return out


def f2_degree(a: Int) -> Int:
    """Degree of a nonzero bit-mask polynomial (`-1` for zero)."""
    return _bit_length(a) - 1


def f2_strip_t(p: Int) -> Int:
    """The part prime to `t`: remove the factors `t` (zero stays zero)."""
    if p == 0:
        return 0
    var x = p
    while x & 1 == 0:
        x >>= 1
    return x


def _f2_pow(a: Int, e: Int) raises -> Int:
    var out = 1
    for _ in range(e):
        out = f2_mul(out, a)
    return out


# ----------------------------------------------------------------------------
# Cyclotomic polynomials.


def _totient(d: Int) -> Int:
    var result = d
    var m = d
    var p = 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            result -= result // p
        p += 1
    if m > 1:
        result -= result // m
    return result


struct CyclotomicTable(Copyable, Movable):
    """`Phi_1, ..., Phi_D`, built bottom-up by `Phi_d = (t^d - 1) / prod_{e | d,
    e < d} Phi_e` with exact division, and extended on demand up to
    `MAX_CYCLOTOMIC_INDEX`."""

    var polys: List[List[Int]]

    def __init__(out self, max_index: Int) raises:
        self.polys = List[List[Int]]()
        self.polys.append(List[Int]())
        self.ensure(max_index)

    def ensure(mut self, d: Int) raises:
        if d > MAX_CYCLOTOMIC_INDEX:
            raise Error("rank-two parity: a cyclotomic index beyond MAX_CYCLOTOMIC_INDEX: refuse to conclude")
        while len(self.polys) <= d:
            var k = len(self.polys)
            var p = _t_power_minus_one(k)
            for e in range(1, k):
                if k % e == 0:
                    p = poly_exact_quotient(p, self.polys[e])
            self.polys.append(p^)

    def poly(mut self, d: Int) raises -> List[Int]:
        if d < 1:
            raise Error("rank-two parity: a cyclotomic index is at least one")
        self.ensure(d)
        return self.polys[d].copy()

    def mod2(mut self, d: Int) raises -> Int:
        return f2_reduce(self.poly(d))


def cyclotomic(d: Int) raises -> List[Int]:
    var table = CyclotomicTable(1)
    return table.poly(d)


def cyclotomic_exponents(map: ERGraphMap, n: Int) raises -> List[Int]:
    """Exponent of `Phi_d` in `c_n`, index `d` (index 0 unused), from the
    cycle type of `f^n`: `[d = 1] + #{edge cycles with d | L} - #{vertex
    cycles with d | L}`."""
    var edge_type = map.edge_cycle_type(n)
    var vertex_type = map.vertex_cycle_type(n)
    var top = 1
    for k in range(len(edge_type)):
        if edge_type[k] > top:
            top = edge_type[k]
    for k in range(len(vertex_type)):
        if vertex_type[k] > top:
            top = vertex_type[k]
    var e = List[Int](length=top + 1, fill=0)
    e[1] = 1
    for k in range(len(edge_type)):
        for d in range(1, edge_type[k] + 1):
            if edge_type[k] % d == 0:
                e[d] += 1
    for k in range(len(vertex_type)):
        for d in range(1, vertex_type[k] + 1):
            if vertex_type[k] % d == 0:
                e[d] -= 1
    for d in range(1, top + 1):
        if e[d] < 0:
            raise Error("rank-two parity: a negative cyclotomic exponent (impossible for a polynomial c_n)")
    return e^


def cyclotomic_product(exponents: List[Int], mut table: CyclotomicTable) raises -> List[Int]:
    var out: List[Int] = [1]
    for d in range(1, len(exponents)):
        if exponents[d] < 0:
            raise Error("rank-two parity: a negative cyclotomic exponent")
        if exponents[d] == 0:
            continue
        var phi = table.poly(d)
        for _ in range(exponents[d]):
            out = poly_mul(out, phi)
    return out^


def cyclotomic_factorisation(poly: List[Int], mut table: CyclotomicTable) raises -> List[Int]:
    """Exponents `e_d` with `poly = prod Phi_d^{e_d}`, by trial division over
    every `d` with `phi(d) <= deg` (so `d <= 2 deg^2`). Raises unless `poly` is
    a monic product of cyclotomic polynomials."""
    var rest = _trim(poly.copy())
    if len(rest) == 0:
        raise Error("rank-two parity: the zero polynomial is not a product of cyclotomic polynomials")
    if rest[len(rest) - 1] != 1:
        raise Error("rank-two parity: not monic, so not a product of cyclotomic polynomials")
    var degree = len(rest) - 1
    var bound = 2 * degree * degree + 2
    if bound > MAX_CYCLOTOMIC_INDEX:
        raise Error("rank-two parity: cyclotomic trial division beyond MAX_CYCLOTOMIC_INDEX: refuse to conclude")
    var e = List[Int](length=bound + 1, fill=0)
    for d in range(1, bound + 1):
        if _totient(d) > len(rest) - 1:
            continue
        var phi = table.poly(d)
        while len(rest) >= len(phi):
            var division = poly_divide(rest, phi)
            if len(division.remainder) != 0:
                break
            rest = division.quotient.copy()
            e[d] += 1
    if len(rest) != 1 or rest[0] != 1:
        raise Error("rank-two parity: not a product of cyclotomic polynomials")
    return e^


# ----------------------------------------------------------------------------
# chi_{M^n} mod 2 and h_n.


def incidence_mod2(sigma: List[List[Int]]) raises -> List[Int]:
    """`M mod 2`, row-major, entries in `{0, 1}`, after the validation and
    primitivity gate of `psc.h1_census.incidence_rows`; three letters only."""
    if len(sigma) != 3:
        raise Error("rank-two parity: Theorem P+ is stated for PIP3, on three letters")
    var rows = incidence_rows(sigma)
    var out = List[Int]()
    for k in range(9):
        out.append(rows[k] & 1)
    return out^


def _f2_matmul(a: List[Int], b: List[Int]) -> List[Int]:
    var out = List[Int](length=9, fill=0)
    for i in range(3):
        for j in range(3):
            var s = 0
            for k in range(3):
                s ^= a[3 * i + k] & b[3 * k + j]
            out[3 * i + j] = s
    return out^


def _f2_charpoly(a: List[Int]) -> Int:
    """`t^3 + tr t^2 + e_2 t + det` over `F_2`, as a bit mask."""
    var tr = a[0] ^ a[4] ^ a[8]
    var e2 = (a[0] & a[4]) ^ (a[1] & a[3]) ^ (a[0] & a[8]) ^ (a[2] & a[6]) ^ (a[4] & a[8]) ^ (a[5] & a[7])
    var det = (
        (a[0] & a[4] & a[8]) ^ (a[1] & a[5] & a[6]) ^ (a[2] & a[3] & a[7])
        ^ (a[2] & a[4] & a[6]) ^ (a[1] & a[3] & a[8]) ^ (a[0] & a[5] & a[7])
    )
    return 8 | (tr << 2) | (e2 << 1) | det


def chi_power_mod2(m2: List[Int], n: Int) raises -> Int:
    """`chi_{M^n} mod 2`: the characteristic polynomial of `(M mod 2)^n`."""
    _require_power(n)
    if len(m2) != 9:
        raise Error("rank-two parity: M mod 2 has nine entries")
    var p = m2.copy()
    for _ in range(n - 1):
        p = _f2_matmul(p, m2)
    return _f2_charpoly(p)


def h_polynomial(m2: List[Int], n: Int) raises -> Int:
    """`h_n`: the part of `chi_{M^n} mod 2` prime to `t`."""
    return f2_strip_t(chi_power_mod2(m2, n))


def is_admissible(sigma: List[List[Int]], legal: List[Bool], n: Int) raises -> Bool:
    """The note's definition: some legal word `ba` has `g_R^n(b) = b` and
    `g^n(a) = a`."""
    _require_power(n)
    var size = len(sigma)
    if len(legal) != size * size:
        raise Error("rank-two parity: a legal-word mask has one entry per two-letter word")
    var first = prefix_endpoint_map(sigma)
    var last = suffix_endpoint_map(sigma)
    for b in range(size):
        var x = b
        for _ in range(n):
            x = last[x]
        if x != b:
            continue
        for a in range(size):
            if not legal[size * b + a]:
                continue
            var y = a
            for _ in range(n):
                y = first[y]
            if y == a:
                return True
    return False


# ----------------------------------------------------------------------------
# The search at one n.


struct DivisorWitness(Copyable, Movable):
    """The outcome of the search at one `n`: `found`, the exponents of the
    first witness (`r`, `q1`, index `d`), and the number of candidates
    examined."""

    var found: Bool
    var r: List[Int]
    var q1: List[Int]
    var examined: Int

    def __init__(out self, found: Bool, var r: List[Int], var q1: List[Int], examined: Int):
        self.found = found
        self.r = r^
        self.q1 = q1^
        self.examined = examined


def divisor_search(exponents: List[Int], h: Int, mut table: CyclotomicTable) raises -> DivisorWitness:
    """Every pair of sub-multisets `(a_d), (b_d)` with `a_d + b_d <= e_d` of
    `c_n = prod Phi_d^{e_d}`, tested for `h rbar = (t + 1) q_1bar` over
    `F_2`. `h` must be a nonzero polynomial prime to `t`."""
    if h <= 0 or h & 1 == 0:
        raise Error("rank-two parity: h_n must be a nonzero F_2 polynomial prime to t")
    var support = List[Int]()
    var reduced = List[Int]()
    var option_count = List[Int]()
    for d in range(1, len(exponents)):
        if exponents[d] < 0:
            raise Error("rank-two parity: a negative cyclotomic exponent")
        if exponents[d] > 0:
            support.append(d)
            reduced.append(table.mod2(d))
            var e = exponents[d]
            option_count.append((e + 1) * (e + 2) // 2)
    # options of one d, in lexicographic order of (a, b) with a + b <= e
    var option_a = List[List[Int]]()
    var option_b = List[List[Int]]()
    for k in range(len(support)):
        var e = exponents[support[k]]
        var la = List[Int]()
        var lb = List[Int]()
        for a in range(e + 1):
            for b in range(e + 1 - a):
                la.append(a)
                lb.append(b)
        option_a.append(la^)
        option_b.append(lb^)
    var digits = List[Int](length=len(support), fill=0)
    var examined = 0
    while True:
        var rbar = 1
        var qbar = 1
        for k in range(len(support)):
            rbar = f2_mul(rbar, _f2_pow(reduced[k], option_a[k][digits[k]]))
            qbar = f2_mul(qbar, _f2_pow(reduced[k], option_b[k][digits[k]]))
        examined += 1
        if f2_mul(h, rbar) == f2_mul(3, qbar):
            var r = List[Int](length=len(exponents), fill=0)
            var q = List[Int](length=len(exponents), fill=0)
            for k in range(len(support)):
                r[support[k]] = option_a[k][digits[k]]
                q[support[k]] = option_b[k][digits[k]]
            return DivisorWitness(True, r^, q^, examined)
        # odometer, last digit fastest
        var k = len(support) - 1
        while k >= 0:
            digits[k] += 1
            if digits[k] < option_count[k]:
                break
            digits[k] = 0
            k -= 1
        if k < 0:
            break
    return DivisorWitness(
        False, List[Int](length=len(exponents), fill=0), List[Int](length=len(exponents), fill=0), examined
    )


# ----------------------------------------------------------------------------
# One substitution.


def require_pip3(sigma: List[List[Int]]) raises -> Mat3:
    """The incidence matrix of `sigma`, after the PIP3 gate. Raises otherwise."""
    if len(sigma) != 3:
        raise Error("rank-two parity: Theorem P+ is stated for PIP3, on three letters")
    var m = Mat3(incidence_rows(sigma))  # validation; raises unless primitive
    var chi = m.charpoly()
    if not is_irreducible_cubic(chi):
        raise Error("rank-two parity: not PIP3: the characteristic polynomial of M is reducible over Q")
    if not is_pisot_charpoly(chi):
        raise Error("rank-two parity: not PIP3: the Perron root is not a Pisot number")
    return m^


struct DivisorProfile(Copyable, Movable):
    """The divisor condition of Theorem P+ for one PIP3 substitution, at
    `n = 1..ADMISSIBLE_PERIOD` (Lemma N: every residue mod 42). Lists are
    indexed by `n` (index 0 unused). `satisfied[n]` is meaningful where
    `admissible[n]`; `first_failure` is the least admissible `n` without a
    witness, `0` when there is none."""

    var d2: Int
    var trace_parity: Int
    var e2_parity: Int
    var det_parity: Int
    var betti: Int
    var h1_dimension: Int
    var order: Int
    var admissible: List[Bool]
    var satisfied: List[Bool]
    var h: List[Int]
    var exponents: List[List[Int]]
    var examined: Int
    var first_failure: Int

    def __init__(out self):
        self.d2 = 0
        self.trace_parity = 0
        self.e2_parity = 0
        self.det_parity = 0
        self.betti = 0
        self.h1_dimension = 0
        self.order = 0
        self.admissible = List[Bool](length=ADMISSIBLE_PERIOD + 1, fill=False)
        self.satisfied = List[Bool](length=ADMISSIBLE_PERIOD + 1, fill=False)
        self.h = List[Int](length=ADMISSIBLE_PERIOD + 1, fill=0)
        self.exponents = List[List[Int]]()
        self.exponents.append(List[Int]())
        self.examined = 0
        self.first_failure = 0

    def fails(self) -> Bool:
        """Some admissible `n` has no witness: Theorem P+, if its imports
        hold, excludes coincidence rank 2. Not a certificate."""
        return self.first_failure != 0

    def det_odd(self) -> Bool:
        return self.det_parity == 1

    def parity_clause(self) -> Bool:
        """`tr M != e_2(M) (mod 2)`."""
        return self.trace_parity != self.e2_parity

    def dimension_bound(self) -> Int:
        """`3 + |d_2 - 1|` (Theorem P+, item 1)."""
        return 3 + (self.d2 - 1 if self.d2 >= 1 else 1 - self.d2)

    def dimension_bound_holds(self) -> Bool:
        return self.h1_dimension >= self.dimension_bound()

    def admissible_count(self) -> Int:
        var c = 0
        for n in range(1, ADMISSIBLE_PERIOD + 1):
            if self.admissible[n]:
                c += 1
        return c

    def failure_count(self) -> Int:
        var c = 0
        for n in range(1, ADMISSIBLE_PERIOD + 1):
            if self.admissible[n] and not self.satisfied[n]:
                c += 1
        return c


def _same_exponents(a: List[Int], b: List[Int]) -> Bool:
    var top = len(a) if len(a) > len(b) else len(b)
    for d in range(1, top):
        var x = a[d] if d < len(a) else 0
        var y = b[d] if d < len(b) else 0
        if x != y:
            return False
    return True


def divisor_profile_with(sigma: List[List[Int]], mut table: CyclotomicTable) raises -> DivisorProfile:
    """The divisor condition of Theorem P+ for a PIP3 `sigma`, decided at every
    `n = 1..42` with the internal agreements of the module docstring."""
    _ = require_pip3(sigma)
    var out = DivisorProfile()
    var map = er_graph_map(sigma)
    out.betti = map.betti()
    out.order = map.order()
    if 6 % out.order != 0:
        raise Error("rank-two parity: the order of f on ER does not divide 6 (Lemma 7(1) fails)")
    out.h1_dimension = 3 + out.betti
    if h1_profile(sigma).dimension != out.h1_dimension:
        raise Error("rank-two parity: deg c_n disagrees with dim H^1 - 3")
    var legal = legal_two_words(sigma)
    var m2 = incidence_mod2(sigma)
    var chi1 = chi_power_mod2(m2, 1)
    out.trace_parity = (chi1 >> 2) & 1
    out.e2_parity = (chi1 >> 1) & 1
    out.det_parity = chi1 & 1
    out.d2 = f2_degree(f2_strip_t(chi1))
    var power = m2.copy()
    for n in range(1, ADMISSIBLE_PERIOD + 1):
        if n > 1:
            power = _f2_matmul(power, m2)
        var h = f2_strip_t(_f2_charpoly(power))
        if f2_degree(h) != out.d2:
            raise Error("rank-two parity: deg h_n differs from d_2 (impossible)")
        out.h[n] = h
        var exponents = cyclotomic_exponents(map, n)
        var c = er_charpoly(map, n)
        if cyclotomic_product(exponents, table) != c:
            raise Error("rank-two parity: the cycle-type factorisation does not multiply to c_n")
        if not _same_exponents(cyclotomic_factorisation(c, table), exponents):
            raise Error("rank-two parity: trial division and the cycle type factor c_n differently")
        out.exponents.append(exponents.copy())
        var admissible = is_admissible(sigma, legal, n)
        if admissible != (map.fixed_edges(n) > 0):
            raise Error("rank-two parity: admissibility disagrees with the fixed edges of f^n")
        out.admissible[n] = admissible
        if admissible:
            var w = divisor_search(exponents, h, table)
            out.examined += w.examined
            out.satisfied[n] = w.found
            if not w.found and out.first_failure == 0:
                out.first_failure = n
    return out^


def divisor_profile(sigma: List[List[Int]]) raises -> DivisorProfile:
    var table = CyclotomicTable(32)
    return divisor_profile_with(sigma, table)


# ----------------------------------------------------------------------------
# The census.


struct RankTwoParityCensus(Copyable, Movable):
    """Per-specimen facts over a corpus, folded into order-independent
    tables. `cells` is keyed by the `CELL_*` bits. `first_failure` and
    `failures_at` are keyed by `64 * (det M odd) + n`; `admissible_at` by `n`.
    `beyond` lists the corpus indices on which the divisor condition fails
    and `CELL_PRIOR` does not hold (the specimens Theorem P+ reaches beyond
    the recorded theorems without the divisor condition);
    `beyond_classes` (key `10 * d_2 + dim H^1`) and `beyond_first_failure`
    tabulate them. Class counts under a recorded conditional theorem, not
    certificates of a coincidence rank."""

    var total: Int
    var cells: Histogram
    var first_failure: Histogram
    var failures_at: Histogram
    var admissible_at: Histogram
    var beyond_classes: Histogram
    var beyond_first_failure: Histogram
    var beyond: List[Int]
    var beyond_labels: List[String]
    var examined: Int

    def __init__(out self):
        self.total = 0
        self.cells = Histogram(CELL_COUNT)
        self.first_failure = Histogram(128)
        self.failures_at = Histogram(128)
        self.admissible_at = Histogram(ADMISSIBLE_PERIOD + 1)
        self.beyond_classes = Histogram(40)
        self.beyond_first_failure = Histogram(ADMISSIBLE_PERIOD + 1)
        self.beyond = List[Int]()
        self.beyond_labels = List[String]()
        self.examined = 0

    def count_where(self, mask: Int, value: Int) -> Int:
        """Number of specimens whose cell agrees with `value` on `mask`."""
        var n = 0
        for key in range(CELL_COUNT):
            if key & mask == value:
                n += self.cells.count(key)
        return n

    def summary(self) -> String:
        var fails = CELL_FAILS
        var odd = CELL_DET_ODD
        var bound = CELL_DIMENSION_BOUND
        var prior = CELL_PRIOR
        var open_mask = CELL_F | CELL_TWO_PERIODIC
        var out = String("rank-two parity (Theorem P+ divisor condition, n = 1..42): ")
        out += String(self.total) + " specimens; the condition fails on "
        out += String(self.count_where(fails | odd, fails | odd)) + " odd and "
        out += String(self.count_where(fails | odd, fails)) + " even; beyond the dimension bound "
        out += String(self.count_where(fails | bound | odd, fails | bound | odd)) + " odd and "
        out += String(self.count_where(fails | bound | odd, fails | bound)) + " even; beyond the prior classes "
        out += String(self.count_where(fails | prior | odd, fails | odd)) + " odd and "
        out += String(self.count_where(fails | prior | odd, fails)) + " even; open classes (F, two periodic"
        out += " letters on both sides, not prior): "
        out += String(self.count_where(open_mask | prior | odd, open_mask | odd)) + " odd and "
        out += String(self.count_where(open_mask | prior | odd, open_mask)) + " even, of which the condition fails on "
        out += String(self.count_where(open_mask | prior | odd | fails, open_mask | odd | fails)) + " odd and "
        out += String(self.count_where(open_mask | prior | odd | fails, open_mask | fails)) + " even; "
        out += self.beyond_classes.line("beyond-prior (10 d_2 + dim H^1):") + "; "
        out += self.first_failure.line("first failure (64 odd + n):") + "; candidates examined "
        out += String(self.examined)
        return out^


def rank_two_parity_census(corpus: List[Specimen]) raises -> RankTwoParityCensus:
    """One pass over `corpus`: the divisor condition, (F), the endpoint and
    arithmetic classes of `psc.c4_geometric_f`."""
    var out = RankTwoParityCensus()
    var table = CyclotomicTable(32)
    var boxes = StableRadiiCache()
    for s in range(len(corpus)):
        var sigma = corpus[s].sigma.copy()
        var p = divisor_profile_with(sigma, table)
        var m = PrototileMap(sigma)
        var verdict = decide_geometric_f_with(m, boxes)
        var f = fc3_profile_of(m)
        if f.d2() != p.d2 or f.h1_dimension != p.h1_dimension or f.det_odd() != p.det_odd():
            raise Error("rank-two parity: d_2, dim H^1 or the determinant parity disagree with psc.c4_geometric_f")
        if f.parity_clause() != p.parity_clause() or f.dimension_clause() == p.dimension_bound_holds():
            raise Error("rank-two parity: the parity or dimension clause disagrees with psc.c4_geometric_f")
        var key = 0
        if p.fails():
            key |= CELL_FAILS
        if p.det_odd():
            key |= CELL_DET_ODD
        if verdict.holds:
            key |= CELL_F
        if not f.endpoint_trivial():
            key |= CELL_TWO_PERIODIC
        if p.dimension_bound_holds():
            key |= CELL_DIMENSION_BOUND
        if f.rank_two_hypotheses_hold():
            key |= CELL_PRIOR
        if p.parity_clause():
            key |= CELL_PARITY
        out.cells.record(key)
        var parity_offset = 64 if p.det_odd() else 0
        for n in range(1, ADMISSIBLE_PERIOD + 1):
            if p.admissible[n]:
                out.admissible_at.record(n)
                if not p.satisfied[n]:
                    out.failures_at.record(parity_offset + n)
        if p.fails():
            out.first_failure.record(parity_offset + p.first_failure)
            if not f.rank_two_hypotheses_hold():
                out.beyond.append(s)
                out.beyond_labels.append(corpus[s].label())
                out.beyond_classes.record(10 * p.d2 + p.h1_dimension)
                out.beyond_first_failure.record(p.first_failure)
        out.examined += p.examined
        out.total += 1
    return out^
