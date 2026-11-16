"""The geometric property (F) of a ternary irreducible Pisot substitution,
decided exactly, and the corpus content of Theorems FC1, P and FC3, and of
Theorems H3, FC3+ and P+ of round 2.

docs/c4-geometric-f-class-2026-11-16.md; for round 2,
docs/c4-rank-two-wall-2026-11-16.md. Standing class PIP3: a primitive
substitution `sigma` on `{0,1,2}` whose incidence matrix `M` has an irreducible
characteristic polynomial with a Pisot Perron root `beta` (nonunit allowed).
`ell` is the positive left Perron vector (tile lengths), `p(.)` the Parikh
vector, `g` / `g_R` the first- / last-letter maps.

The prototile state map
-----------------------
A *state* is `(j, v)` with `j` a letter, `v` in `Z^3` and
`0 <= <ell, v> < ell_j`: the lattice point `v` seen from the left end of a
tile of type `j` that contains it. Inflating,

    f(j, v) = (j', M v - p(P)),     sigma(j) = P j' S,
    <ell, p(P)>  <=  <ell, M v>  <  <ell, p(P)> + ell_{j'},

the sub-tile of `sigma(j)` that contains the inflated point, and the point
seen from its left end. `<ell, M v> = beta <ell, v>` lies in `[0, beta ell_j)`,
which the sub-tiles of `sigma(j)` partition into half-open intervals, so `f`
is a function on states. *Vertex states* (`v = 0`) are forward invariant:
`f(j, 0) = (g(j), 0)`.

    (F)  :=  no f-periodic state has v != 0.

This is the geometric property (F) of the Pisot-substitution literature
(Minervino--Thuswaldner, arXiv:1402.2002, Def. 9.3 / Prop. 9.4) and, by the
bridge below, the hypothesis of Corollary LC5 of
docs/p1b-leftmost-chain-periodic-pair-2026-10-05.md ("no terminal leftmost
cycle"). An f-cycle through `(e, v)` of length `k` with `v != 0` is an
*interior periodic address*: composing the `k` steps, `sigma^k(e) = P e Q`
with `P` and `Q` nonempty and

    (M^k - I) v = p(P),

so `(M^k - I)^{-1} p(P)` is integral. `interior_address` replays exactly that.

Why the enumeration is complete (the bound, with its proof)
-----------------------------------------------------------
Every decision is taken in `Z^3` and in `Z[beta]` at the Perron embedding
(`psc.perron_field3.sign_at_perron`, exact). `<ell, .>` is injective on `Q^3`
because the characteristic polynomial is irreducible (the three conjugate
left eigenvectors are independent), so a state is its letter and its
position `x = <ell, v>`, and `ell_0, ell_1, ell_2` is a `Q`-basis of
`Q(beta)`.

*Lemma B (every f-periodic state lies in the box).* Let `(j_n, v_n)`,
`n in Z/k`, be an f-cycle and `x_n = <ell, v_n>`. Then

1. `0 <= x_n < ell_{j_n} <= ell_max` at the Perron embedding: that is the
   definition of a state.
2. `x_{n+1} = beta x_n - <ell, d_n>` with `d_n = p(P_n)` the Parikh vector of
   a proper prefix of `sigma(j_n)`. So `d_n = 0`, or `d_n` lies in the digit
   set `D_M` of the vectors `d != 0` with `0 <= d <= M e_j` componentwise and
   `d != M e_j` for some letter `j`, which depends on `M` only. For a
   contracting embedding `tau` of `Q(beta)` (`|tau(beta)| < 1`: the Pisot
   property), put `S = max_n |tau(x_n)|`, finite because the cycle is, and
   `C_tau = max_{d in D_M} |tau(<ell, d>)|`. Then
   `S <= |tau(beta)| S + C_tau`, hence

       |tau(x_n)|  <=  C_tau / (1 - |tau(beta)|)       for every n.

3. Let `theta_0, theta_1, theta_2` be the trace-dual basis of
   `ell_0, ell_1, ell_2`. Then `(v_n)_a = Tr(theta_a x_n)`, a sum over the
   three embeddings, so

       |(v_n)_a|  <=  |theta_a| ell_max
                     + sum_tau |tau(theta_a)| C_tau / (1 - |tau(beta)|),

   the sum over the contracting embeddings (a complex pair counts twice).

Steps 1--3 are Proposition V, step 1
(docs/p1b-vertex-coincidence-box-2026-10-02.md) specialised to `f`. Its
implementation `psc.vertex_coincidence.box_radii` decides every bound by
Sturm--Tarski queries over unbounded rationals, at about 0.2 s per
substitution (measured 2026-11-16: 45 s on every 23rd corpus specimen, so
about 17 CPU-minutes on the corpus; `leftmost_chain_census.mojo` took 22),
which a corpus regression cannot afford 4,554 times. `stable_radii`
evaluates the right-hand side of step 3 with the digit set `D_M`, from the
incidence matrix alone, by outward-rounded rational interval arithmetic
(`finite_exact` `IQ`): the radii `R_a` are certified upper bounds and are
shared by every substitution with that matrix (348 matrices on the corpus,
about 6 s in all; the whole (F) decision of the corpus takes about 15 s).
The returned integers are not comparable coordinate-wise with those of
`box_radii`, which uses the offset increments of the overlap graph of the
one substitution and rounds its bound up where `stable_radii` takes the floor
(Tribonacci: `[2, 3, 4]` against `[3, 3, 3]`, both pinned in the regression).

- *trace-dual basis.* `chi(t) / (t - beta) = b_0 + b_1 t + b_2 t^2` with
  `b_2 = 1`, `b_1 = beta + chi_2`, `b_0 = beta^2 + chi_2 beta + chi_1`, and
  `Tr(beta^i b_j / chi'(beta)) = delta_ij` (Euler). With `L` the matrix of the
  `ell_a` in the basis `1, beta, beta^2`,
  `theta_a = g_a / (det L chi'(beta))`, `g_a = sum_i adj(L)_{ai} b_i` in
  `Z[beta]`. `stable_radii` does not trust this paragraph: it checks
  `Tr(g_a ell_c cof) = N det L delta_ac` exactly, where `cof` is the product
  of the two other conjugates of `chi'(beta)` and `N = chi'(beta) cof` its
  norm, a rational integer (minus the discriminant).
- *embeddings.* The Perron root is bracketed by
  `psc.perron_root_sign.perron_root_bracket`. If the discriminant is positive
  the two conjugates are real, isolated in `(-1, 1)` by
  `psc.real_root_sign.isolate_real_roots` and bisected. If it is negative
  they are a complex pair and only symmetric functions are needed:
  `beta' + beta'' = -chi_2 - beta`, `beta' beta'' = beta^2 + chi_2 beta + chi_1`.
  In both cases `|tau(y)|^2` for `y = a_0 + a_1 beta + a_2 beta^2` is the
  quadratic form `sum_{i <= j} a_i a_j m_ij` in six enclosed moments, and
  `|tau(beta)|^2 = m_11` must be certified below `1`.
- *square roots.* `(r + x / r) / 2 >= sqrt(x)` for every `r > 0`, so each
  Newton iterate, rounded up to a dyadic grid, is a certified upper bound.

A radius that cannot be certified (an enclosure that does not separate from
zero, a contraction not below `1`, a radius beyond `RADIUS_CAP`) raises. A
loose radius is harmless: a superset of the periodic states changes no
verdict.

The same radii bound the offset vector of every vertex of a terminal
leftmost cycle: by Lemma S of the LC note one of the two indices is `0` at
every leftmost step, so the offsets obey `t_{n+1} = beta t_n +- c_n` with a
single sub-tile position `c_n`, and `|t_n| < ell_max` for an overlap. The
regression seeds `psc.leftmost_chain` with them, without `box_radii`.

*Lemma W (the walk finds every cycle).* `box_candidates` lists every state
with `|v_a| <= R_a` and `v != 0`: for each value of two coordinates the third
runs over the integer interval on which `0 <= <ell, v> < ell_max`, found by
exact monotone sign tests. Each candidate's f-orbit is followed until it
reaches a vertex state, settled ground, or closes on itself. An interior
cycle never meets a vertex state (vertex states are forward invariant), so
the first walk to enter a cycle goes once around it and closes on its entry
state: every f-cycle with `v != 0` is recorded exactly once. The orbit of a
candidate may leave the box; that is allowed, `f` is defined on all states.

So `decide_geometric_f` returns *all* interior f-cycles, and `(F)` holds
exactly when it returns none. Only `decide_geometric_f` and
`decide_geometric_f_with` return a `GeometricFVerdict`, and both take the box
from `stable_radii`. `interior_cycles_in_box` walks a box the caller names
and returns a `BoxSearch`, which carries no verdict: an empty search in a box
that is not certified says nothing about (F).

Status: Lemma B and Lemma W are recorded proofs in this docstring, not
machine-checked, independent human review pending. The regression checks
their consequences, not the lemmas: the radii are pinned (the five fixtures,
and their sum over the corpus); the doubled box holds no further cycle on
the fixtures and on every 97th corpus specimen; on the fixtures the box of
the independent `box_radii` holds none either; and the leftmost-cycle count
of the literal box graph, whose radii are the independent ones, agrees on
the fixtures that fail (F) and on every 97th specimen.

The bridge to the leftmost chain (Corollary LC5)
------------------------------------------------
For an overlap `(i, j, t)` of negative offset the top tile starts inside the
bottom tile at relative position `-t`, and the leftmost step of
`psc.leftmost_chain` is `(i, j, t) -> (g(i), f(j, -t))` in the coordinates
above; positive offsets are the mirror image. So the terminal leftmost cycles
of one sign are the cycles of `g x f` on (g-periodic letter) x (interior
f-periodic state); a `k`-cycle times an `m`-cycle splits into `gcd(k, m)`
cycles of length `lcm(k, m)`, and

    #terminal leftmost cycles  =  2 * sum_{C interior, G a g-cycle} gcd(|C|, |G|).

`predicted_leftmost_cycles` evaluates the right-hand side;
`kernel/tests/test_c4_geometric_f.mojo` compares it with
`psc.leftmost_chain.terminal_leftmost_cycles` on every corpus specimen.

Theorem FC1: relative states of two fixed rays
----------------------------------------------
Let `c != d` be letters periodic under `g`, `m` the least `m >= 1` with
`g^m(c) = c` and `g^m(d) = d`, `tau = sigma^m`, and `X_c`, `X_d` the
`tau`-fixed rays. The *relative state* of a vertex `y` of one ray is
`(b, y - y')`, where the tile of the other ray that contains the point `y`
has type `b` and left vertex `y'`. `tau` maps that tile to a patch of the
same ray, so `s(M^m y) = f^m(s(y))`, and `y` is a common vertex exactly when
`s(y)` is a vertex state.

`fixed_ray_relative_states` computes the set of relative states exactly, with
no prefix truncation: the tiles of `sigma^n(c)` and `sigma^n(d)`, both placed
at the origin, that overlap in an interval are the level-`n` descendants of
the prefix-aligned root overlap `(c, d, 0)` in the overlap graph, and
`sigma^n(c)`, `sigma^n(d)` are prefixes of `X_c`, `X_d` exactly when `m | n`.
So the overlaps of the two rays are the descendants of the root at the levels
divisible by `m`, a finite set (the closure carries the level mod `m`), and an
overlap `(a, b, t)` contributes the relative state `(b, -t)` when `t <= 0`
(the top vertex inside the bottom tile) and `(a, t)` when `t >= 0`.

The *transient length* of a relative state `s` is the least `n >= 0` with
`f^n(s)` a vertex state; it does not exist when the orbit of `s` enters an
interior cycle, and `s` is then *absorbed*. The transient `N` of the pair is
the maximum over its relative states. When no state is absorbed, every
vertex `y` of either ray has `M^{m N'} y` a common vertex of both, for
`N' = ceil(N / m)`: Theorem FC1.
Under (F) no state can be absorbed, and `OrbitMemo` raises if an orbit closes
on a cycle that `decide_geometric_f` did not certify: that would contradict
Lemma B, and is never reported as a count.

Arithmetic classes (Theorems P and FC3)
---------------------------------------
`fc3_profile` records `det M`, `tr M`, `e_2(M)` (the sum of the principal
2x2 minors, `tr Lambda^2 M`), `dim H^1` (`psc.h1_census.h1_profile`) and the
number of periodic letters of `g` and `g_R`. The clauses evaluated are
three of the note's: (a') an endpoint map with fewer than two periodic
letters, i.e. `g` or `g_R` eventually constant (the sub-case of clause (a)
that needs no coincidence search; clause (a) itself, `nu_L = 1` or
`nu_R = 1`, is not evaluated here); (b) `det M` odd and `dim H^1 <= 4`;
(c) `det M` odd and `tr M != e_2(M) (mod 2)`. `fc3_profile` raises on input
that is not PIP3: outside PIP3 the clauses mean nothing.
`geometric_f_census` folds the per-specimen facts into `psc.histogram`
tables. The census counts classes; it certifies no coincidence rank, no pure
discrete spectrum and no strong coincidence, and changes no claim status.

Round 2: every determinant (Theorems H3, FC3+ and P+)
------------------------------------------------------
docs/c4-rank-two-wall-2026-11-16.md. With
`chi_M = t^3 - (tr M) t^2 + e_2(M) t - det M`,

    chi_M mod 2 = t^3 + a t^2 + b t + c,    a, b, c the parities of
                                            tr M, e_2(M), det M,

and `FC3Profile.chi_mod2` is the code `4a + 2b + c` of that class.

    d_2(sigma) := 3 - ord_t(chi_M mod 2)

is the number of nonzero roots of `chi_M` over an algebraic closure of
`F_2`, with multiplicity: `3` when `det M` is odd, else `2` when `e_2(M)` is
odd, else `1` when `tr M` is odd, else `0` (`nonzero_roots_mod2`). It is
also the rank over `F_2` of `(M mod 2)^3`; the regression recomputes it that
way on every corpus specimen. Two further clauses are evaluated, beside
(a'), (b), (c) above; the letters (d) and (e) are this module's:

(d) `dim H^1 = 3`, for every determinant (`FC3Profile.h1_three`). Theorem H3
    of the note: a PIP3 substitution with `dim H^1(Omega; Q) = 3` does not
    have coincidence rank 2. For odd determinant that is Barge 2015 Theorem
    22 and lies inside clause (b); the even determinants are what the note
    adds. With (F) it is Theorem FC3+.
(e) `dim H^1 < 3 + |d_2 - 1|` (`FC3Profile.dimension_clause`): the dimension
    bound of Theorem P+ fails. Theorem P+: coincidence rank 2 needs
    `dim H^1 >= 3 + |d_2 - 1|`, that is `>= 5` for `d_2 = 3` (Barge's bound,
    clause (b)), `>= 4` for `d_2 = 2` and for `d_2 = 0`, and nothing for
    `d_2 = 1`. For even determinant (e) is contained in (d). The note
    attributes the mechanism of P+ to the parity argument of
    Barge--Bruin--Jones--Sadun for degree one; Barge 2015 Theorem 22 is the
    odd-norm case.

`FC3Profile.rank_two_excluded` is the union with the round-1 clauses: odd
determinant and (`dim H^1 <= 4` or `tr M != e_2(M) (mod 2)`), or even
determinant and `dim H^1 = 3`. `ClassTable` tabulates
(`chi_M mod 2`, `dim H^1`) and (`d_2`, `dim H^1`); the census keeps one table
for the corpus and one for the (F) specimens with at least two periodic
letters on both sides.

These are class counts under recorded conditional theorems (the note labels
H3, FC3+ and P+: recorded proof, conditional on the listed imports, single
prover plus independent adversarial re-derivation within the session, not
machine-checked, independent human review pending). A flag says that the
hypotheses of a clause hold. It is not a certificate of a coincidence rank:
no coincidence rank is computed anywhere in this module.

Not implemented: the divisor condition of Theorem P+ (at every admissible
`n`, factors `r`, `q_1` of `c_n` with `h_n r = (t + 1) q_1` over `F_2`), and
the refinement of Remark (3) after Theorem P of the class note (Lemma S at
the admissible `n < 6`). What the record says those two add on the corpus is
an exploratory scratch observation, not replayable from the repository.

Fail closed
-----------
A substitution that is not PIP3 raises in `build_seed_overlap_tables` (no
field, no verdict). A state cap raises (`refuse to conclude`: an exhausted
budget is not a verdict). A point that is not a state, a cycle whose address
equation fails its replay, an occurrence that is not interior, and an orbit
that closes outside the certified cycles all raise. A search in a box that
is not certified returns a `BoxSearch`, never a verdict. No floating point
is used anywhere.

All `Z[beta]` and state arithmetic is checked (`finite_exact.checked_int` and
the checked cubic operations of `psc.perron_field3`). Determinants, adjugates
and traces of 3x3 integer matrices come from the vendored `Mat3`, which is
unchecked machine-integer arithmetic. For the tile-length matrix its results
are replayed exactly: by the trace-dual check in `stable_radii`, and by the
position of every relative state, which must equal the offset it was solved
from. For the incidence matrix in `fc3_profile` (`det M`, `tr M`) they are
not replayed; its entries are at most the longest image, which is 6 in the
audited image-length domain. Counters and loop indices are plain machine
integers.
"""

from finite_exact.checked_int import checked_abs, checked_add, checked_mul, checked_sub
from finite_exact.closed_interval import IQ
from finite_exact.integer_gcd import gcd_int
from finite_exact.rat_q import Q, q_abs, q_max
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.corpus import STATE_CAP, Specimen
from psc.degree2_sieve import mod2
from psc.exact import (
    eval_int_poly_at_q,
    interval_horner_int,
    midpoint,
    q_floor_abs,
    q_int,
    q_poly,
    q_sign,
    require_iq,
    require_q,
)
from psc.endpoint_core import (
    LetterPair,
    functional_cycle_lengths,
    prefix_endpoint_map,
    recurrent_nonsynchronizing_core,
    suffix_endpoint_map,
)
from psc.field3 import discriminant
from psc.h1_census import h1_profile
from psc.histogram import Histogram
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapTables,
    build_seed_overlap_tables,
    cached_sign,
    incidence_key,
    overlap_children_cached,
)
from psc.periodic_pair import image_sizes
from psc.perron_field3 import (
    CubicElt,
    cubic_add_checked,
    cubic_mul,
    cubic_mul_beta,
    cubic_scale_checked,
    cubic_sub_checked,
)
from psc.perron_root_sign import perron_root_bracket
from psc.real_root_sign import isolate_real_roots
from psc.symmetry import reversed_substitution, substitution_key
from psc.vertex_coincidence import length_matrix, offset_vector

# Fail-closed budget of prototile states visited by one (F) decision. The
# standing corpus stays far below it (the regression bounds the observed peak).
comptime GEOMETRIC_F_STATE_CAP = 2000000

# Census cells: one bit per per-specimen fact.
comptime CELL_F = 1
comptime CELL_DET_ODD = 2
comptime CELL_H1_AT_MOST_4 = 4
comptime CELL_PARITY = 8
comptime CELL_LEFT_TRIVIAL = 16
comptime CELL_RIGHT_TRIVIAL = 32
# Round 2: dim H^1 = 3, and dim H^1 below the bound 3 + |d_2 - 1| of Theorem P+.
comptime CELL_H1_THREE = 64
comptime CELL_RANK_BOUND = 128
comptime CELL_COUNT = 256

# Classes of chi_M mod 2 (three coefficient parities), and the largest
# dim H^1 a class table holds (on three letters dim H^1 <= 7).
comptime CHI_MOD2_CLASSES = 8
comptime MAX_H1_DIMENSION = 9

comptime MAX_PERIOD = 64
comptime MAX_TRANSIENT = 128

# Bisections of every root bracket, the dyadic grid of the square-root upper
# bounds, and the radius beyond which a box is refused rather than scanned.
comptime BRACKET_BITS = 40
comptime SQRT_GRID_BITS = 24
comptime SQRT_STEPS = 5
comptime RADIUS_CAP = 4096


struct PrototileState(ImplicitlyCopyable, Copyable, Movable, Equatable, Hashable, Writable):
    """`(j, v)`: the lattice point `v` seen from the left end of a `j`-tile."""

    var letter: Int
    var v0: Int
    var v1: Int
    var v2: Int

    def __init__(out self, letter: Int, v0: Int, v1: Int, v2: Int):
        self.letter = letter
        self.v0 = v0
        self.v1 = v1
        self.v2 = v2

    def __eq__(self, other: PrototileState) -> Bool:
        return (
            self.letter == other.letter
            and self.v0 == other.v0
            and self.v1 == other.v1
            and self.v2 == other.v2
        )

    def __ne__(self, other: PrototileState) -> Bool:
        return not (self == other)

    def is_vertex(self) -> Bool:
        return self.v0 == 0 and self.v1 == 0 and self.v2 == 0

    def vector(self) -> List[Int]:
        return [self.v0, self.v1, self.v2]

    def precedes(self, other: PrototileState) -> Bool:
        """Lexicographic order on `(letter, v0, v1, v2)`: the base point of a
        cycle is its least state, so a cycle prints the same however it was
        entered."""
        if self.letter != other.letter:
            return self.letter < other.letter
        if self.v0 != other.v0:
            return self.v0 < other.v0
        if self.v1 != other.v1:
            return self.v1 < other.v1
        return self.v2 < other.v2

    def write_to[W: Writer](self, mut w: W):
        w.write("(", self.letter, ";", self.v0, ",", self.v1, ",", self.v2, ")")


struct PrototileStep(ImplicitlyCopyable, Copyable, Movable):
    """`f(state)` with the index of the sub-tile of `sigma(letter)` it used."""

    var child: PrototileState
    var index: Int

    def __init__(out self, child: PrototileState, index: Int):
        self.child = child
        self.index = index


struct PrototileMap(Copyable, Movable):
    """The substitution-local data of `f`, computed once: the exact Perron
    tables, the incidence matrix, the Parikh vector of every proper prefix of
    every image, the tile lengths as a matrix, and the sign cache."""

    var tables: SeedOverlapTables
    var incidence: Mat3
    var prefix_parikh: List[List[Int]]
    var lengths: Mat3
    var signs: Dict[CubicElt, Int]

    def __init__(out self, sigma: List[List[Int]]) raises:
        """Raises unless `sigma` is PIP3 inside the audited image-length
        domain of `build_seed_overlap_tables`."""
        self.tables = build_seed_overlap_tables(sigma)
        self.incidence = Mat3(substitution_incidence(sigma))
        self.prefix_parikh = List[List[Int]]()
        for parent in range(3):
            var running: List[Int] = [0, 0, 0]
            for q in range(len(sigma[parent])):
                self.prefix_parikh.append(running.copy())
                running[sigma[parent][q]] += 1
        self.lengths = length_matrix(self.tables)
        self.signs = Dict[CubicElt, Int]()

    def sign(mut self, x: CubicElt) raises -> Int:
        """Exact sign of `x` at the Perron embedding."""
        return cached_sign(self.tables, self.signs, x)

    def position(self, s: PrototileState) raises -> CubicElt:
        """`<ell, v>` in `Z[beta]`."""
        var x = cubic_scale_checked(self.tables.lengths.at(0), s.v0)
        x = cubic_add_checked(x, cubic_scale_checked(self.tables.lengths.at(1), s.v1))
        return cubic_add_checked(x, cubic_scale_checked(self.tables.lengths.at(2), s.v2))

    def is_state(mut self, s: PrototileState) raises -> Bool:
        """`0 <= <ell, v> < ell_letter`."""
        if s.letter < 0 or s.letter >= 3:
            return False
        var x = self.position(s)
        if self.sign(x) < 0:
            return False
        return self.sign(cubic_sub_checked(x, self.tables.lengths.at(s.letter))) < 0

    def prefix_vector(self, parent: Int, index: Int) raises -> List[Int]:
        """Parikh vector of the length-`index` prefix of `sigma(parent)`."""
        if parent < 0 or parent >= 3 or index < 0 or index >= len(self.tables.sigma[parent]):
            raise Error("prototile state map: prefix outside the image")
        return self.prefix_parikh[self.tables.prefix_starts[parent] + index].copy()

    def apply_incidence(self, v: List[Int]) raises -> List[Int]:
        """`M v`, checked."""
        var out = List[Int]()
        for i in range(3):
            var s = 0
            for k in range(3):
                s = checked_add(s, checked_mul(self.incidence.at(i, k), v[k]))
            out.append(s)
        return out^

    def step(mut self, s: PrototileState) raises -> PrototileStep:
        """`f(s)`. Raises when `s` is not a state: a point outside its tile
        has no sub-tile, and no value is invented for it."""
        var j = s.letter
        if j < 0 or j >= 3:
            raise Error("prototile state map: letter outside 0..2")
        var scaled = cubic_mul_beta(self.tables.field, self.position(s))
        var chosen = -1
        var relative = CubicElt()
        for q in range(len(self.tables.sigma[j])):
            var candidate = cubic_sub_checked(scaled, self.tables.prefix(j, q))
            if self.sign(candidate) < 0:
                break
            chosen = q
            relative = candidate
        if chosen < 0:
            raise Error("prototile state map: negative position, not a state")
        var child = self.tables.sigma[j][chosen]
        if self.sign(cubic_sub_checked(relative, self.tables.lengths.at(child))) >= 0:
            raise Error("prototile state map: position beyond the tile, not a state")
        var mv = self.apply_incidence(s.vector())
        var d = self.prefix_vector(j, chosen)
        var out = PrototileState(
            child, checked_sub(mv[0], d[0]), checked_sub(mv[1], d[1]), checked_sub(mv[2], d[2])
        )
        if self.position(out) != relative:
            raise Error("prototile state map: integer and Z[beta] steps disagree")
        return PrototileStep(out, chosen)


def _scaled(e: IQ, n: Int) raises -> IQ:
    """`n e`, from the two endpoint products."""
    var k = q_int(n)
    if n >= 0:
        return require_iq(IQ(e.lo.mul(k), e.hi.mul(k)), "scaled enclosure")
    return require_iq(IQ(e.hi.mul(k), e.lo.mul(k)), "scaled enclosure")


def _upper_abs(e: IQ) raises -> Q:
    return require_q(q_max(q_abs(e.lo), q_abs(e.hi)), "absolute upper bound")


def _enclosure(x: CubicElt, at: IQ) raises -> IQ:
    return interval_horner_int([x.a0, x.a1, x.a2], at)


def _round_up(x: Q, bits: Int) raises -> Q:
    """A dyadic rational `> x` with denominator `2^bits`, for `x >= 0`."""
    var scale = q_int(1 << bits)
    var whole = q_floor_abs(require_q(x.mul(scale), "dyadic rounding"))
    return require_q(whole.add(q_int(1)).div(scale), "dyadic rounding")


def _sqrt_upper(x: Q) raises -> Q:
    """A rational `r >= sqrt(x)`. `(r + x / r) / 2 >= sqrt(x)` for every
    `r > 0`, so Newton's iteration from a power of two with `r^2 >= x`, rounded
    up at each step, never drops below the root."""
    if q_sign(x) < 0:
        raise Error("geometric (F): square root of a negative bound")
    if q_sign(x) == 0:
        return Q.zero()
    var r = q_int(1)
    var two = q_int(2)
    for _ in range(128):
        if not r.square().lt(x):
            break
        r = require_q(r.mul(two), "sqrt start")
    for _ in range(128):
        var half = require_q(r.div(two), "sqrt start")
        if half.square().lt(x):
            break
        r = half^
    if r.square().lt(x):
        raise Error("geometric (F): square-root start did not bracket the root")
    for _ in range(SQRT_STEPS):
        r = _round_up(require_q(r.add(x.div(r)).div(two), "sqrt step"), SQRT_GRID_BITS)
    return r^


def _floor_radius(x: Q) raises -> Int:
    """`floor(x)` for `0 <= x <= RADIUS_CAP`; a larger box is refused."""
    if q_sign(x) < 0:
        raise Error("geometric (F): negative radius bound")
    var n = 0
    while q_int(n + 1).le(x):
        n += 1
        if n > RADIUS_CAP:
            raise Error("geometric (F): box radius beyond the cap; inconclusive, not a verdict")
    return n


def _trace(chi: List[Int], x: CubicElt) raises -> Int:
    """`Tr_{Q(beta)/Q}(x)`: the power sums are `3`, `-chi_2`, `chi_2^2 - 2 chi_1`."""
    var p1 = checked_sub(0, chi[2])
    var p2 = checked_sub(checked_mul(chi[2], chi[2]), checked_mul(2, chi[1]))
    return checked_add(
        checked_add(checked_mul(3, x.a0), checked_mul(p1, x.a1)), checked_mul(p2, x.a2)
    )


def _cofactor(tables: SeedOverlapTables, z: CubicElt) raises -> CubicElt:
    """`z' z''`, the product of the two other conjugates of `z`:
    `z^2 - Tr(z) z + e_2(z)` with `e_2(z) = (Tr(z)^2 - Tr(z^2)) / 2`."""
    var chi = tables.field.charpoly()
    var square = cubic_mul(tables.field, z, z)
    var t = _trace(chi, z)
    var twice = checked_sub(checked_mul(t, t), _trace(chi, square))
    if twice % 2 != 0:
        raise Error("geometric (F): odd second symmetric function")
    var out = cubic_sub_checked(square, cubic_scale_checked(z, t))
    return cubic_add_checked(out, CubicElt(twice // 2, 0, 0))


def _refined_root(chi: List[Int], lo: Q, hi: Q) raises -> IQ:
    """`BRACKET_BITS` bisections of an isolating bracket of a simple real root."""
    var a = lo.copy()
    var b = hi.copy()
    var fa = q_sign(eval_int_poly_at_q(chi, a))
    var fb = q_sign(eval_int_poly_at_q(chi, b))
    if fa == 0 or fb == 0 or fa == fb:
        raise Error("geometric (F): a conjugate bracket does not isolate a sign change")
    for _ in range(BRACKET_BITS):
        var mid = midpoint(a, b)
        var fm = q_sign(eval_int_poly_at_q(chi, mid))
        if fm == 0:
            raise Error("geometric (F): an irreducible cubic has no rational root")
        if fm == fa:
            a = mid^
        else:
            b = mid^
    return require_iq(IQ(a, b), "conjugate root enclosure")


def _real_moments(xi: IQ) raises -> List[IQ]:
    """Enclosures of the moments of `(a_0 + a_1 xi + a_2 xi^2)^2`, in the order
    `(00, 01, 02, 11, 12, 22)`: `1, 2 xi, 2 xi^2, xi^2, 2 xi^3, xi^4`."""
    var x2 = xi.square()
    var x3 = x2.mul(xi)
    var out = List[IQ]()
    out.append(IQ.singleton(Q.one()))
    out.append(_scaled(xi, 2))
    out.append(_scaled(x2, 2))
    out.append(require_iq(x2, "conjugate moment"))
    out.append(_scaled(x3, 2))
    out.append(require_iq(x2.square(), "conjugate moment"))
    return out^


def _complex_moments(beta: IQ, chi: List[Int]) raises -> List[IQ]:
    """Enclosures of the moments of `y(beta') y(beta'')` for a complex pair,
    in the order `(00, 01, 02, 11, 12, 22)`: `1, e_1, e_1^2 - 2 e_2, e_2,
    e_1 e_2, e_2^2` with `e_1 = beta' + beta'' = -chi_2 - beta` and
    `e_2 = beta' beta'' = beta^2 + chi_2 beta + chi_1`."""
    var e1 = require_iq(IQ.singleton(q_int(-chi[2])).sub(beta), "conjugate sum")
    var e2 = interval_horner_int([chi[1], chi[2], 1], beta)
    var out = List[IQ]()
    out.append(IQ.singleton(Q.one()))
    out.append(e1.copy())
    out.append(require_iq(e1.square().sub(_scaled(e2, 2)), "conjugate moment"))
    out.append(e2.copy())
    out.append(require_iq(e1.mul(e2), "conjugate moment"))
    out.append(require_iq(e2.square(), "conjugate moment"))
    return out^


def _square_modulus(moments: List[IQ], x: CubicElt) raises -> IQ:
    """Enclosure of `|tau(x)|^2 = sum_{i <= j} a_i a_j m_ij`."""
    var a: List[Int] = [x.a0, x.a1, x.a2]
    var total = IQ.singleton(Q.zero())
    var k = 0
    for i in range(3):
        for j in range(i, 3):
            var coefficient = checked_mul(a[i], a[j])
            if coefficient != 0:
                total = total.add(_scaled(moments[k], coefficient))
            k += 1
    return require_iq(total, "conjugate square modulus")


def matrix_digits(tables: SeedOverlapTables) raises -> List[CubicElt]:
    """`<ell, d>` for the digit set `D_M`: every `d != 0` with
    `0 <= d <= M e_j` componentwise and `d != M e_j`, for some letter `j`. It
    contains the Parikh vector of every nonempty proper prefix of every image
    of every substitution with this incidence matrix."""
    var incidence = Mat3(substitution_incidence(tables.sigma))
    var out = List[CubicElt]()
    var seen = Dict[CubicElt, Bool]()
    for j in range(3):
        for d0 in range(incidence.at(0, j) + 1):
            for d1 in range(incidence.at(1, j) + 1):
                for d2 in range(incidence.at(2, j) + 1):
                    var full = (
                        d0 == incidence.at(0, j) and d1 == incidence.at(1, j) and d2 == incidence.at(2, j)
                    )
                    if full or (d0 == 0 and d1 == 0 and d2 == 0):
                        continue
                    var c = cubic_scale_checked(tables.lengths.at(0), d0)
                    c = cubic_add_checked(c, cubic_scale_checked(tables.lengths.at(1), d1))
                    c = cubic_add_checked(c, cubic_scale_checked(tables.lengths.at(2), d2))
                    if c not in seen:
                        seen[c] = True
                        out.append(c)
    return out^


def stable_radii(tables: SeedOverlapTables) raises -> List[Int]:
    """The radii of Lemma B, by outward-rounded rational interval arithmetic:
    `radii[a] >= |v_a|` for every f-periodic state `(j, v)`. Depends on the
    incidence matrix only. Raises when a bound cannot be certified; never
    returns an estimate."""
    var field = tables.field
    var chi = field.charpoly()
    var disc = discriminant(field)
    if disc == 0:
        raise Error("geometric (F): an irreducible cubic has a nonzero discriminant")
    var lengths = List[CubicElt]()
    for a in range(3):
        lengths.append(tables.lengths.at(a))
    var matrix = length_matrix(tables)
    var det = matrix.det()
    if det == 0:
        raise Error("geometric (F): tile lengths are linearly dependent")
    var adj = matrix.adjugate()

    # theta_a = g_a / (det L chi'(beta)), checked exactly through the trace.
    var dual: List[CubicElt] = [CubicElt(chi[1], chi[2], 1), CubicElt(chi[2], 1, 0), CubicElt(1, 0, 0)]
    var g = List[CubicElt]()
    for a in range(3):
        var acc = CubicElt()
        for i in range(3):
            acc = cubic_add_checked(acc, cubic_scale_checked(dual[i], adj.at(a, i)))
        g.append(acc)
    var derivative = CubicElt(chi[1], checked_mul(2, chi[2]), 3)
    var cofactor = _cofactor(tables, derivative)
    var norm = cubic_mul(field, derivative, cofactor)
    if norm.a1 != 0 or norm.a2 != 0 or norm.a0 != checked_sub(0, disc):
        raise Error("geometric (F): N(chi'(beta)) is not minus the discriminant")
    for a in range(3):
        for c in range(3):
            var product = cubic_mul(field, cubic_mul(field, g[a], lengths[c]), cofactor)
            var expected = checked_mul(norm.a0, det) if a == c else 0
            if _trace(chi, product) != expected:
                raise Error("geometric (F): the trace-dual basis failed its exact check")

    # Enclosures of the three embeddings.
    var beta = perron_root_bracket(chi[0], chi[1], chi[2], BRACKET_BITS)
    var slots = List[List[IQ]]()
    var multiplicity = List[Int]()
    if disc < 0:
        slots.append(_complex_moments(beta, chi))
        multiplicity.append(2)
    else:
        var boxes = isolate_real_roots(q_poly(chi), q_int(-1), q_int(1), 2)
        for r in range(2):
            slots.append(_real_moments(_refined_root(chi, boxes[r][0], boxes[r][1])))
            multiplicity.append(1)

    # Perron side: |theta_a| ell_max.
    var chi_prime = _enclosure(derivative, beta)
    if q_sign(chi_prime.lo) <= 0:
        raise Error("geometric (F): chi'(beta) is not certified positive")
    var longest = Q.zero()
    for a in range(3):
        longest = q_max(longest, _upper_abs(_enclosure(lengths[a], beta)))
    var scale = q_int(checked_abs(det))

    # Contracting side, per embedding: sqrt(C^2 / |chi'|^2) / (1 - |tau(beta)|).
    var digits = matrix_digits(tables)
    if len(digits) == 0:
        raise Error("geometric (F): empty digit set")
    var weights = List[Q]()
    for k in range(len(slots)):
        var contraction = _sqrt_upper(slots[k][3].hi)
        var gap = require_q(q_int(1).sub(contraction), "contraction gap")
        if q_sign(gap) <= 0:
            raise Error("geometric (F): a conjugate is not certified inside the unit disc")
        var below = _square_modulus(slots[k], derivative).lo.copy()
        if q_sign(below) <= 0:
            raise Error("geometric (F): |chi'| at a conjugate is not certified positive")
        var widest = Q.zero()
        for d in range(len(digits)):
            widest = q_max(widest, _square_modulus(slots[k], digits[d]).hi)
        var weight = _sqrt_upper(require_q(widest.div(below), "digit weight"))
        weights.append(require_q(weight.mul(q_int(multiplicity[k])).div(gap), "embedding weight"))

    var radii = List[Int]()
    for a in range(3):
        var expanding = require_q(
            _upper_abs(_enclosure(g[a], beta)).mul(longest).div(scale.mul(chi_prime.lo)), "expanding term"
        )
        var contracting = Q.zero()
        for k in range(len(slots)):
            var size = _sqrt_upper(q_max(_square_modulus(slots[k], g[a]).hi, Q.zero()))
            contracting = require_q(contracting.add(size.mul(weights[k]).div(scale)), "contracting term")
        radii.append(_floor_radius(require_q(expanding.add(contracting), "state radius")))
    return radii^


struct StableRadiiCache(Copyable, Movable):
    """`stable_radii` once per incidence matrix: the radii depend on nothing
    else, and the standing corpus has 348 matrices for 4,554 substitutions."""

    var index: Dict[String, Int]
    var radii: List[List[Int]]

    def __init__(out self):
        self.index = Dict[String, Int]()
        self.radii = List[List[Int]]()

    def radii_for(mut self, tables: SeedOverlapTables) raises -> List[Int]:
        var key = incidence_key(tables.sigma)
        if key not in self.index:
            # Build before indexing: a refused box must leave no entry behind.
            var fresh = stable_radii(tables)
            self.index[key] = len(self.radii)
            self.radii.append(fresh^)
        return self.radii[self.index[key]].copy()

    def distinct_matrices(self) -> Int:
        return len(self.radii)


struct InteriorCycle(Copyable, Movable):
    """An f-cycle with `v != 0`, based at its least state:
    `states[t + 1] = f(states[t])` through sub-tile `indices[t]`, cyclically."""

    var states: List[PrototileState]
    var indices: List[Int]

    def __init__(out self, states: List[PrototileState], indices: List[Int]):
        self.states = states.copy()
        self.indices = indices.copy()

    def period(self) -> Int:
        return len(self.states)


struct InteriorAddress(Copyable, Movable):
    """`sigma^period(letter) = P letter Q` with `(M^period - I) vector = p(P)`,
    `P` and `Q` nonempty."""

    var letter: Int
    var vector: List[Int]
    var period: Int
    var prefix_parikh: List[Int]
    var prefix_length: Int
    var image_length: Int

    def __init__(
        out self,
        letter: Int,
        vector: List[Int],
        period: Int,
        prefix_parikh: List[Int],
        prefix_length: Int,
        image_length: Int,
    ):
        self.letter = letter
        self.vector = vector.copy()
        self.period = period
        self.prefix_parikh = prefix_parikh.copy()
        self.prefix_length = prefix_length
        self.image_length = image_length


struct BoxSearch(Copyable, Movable):
    """What walking the candidates of one box found: the interior f-cycles
    their orbits enter, and the size of the search. It is not a verdict and
    has no `holds`. An empty `cycles` says that no orbit from the box of
    `radii` enters an interior cycle; that is property (F) only when the box
    is certified to hold every f-periodic state (Lemma B), and a box named by
    a caller is not."""

    var radii: List[Int]
    var candidates: Int
    var visited: Int
    var cycles: List[InteriorCycle]

    def __init__(out self, radii: List[Int], candidates: Int, visited: Int, cycles: List[InteriorCycle]):
        self.radii = radii.copy()
        self.candidates = candidates
        self.visited = visited
        self.cycles = cycles.copy()


struct GeometricFVerdict(Copyable, Movable):
    """The complete list of interior f-cycles of one substitution. `holds` is
    property (F). `radii`, `candidates` and `visited` are the size of the
    search that Lemma B and Lemma W make exhaustive.

    The constructor runs the search itself, in the box of `stable_radii`
    (through a `StableRadiiCache`), and accepts no box and no `BoxSearch`
    from the caller: a search in any other box stays a `BoxSearch`. Mojo has
    no private fields, so a field overwritten by hand, or a cache filled by
    hand, is outside this guarantee."""

    var holds: Bool
    var radii: List[Int]
    var candidates: Int
    var visited: Int
    var cycles: List[InteriorCycle]

    def __init__(
        out self, mut m: PrototileMap, mut boxes: StableRadiiCache, max_states: Int = GEOMETRIC_F_STATE_CAP
    ) raises:
        """Runs the search itself, in the box `boxes.radii_for(m.tables)`:
        `stable_radii`, once per incidence matrix. No box and no `BoxSearch`
        is accepted from the caller, so a verdict cannot be built from a
        search in a box the caller named. What Mojo cannot prevent, a field
        overwritten by hand or a `StableRadiiCache` filled by hand, is outside
        the contract."""
        var search = interior_cycles_in_box(m, boxes.radii_for(m.tables), max_states)
        self.holds = len(search.cycles) == 0
        self.radii = search.radii.copy()
        self.candidates = search.candidates
        self.visited = search.visited
        self.cycles = search.cycles.copy()

    def first_period(self) -> Int:
        """The least interior period; `0` when (F) holds."""
        var least = 0
        for c in range(len(self.cycles)):
            var k = self.cycles[c].period()
            if least == 0 or k < least:
                least = k
        return least

    def interior_states(self) -> Dict[PrototileState, Int]:
        """Every interior f-periodic state, mapped to its period."""
        var out = Dict[PrototileState, Int]()
        for c in range(len(self.cycles)):
            for t in range(self.cycles[c].period()):
                out[self.cycles[c].states[t]] = self.cycles[c].period()
        return out^


def box_candidates(mut m: PrototileMap, radii: List[Int]) raises -> List[PrototileState]:
    """Every state `(j, v)` with `v != 0` and `|v_a| <= radii[a]`.

    The coordinate with the largest radius is solved for: `<ell, v>` increases
    with it, so `0 <= <ell, v> < ell_max` is an integer interval, found by
    exact monotone scans from the previous row's start."""
    if len(radii) != 3 or radii[0] < 0 or radii[1] < 0 or radii[2] < 0:
        raise Error("geometric (F): malformed box radii")
    var longest = m.tables.lengths.at(0)
    for a in range(1, 3):
        if m.sign(cubic_sub_checked(m.tables.lengths.at(a), longest)) > 0:
            longest = m.tables.lengths.at(a)
    var z = 0
    for a in range(1, 3):
        if radii[a] > radii[z]:
            z = a
    var x = 1 if z == 0 else 0
    var y = 2 if z != 2 else 1
    var out = List[PrototileState]()
    var starts = List[Int](length=2 * radii[y] + 1, fill=0)
    for wx in range(-radii[x], radii[x] + 1):
        for iy in range(2 * radii[y] + 1):
            var w: List[Int] = [0, 0, 0]
            w[x] = wx
            w[y] = iy - radii[y]
            w[z] = starts[iy]
            # least w[z] with <ell, w> >= 0
            if m.sign(m.position(PrototileState(0, w[0], w[1], w[2]))) < 0:
                while m.sign(m.position(PrototileState(0, w[0], w[1], w[2]))) < 0:
                    w[z] += 1
            else:
                while True:
                    w[z] -= 1
                    if m.sign(m.position(PrototileState(0, w[0], w[1], w[2]))) < 0:
                        w[z] += 1
                        break
            starts[iy] = w[z]
            while True:
                var t = m.position(PrototileState(0, w[0], w[1], w[2]))
                if m.sign(cubic_sub_checked(t, longest)) >= 0:
                    break
                var inside = w[z] >= -radii[z] and w[z] <= radii[z]
                if inside and not (w[0] == 0 and w[1] == 0 and w[2] == 0):
                    for j in range(3):
                        if m.sign(cubic_sub_checked(t, m.tables.lengths.at(j))) < 0:
                            out.append(PrototileState(j, w[0], w[1], w[2]))
                w[z] += 1
    return out^


def _based_cycle(states: List[PrototileState], indices: List[Int], first: Int) -> InteriorCycle:
    """`states[first:]` rotated to start at its least state."""
    var k = len(states) - first
    var base = 0
    for t in range(1, k):
        if states[first + t].precedes(states[first + base]):
            base = t
    var rotated = List[PrototileState]()
    var rotated_indices = List[Int]()
    for t in range(k):
        rotated.append(states[first + (base + t) % k])
        rotated_indices.append(indices[first + (base + t) % k])
    return InteriorCycle(rotated, rotated_indices)


def interior_cycles_in_box(
    mut m: PrototileMap, radii: List[Int], max_states: Int = GEOMETRIC_F_STATE_CAP
) raises -> BoxSearch:
    """Every interior f-cycle of the substitution behind `m` that the orbit of
    a candidate of the box of the given radii enters, in particular every one
    that meets the box. A search, not a verdict on (F): only for the certified
    radii of `stable_radii` is this every interior f-cycle (Lemmas B and W of
    the module docstring), and only `decide_geometric_f` and
    `decide_geometric_f_with` say so. Raises when the walk visits more than
    `max_states` states: a capped search is not a verdict."""
    if max_states <= 0:
        raise Error("geometric (F): the state cap must be positive")
    var candidates = box_candidates(m, radii)
    # depth + 1 while on the current walk, 0 once settled
    var mark = Dict[PrototileState, Int]()
    var cycles = List[InteriorCycle]()
    for c in range(len(candidates)):
        if candidates[c] in mark:
            continue
        var path = List[PrototileState]()
        var indices = List[Int]()
        var s = candidates[c]
        while True:
            if s.is_vertex():
                break
            if s in mark:
                var depth = mark[s]
                if depth > 0:
                    cycles.append(_based_cycle(path, indices, depth - 1))
                break
            if len(mark) >= max_states:
                raise Error("geometric (F): state cap reached; inconclusive, not a verdict")
            path.append(s)
            mark[s] = len(path)
            var step = m.step(s)
            indices.append(step.index)
            s = step.child
        for k in range(len(path)):
            mark[path[k]] = 0
    return BoxSearch(radii, len(candidates), len(mark), cycles)


def decide_geometric_f_with(
    mut m: PrototileMap, mut boxes: StableRadiiCache, max_states: Int = GEOMETRIC_F_STATE_CAP
) raises -> GeometricFVerdict:
    """Property (F) for the substitution behind `m`, with every interior
    f-cycle, in the certified box `boxes.radii_for(m.tables)`: `stable_radii`,
    computed once per incidence matrix. Raises when a radius cannot be
    certified and when the state cap is reached."""
    return GeometricFVerdict(m, boxes, max_states)


def decide_geometric_f(
    sigma: List[List[Int]], max_states: Int = GEOMETRIC_F_STATE_CAP
) raises -> GeometricFVerdict:
    """Property (F) for one substitution, with every interior f-cycle, in the
    certified box of `stable_radii`. Raises unless `sigma` is PIP3, when a
    radius cannot be certified, and when the state cap is reached."""
    var m = PrototileMap(sigma)
    var boxes = StableRadiiCache()
    return GeometricFVerdict(m, boxes, max_states)


def interior_address(m: PrototileMap, cycle: InteriorCycle, start: Int = 0) raises -> InteriorAddress:
    """The interior periodic address of `cycle.states[start]`, replayed.

    The `k` sub-tile indices of the cycle compose to one occurrence of the
    letter in `sigma^k(letter)`; its prefix `P` has Parikh vector
    `sum_t M^{k-1-t} p(P_t)` and length `sum_t |sigma^{k-1-t}(P_t)|`. The
    address equation `(M^k - I) v = p(P)` and the interiority of the occurrence
    are checked here and raise on failure."""
    var k = cycle.period()
    if k < 1 or len(cycle.indices) != k or start < 0 or start >= k:
        raise Error("interior address: malformed cycle")
    var sigma = m.tables.sigma.copy()
    var sizes = image_sizes(sigma, k)
    var base = cycle.states[start]
    var parikh: List[Int] = [0, 0, 0]
    var length = 0
    for t in range(k):
        var s = cycle.states[(start + t) % k]
        var q = cycle.indices[(start + t) % k]
        if sigma[s.letter][q] != cycle.states[(start + t + 1) % k].letter:
            raise Error("interior address: the cycle does not follow its sub-tile indices")
        var d = m.prefix_vector(s.letter, q)
        parikh = m.apply_incidence(parikh)
        for a in range(3):
            parikh[a] = checked_add(parikh[a], d[a])
        for c in range(q):
            length = checked_add(length, sizes[k - 1 - t][sigma[s.letter][c]])
    var image = base.vector()
    for _ in range(k):
        image = m.apply_incidence(image)
    var v = base.vector()
    for a in range(3):
        if checked_sub(image[a], v[a]) != parikh[a]:
            raise Error("interior address: (M^k - I) v = p(P) failed its exact replay")
    var total = sizes[k][base.letter]
    if length < 1 or length > total - 2:
        raise Error("interior address: the occurrence is not interior")
    return InteriorAddress(base.letter, v, k, parikh, length, total)


struct LeftmostPrediction(ImplicitlyCopyable, Copyable, Movable):
    """What the interior f-cycles say about `psc.leftmost_chain`."""

    var cycles: Int
    var longest: Int

    def __init__(out self, cycles: Int, longest: Int):
        self.cycles = cycles
        self.longest = longest


def predicted_leftmost_cycles(sigma: List[List[Int]], verdict: GeometricFVerdict) raises -> LeftmostPrediction:
    """`2 * sum gcd(|C|, |G|)` terminal leftmost cycles, the longest of length
    `max lcm(|C|, |G|)`, over interior f-cycles `C` and cycles `G` of the
    first-letter map (the bridge of the module docstring)."""
    var g_cycles = functional_cycle_lengths(prefix_endpoint_map(sigma))
    var count = 0
    var longest = 0
    for c in range(len(verdict.cycles)):
        var k = verdict.cycles[c].period()
        for i in range(len(g_cycles)):
            var d = gcd_int(k, g_cycles[i])
            count += 2 * d
            var l = k // d * g_cycles[i]
            if l > longest:
                longest = l
    return LeftmostPrediction(count, longest)


struct OrbitMemo(Copyable, Movable):
    """Transient lengths of prototile states, memoised along f-orbits.

    `steps[s]` is the least `n` with `f^n(s)` a vertex state, or `-1` when the
    orbit of `s` enters an interior cycle. `certified` is the set of interior
    periodic states `decide_geometric_f` returned; an orbit that closes on a
    state outside it contradicts Lemma B and raises."""

    var steps: Dict[PrototileState, Int]
    var certified: Dict[PrototileState, Int]
    var max_states: Int

    def __init__(out self, verdict: GeometricFVerdict, max_states: Int = GEOMETRIC_F_STATE_CAP) raises:
        if max_states <= 0:
            raise Error("geometric (F): the state cap must be positive")
        self.steps = Dict[PrototileState, Int]()
        self.certified = verdict.interior_states()
        self.max_states = max_states

    def transient(mut self, mut m: PrototileMap, s: PrototileState) raises -> Int:
        if not m.is_state(s):
            raise Error("geometric (F): transient length of a point that is not a state")
        var path = List[PrototileState]()
        var on_path = Dict[PrototileState, Bool]()
        var cur = s
        var base = 0
        while not cur.is_vertex():
            if cur in self.steps:
                base = self.steps[cur]
                break
            if cur in on_path:
                if cur not in self.certified:
                    raise Error(
                        "geometric (F): an orbit closed on an interior cycle outside the certified box"
                    )
                base = -1
                break
            if len(self.steps) + len(path) >= self.max_states:
                raise Error("geometric (F): state cap reached; inconclusive, not a verdict")
            on_path[cur] = True
            path.append(cur)
            cur = m.step(cur).child
        for k in range(len(path) - 1, -1, -1):
            if base >= 0:
                base += 1
            self.steps[path[k]] = base
        return base


def joint_period(h: List[Int], c: Int, d: Int) raises -> Int:
    """Least `m >= 1` with `h^m(c) = c` and `h^m(d) = d`; raises when `c`, `d`
    are not distinct letters periodic under `h`."""
    if c == d or c < 0 or d < 0 or c >= len(h) or d >= len(h):
        raise Error("fixed rays: need two distinct letters")
    var pair = LetterPair(c, d)
    var current = pair.step(h)
    for m in range(1, len(h) * len(h) + 1):
        if current == pair:
            return m
        current = current.step(h)
    raise Error("fixed rays: the letters are not periodic under the first-letter map")


def periodic_first_letter_pairs(sigma: List[List[Int]]) -> List[LetterPair]:
    """The unordered pairs `c < d` of distinct letters periodic under the
    first-letter map: the off-diagonal recurrent core of `g x g`."""
    var core = recurrent_nonsynchronizing_core(prefix_endpoint_map(sigma))
    var out = List[LetterPair]()
    for i in range(len(core)):
        if core[i].a < core[i].b:
            out.append(core[i].copy())
    return out^


struct RayOverlaps(Copyable, Movable):
    """The overlaps of the two `sigma^m`-fixed rays `X_c`, `X_d`: the
    descendants of the prefix-aligned root `(c, d, 0)` at levels divisible by
    the joint period. `nodes` counts the (overlap, level mod period) pairs the
    closure visited, which is what its cap bounds."""

    var period: Int
    var overlaps: List[OverlapState]
    var nodes: Int

    def __init__(out self, period: Int, overlaps: List[OverlapState], nodes: Int):
        self.period = period
        self.overlaps = overlaps.copy()
        self.nodes = nodes


def fixed_ray_overlaps(
    mut m: PrototileMap, c: Int, d: Int, max_states: Int = STATE_CAP
) raises -> RayOverlaps:
    """Closure of the root `(c, d, 0)` under inflation, carrying the level mod
    the joint period. Raises when more than `max_states` (overlap, level)
    nodes are reached: a capped closure is not a verdict."""
    if max_states <= 0:
        raise Error("fixed rays: the state cap must be positive")
    var period = joint_period(prefix_endpoint_map(m.tables.sigma), c, d)
    var phases = Dict[OverlapState, Int]()  # bit r set: reached at a level = r mod period
    var queue = List[OverlapState]()
    var queue_phase = List[Int]()
    var root = OverlapState(c, d, CubicElt())
    phases[root] = 1
    queue.append(root)
    queue_phase.append(0)
    var head = 0
    while head < len(queue):
        var state = queue[head]
        var phase = (queue_phase[head] + 1) % period
        head += 1
        var children = overlap_children_cached(m.tables, m.signs, state)
        for i in range(len(children)):
            var seen = phases[children[i]] if children[i] in phases else 0
            if (seen >> phase) & 1 == 1:
                continue
            if len(queue) >= max_states:
                raise Error("fixed rays: overlap cap reached; inconclusive, not a verdict")
            phases[children[i]] = seen | (1 << phase)
            queue.append(children[i])
            queue_phase.append(phase)
    var out = List[OverlapState]()
    for i in range(len(queue)):
        if queue_phase[i] == 0:
            out.append(queue[i])
    return RayOverlaps(period, out, len(queue))


def _relative_state(mut m: PrototileMap, letter: Int, t: CubicElt) raises -> PrototileState:
    """The state `(letter, v)` with `<ell, v> = t`. `offset_vector` solves for
    `v` with the unchecked `Mat3` determinant and adjugate, so the position of
    the result is replayed in checked `Z[beta]` arithmetic before it is used."""
    var v = offset_vector(m.lengths, t)
    var s = PrototileState(letter, v[0], v[1], v[2])
    if m.position(s) != t:
        raise Error("fixed rays: the offset vector does not replay its position")
    if not m.is_state(s):
        raise Error("fixed rays: a relative state is not a state")
    return s


def relative_states_of(mut m: PrototileMap, rays: RayOverlaps) raises -> List[PrototileState]:
    """The relative states of the vertices of each ray in the tiles of the
    other, both orientations, without repetition and in discovery order."""
    var seen = Dict[PrototileState, Bool]()
    var out = List[PrototileState]()
    for i in range(len(rays.overlaps)):
        var o = rays.overlaps[i]
        var sign = m.sign(o.shift)
        if sign <= 0:
            # the top tile starts inside the bottom tile, at -shift from its left end
            var s = _relative_state(m, o.bottom, cubic_sub_checked(CubicElt(), o.shift))
            if s not in seen:
                seen[s] = True
                out.append(s)
        if sign >= 0:
            var s = _relative_state(m, o.top, o.shift)
            if s not in seen:
                seen[s] = True
                out.append(s)
    return out^


def fixed_ray_relative_states(
    mut m: PrototileMap, c: Int, d: Int, max_states: Int = STATE_CAP
) raises -> List[PrototileState]:
    """Every relative state of the two fixed rays through `c` and `d`."""
    return relative_states_of(m, fixed_ray_overlaps(m, c, d, max_states))


struct PairTransient(Copyable, Movable):
    """Theorem FC1 for one pair of periodic first letters. `overlaps` and
    `relative_states` are the sizes of the two exact finite sets, `nodes` the
    size of the closure behind them. `transient` is the largest transient
    length among the relative states that reach a vertex state; `absorbed`
    counts those that never do."""

    var first: Int
    var second: Int
    var period: Int
    var nodes: Int
    var overlaps: Int
    var relative_states: Int
    var absorbed: Int
    var transient: Int

    def __init__(
        out self,
        first: Int,
        second: Int,
        period: Int,
        nodes: Int,
        overlaps: Int,
        relative_states: Int,
        absorbed: Int,
        transient: Int,
    ):
        self.first = first
        self.second = second
        self.period = period
        self.nodes = nodes
        self.overlaps = overlaps
        self.relative_states = relative_states
        self.absorbed = absorbed
        self.transient = transient

    def all_reach_vertices(self) -> Bool:
        return self.absorbed == 0


def pair_transient(
    mut m: PrototileMap, mut memo: OrbitMemo, c: Int, d: Int, max_states: Int = STATE_CAP
) raises -> PairTransient:
    var rays = fixed_ray_overlaps(m, c, d, max_states)
    var states = relative_states_of(m, rays)
    var absorbed = 0
    var longest = 0
    for i in range(len(states)):
        var n = memo.transient(m, states[i])
        if n < 0:
            absorbed += 1
        elif n > longest:
            longest = n
    return PairTransient(
        c, d, rays.period, rays.nodes, len(rays.overlaps), len(states), absorbed, longest
    )


def principal_minor_sum(m: Mat3) raises -> Int:
    """`e_2(M)`: the sum of the three principal 2x2 minors, `tr Lambda^2 M`.
    It equals `m.charpoly()[1]`; it is computed here in checked arithmetic,
    which the vendored `Mat3.charpoly` is not, and the regression asserts the
    agreement."""
    var total = 0
    for i in range(3):
        for j in range(i + 1, 3):
            total = checked_add(
                total,
                checked_sub(checked_mul(m.at(i, i), m.at(j, j)), checked_mul(m.at(i, j), m.at(j, i))),
            )
    return total


def periodic_letter_count(h: List[Int]) -> Int:
    """Number of letters on a cycle of the self-map `h`."""
    var lengths = functional_cycle_lengths(h)
    var n = 0
    for i in range(len(lengths)):
        n += lengths[i]
    return n


def chi_mod2_code(determinant: Int, trace: Int, e2: Int) -> Int:
    """The class of `chi_M mod 2 = t^3 + a t^2 + b t + c` as `4a + 2b + c`,
    with `a, b, c` the parities of `tr M`, `e_2(M)`, `det M`."""
    return 4 * mod2(trace) + 2 * mod2(e2) + mod2(determinant)


def nonzero_roots_mod2(code: Int) raises -> Int:
    """`d_2 = 3 - ord_t(t^3 + a t^2 + b t + c)` for the class `4a + 2b + c`:
    the number of nonzero roots over an algebraic closure of `F_2`, with
    multiplicity. Raises on a code outside `0..7`."""
    if code < 0 or code >= CHI_MOD2_CLASSES:
        raise Error("chi_M mod 2: class code outside 0..7")
    if code & 1 == 1:
        return 3
    if code & 2 == 2:
        return 2
    if code & 4 == 4:
        return 1
    return 0


struct FC3Profile(ImplicitlyCopyable, Copyable, Movable):
    """The arithmetic facts Theorems P and FC3, and Theorems H3, FC3+ and P+
    of round 2, read off one substitution. The clause methods say that the
    hypotheses of a clause hold; none of them is a certificate of a
    coincidence rank."""

    var determinant: Int
    var trace: Int
    var e2: Int
    var h1_dimension: Int
    var left_periodic: Int
    var right_periodic: Int

    def __init__(
        out self,
        determinant: Int,
        trace: Int,
        e2: Int,
        h1_dimension: Int,
        left_periodic: Int,
        right_periodic: Int,
    ):
        self.determinant = determinant
        self.trace = trace
        self.e2 = e2
        self.h1_dimension = h1_dimension
        self.left_periodic = left_periodic
        self.right_periodic = right_periodic

    def det_odd(self) -> Bool:
        return mod2(self.determinant) == 1

    def cohomology_clause(self) -> Bool:
        """`dim H^1 <= 4`, the complement of Barge's bound `2d - 1 = 5`."""
        return self.h1_dimension <= 4

    def parity_clause(self) -> Bool:
        """`tr M != e_2(M) (mod 2)`."""
        return mod2(self.trace) != mod2(self.e2)

    def left_trivial(self) -> Bool:
        return self.left_periodic < 2

    def right_trivial(self) -> Bool:
        return self.right_periodic < 2

    def endpoint_trivial(self) -> Bool:
        """Clause (a'): an endpoint map with fewer than two periodic letters,
        i.e. eventually constant. Clause (a) of Theorem FC3 (`nu_L = 1` or
        `nu_R = 1`) is wider and is not evaluated in this module."""
        return self.left_trivial() or self.right_trivial()

    def arithmetic_clause(self) -> Bool:
        """Clauses (b) or (c): `det M` odd and (`dim H^1 <= 4` or the parity
        clause). The note's Theorem P, conditional on its imports, reads this
        as excluding coincidence rank 2; nothing of the kind is decided here."""
        return self.det_odd() and (self.cohomology_clause() or self.parity_clause())

    def chi_mod2(self) -> Int:
        """The class of `chi_M mod 2`: `4 (tr M) + 2 e_2(M) + det M` on parities."""
        return chi_mod2_code(self.determinant, self.trace, self.e2)

    def d2(self) -> Int:
        """`d_2 = 3 - ord_t(chi_M mod 2)`: `3` for odd `det M`, else `2` for
        odd `e_2(M)`, else `1` for odd `tr M`, else `0`."""
        if mod2(self.determinant) == 1:
            return 3
        if mod2(self.e2) == 1:
            return 2
        if mod2(self.trace) == 1:
            return 1
        return 0

    def h1_three(self) -> Bool:
        """Clause (d): `dim H^1 = 3`, for every determinant (Theorem H3)."""
        return self.h1_dimension == 3

    def rank_two_dimension_bound(self) -> Int:
        """`3 + |d_2 - 1|`: by Theorem P+ coincidence rank 2 needs
        `dim H^1` at least this."""
        var d = self.d2()
        return 3 + (d - 1 if d >= 1 else 1 - d)

    def dimension_clause(self) -> Bool:
        """Clause (e): `dim H^1 < 3 + |d_2 - 1|`, the dimension bound of
        Theorem P+ fails. For odd determinant this is `dim H^1 <= 4`."""
        return self.h1_dimension < self.rank_two_dimension_bound()

    def rank_two_excluded(self) -> Bool:
        """The hypotheses under which the recorded theorems exclude
        coincidence rank 2 without the divisor condition of Theorem P+: (d),
        (e), or odd determinant with the parity clause (c). That is: odd
        determinant and (`dim H^1 <= 4` or `tr M != e_2(M)`), or even
        determinant and `dim H^1 = 3`. Membership in a class; no coincidence
        rank is computed."""
        return self.h1_three() or self.dimension_clause() or (self.det_odd() and self.parity_clause())

    def cell(self, holds: Bool) -> Int:
        var key = 0
        if holds:
            key |= CELL_F
        if self.det_odd():
            key |= CELL_DET_ODD
        if self.cohomology_clause():
            key |= CELL_H1_AT_MOST_4
        if self.parity_clause():
            key |= CELL_PARITY
        if self.left_trivial():
            key |= CELL_LEFT_TRIVIAL
        if self.right_trivial():
            key |= CELL_RIGHT_TRIVIAL
        if self.h1_three():
            key |= CELL_H1_THREE
        if self.dimension_clause():
            key |= CELL_RANK_BOUND
        return key


def fc3_profile_of(m: PrototileMap) raises -> FC3Profile:
    """The profile of the substitution behind `m`. A `PrototileMap` exists
    only for PIP3 input inside the audited image-length domain, so the PIP3
    gate has been passed."""
    var sigma = m.tables.sigma.copy()
    return FC3Profile(
        m.incidence.det(),
        m.incidence.trace(),
        principal_minor_sum(m.incidence),
        h1_profile(sigma).dimension,
        periodic_letter_count(prefix_endpoint_map(sigma)),
        periodic_letter_count(suffix_endpoint_map(sigma)),
    )


def fc3_profile(sigma: List[List[Int]]) raises -> FC3Profile:
    """The profile of `sigma`. Raises unless `sigma` is PIP3 (the gate of
    `PrototileMap`). Theorems P and FC3 are statements about PIP3, and FC3
    needs (F) as well; outside PIP3 the clauses mean nothing: the reducible
    strict control 011/120/2012 has odd determinant and `dim H^1 = 3`, so it
    would satisfy clause (b), and it has a strict system."""
    var m = PrototileMap(sigma)
    return fc3_profile_of(m)


struct ClassTable(Copyable, Movable):
    """Specimens by arithmetic class and `dim H^1`, two ways:
    `chi_dimension`, key `10 * chi_mod2 + dim H^1`, and `d2_dimension`, key
    `10 * d_2 + dim H^1`. `dim H^1` must lie in `3..MAX_H1_DIMENSION`; anything
    else raises. Counts of classes, nothing more."""

    var chi_dimension: Histogram
    var d2_dimension: Histogram

    def __init__(out self):
        self.chi_dimension = Histogram(10 * CHI_MOD2_CLASSES)
        self.d2_dimension = Histogram(40)

    def record(mut self, profile: FC3Profile) raises:
        var dimension = profile.h1_dimension
        if dimension < 3 or dimension > MAX_H1_DIMENSION:
            raise Error("dim H^1 outside the class table")
        self.chi_dimension.record(10 * profile.chi_mod2() + dimension)
        self.d2_dimension.record(10 * profile.d2() + dimension)

    def count(self, code: Int, dimension: Int) -> Int:
        """Specimens with `chi_M mod 2` of class `code` and that `dim H^1`."""
        if code < 0 or code >= CHI_MOD2_CLASSES or dimension < 3 or dimension > MAX_H1_DIMENSION:
            return 0
        return self.chi_dimension.count(10 * code + dimension)

    def d2_count(self, d2: Int, dimension: Int) -> Int:
        """Specimens with that `d_2` and that `dim H^1`."""
        if d2 < 0 or d2 > 3 or dimension < 3 or dimension > MAX_H1_DIMENSION:
            return 0
        return self.d2_dimension.count(10 * d2 + dimension)

    def parity_count(self, odd: Bool, dimension: Int) -> Int:
        """Specimens with `det M` of that parity and that `dim H^1`, summed
        over the classes of `chi_M mod 2` (odd constant term or not)."""
        var n = 0
        for code in range(CHI_MOD2_CLASSES):
            if (code & 1 == 1) == odd:
                n += self.count(code, dimension)
        return n

    def total(self) -> Int:
        return self.chi_dimension.total()


struct GeometricFCensus(Copyable, Movable):
    """Per-specimen facts over a corpus, folded into order-independent tables.

    `cells` is keyed by the `CELL_*` bits. `first_period` is the least interior
    period over the specimens where (F) fails. `residual_determinant` (key
    `det + 8`) covers the (F) specimens reached by none of the clauses (a'),
    (b), (c) evaluated here; clause (a) of Theorem FC3 is not evaluated, so
    this is not "reached by no clause of FC3".
    `transients` is the pair transient `N` over the pairs of periodic first
    letters of (F) specimens; `nonf_pairs_absorbed` counts the pairs of the
    other specimens with a relative state absorbed by an interior cycle.
    `f_pairs_absorbed` is kept for the report line and cannot be nonzero: on
    an (F) specimen the certificate is empty, so an absorbed orbit raises in
    `OrbitMemo.transient` before it is counted. The raise is the guard.
    `peak_candidates`, `peak_visited` and `peak_nodes` are the largest searches
    met, to be read against the caps. `holds[s]`, `radii[s]`,
    `cycle_counts[s]` and `leftmost_predicted[s]` are (F), the certified box
    it was decided in, the number of interior f-cycles and the predicted
    number of terminal leftmost cycles of `corpus[s]`. `matrices` is the
    number of distinct incidence matrices and `matrix_radius_sum` the sum of
    the three radii over them.

    Round 2: `classes` tabulates every specimen by (`chi_M mod 2`, `dim H^1`)
    and (`d_2`, `dim H^1`); `open_classes` the (F) specimens with at least two
    periodic letters on both sides (clause (a') fails). `rank_two_excluded`
    and `open_rank_two_excluded` count `FC3Profile.rank_two_excluded` on the
    same two sets: specimens that meet the hypotheses, not certificates."""

    var total: Int
    var cells: Histogram
    var first_period: Histogram
    var interior_cycles: Histogram
    var residual_determinant: Histogram
    var transients: Histogram
    var classes: ClassTable
    var open_classes: ClassTable
    var rank_two_excluded: Int
    var open_rank_two_excluded: Int
    var holds: List[Bool]
    var radii: List[List[Int]]
    var cycle_counts: List[Int]
    var leftmost_predicted: List[Int]
    var matrices: Int
    var matrix_radius_sum: Int
    var reversal_mismatches: Int
    var reversal_missing: Int
    var interior_cycle_total: Int
    var interior_state_total: Int
    var longest_period: Int
    var leftmost_cycles: Int
    var leftmost_longest: Int
    var leftmost_specimens: Int
    var f_pairs: Int
    var f_pairs_absorbed: Int
    var f_relative_states: Int
    var nonf_pairs: Int
    var nonf_pairs_absorbed: Int
    var nonf_relative_states: Int
    var peak_candidates: Int
    var peak_visited: Int
    var peak_nodes: Int

    def __init__(out self):
        self.total = 0
        self.cells = Histogram(CELL_COUNT)
        self.first_period = Histogram(MAX_PERIOD)
        self.interior_cycles = Histogram(MAX_PERIOD)
        self.residual_determinant = Histogram(16)
        self.transients = Histogram(MAX_TRANSIENT)
        self.classes = ClassTable()
        self.open_classes = ClassTable()
        self.rank_two_excluded = 0
        self.open_rank_two_excluded = 0
        self.holds = List[Bool]()
        self.radii = List[List[Int]]()
        self.cycle_counts = List[Int]()
        self.leftmost_predicted = List[Int]()
        self.matrices = 0
        self.matrix_radius_sum = 0
        self.reversal_mismatches = 0
        self.reversal_missing = 0
        self.interior_cycle_total = 0
        self.interior_state_total = 0
        self.longest_period = 0
        self.leftmost_cycles = 0
        self.leftmost_longest = 0
        self.leftmost_specimens = 0
        self.f_pairs = 0
        self.f_pairs_absorbed = 0
        self.f_relative_states = 0
        self.nonf_pairs = 0
        self.nonf_pairs_absorbed = 0
        self.nonf_relative_states = 0
        self.peak_candidates = 0
        self.peak_visited = 0
        self.peak_nodes = 0

    def count_where(self, mask: Int, value: Int) -> Int:
        """Number of specimens whose cell agrees with `value` on `mask`."""
        var n = 0
        for key in range(CELL_COUNT):
            if key & mask == value:
                n += self.cells.count(key)
        return n


def geometric_f_census(corpus: List[Specimen]) raises -> GeometricFCensus:
    """One pass over `corpus`: (F) with every interior cycle and its replayed
    address, the leftmost-cycle prediction, Theorem FC1 on every pair of
    periodic first letters, the arithmetic cells and the round-2 class
    tables; then reversal invariance of (F) inside the corpus."""
    var out = GeometricFCensus()
    var index = Dict[String, Int]()
    var boxes = StableRadiiCache()
    for s in range(len(corpus)):
        var sigma = corpus[s].sigma.copy()
        index[substitution_key(sigma)] = s
        var m = PrototileMap(sigma)
        var verdict = decide_geometric_f_with(m, boxes)
        out.total += 1
        out.holds.append(verdict.holds)
        out.radii.append(verdict.radii.copy())
        out.cycle_counts.append(len(verdict.cycles))
        if verdict.candidates > out.peak_candidates:
            out.peak_candidates = verdict.candidates
        if verdict.visited > out.peak_visited:
            out.peak_visited = verdict.visited
        out.interior_cycles.record(len(verdict.cycles))
        for c in range(len(verdict.cycles)):
            # every state of every interior cycle replays its address equation
            for t in range(verdict.cycles[c].period()):
                _ = interior_address(m, verdict.cycles[c], t)
            out.interior_cycle_total += 1
            out.interior_state_total += verdict.cycles[c].period()
            if verdict.cycles[c].period() > out.longest_period:
                out.longest_period = verdict.cycles[c].period()
        if not verdict.holds:
            out.first_period.record(verdict.first_period())
        var prediction = predicted_leftmost_cycles(sigma, verdict)
        out.leftmost_predicted.append(prediction.cycles)
        out.leftmost_cycles += prediction.cycles
        if prediction.cycles > 0:
            out.leftmost_specimens += 1
        if prediction.longest > out.leftmost_longest:
            out.leftmost_longest = prediction.longest

        var profile = fc3_profile_of(m)
        out.cells.record(profile.cell(verdict.holds))
        if verdict.holds and not profile.endpoint_trivial() and not profile.arithmetic_clause():
            if profile.determinant < -8 or profile.determinant > 7:
                raise Error("determinant outside the census table")
            out.residual_determinant.record(profile.determinant + 8)
        out.classes.record(profile)
        if profile.rank_two_excluded():
            out.rank_two_excluded += 1
        if verdict.holds and not profile.endpoint_trivial():
            out.open_classes.record(profile)
            if profile.rank_two_excluded():
                out.open_rank_two_excluded += 1

        var memo = OrbitMemo(verdict)
        var pairs = periodic_first_letter_pairs(sigma)
        for p in range(len(pairs)):
            var t = pair_transient(m, memo, pairs[p].a, pairs[p].b)
            if t.nodes > out.peak_nodes:
                out.peak_nodes = t.nodes
            if verdict.holds:
                out.f_pairs += 1
                out.f_relative_states += t.relative_states
                if t.absorbed > 0:
                    out.f_pairs_absorbed += 1
                out.transients.record(t.transient)
            else:
                out.nonf_pairs += 1
                out.nonf_relative_states += t.relative_states
                if t.absorbed > 0:
                    out.nonf_pairs_absorbed += 1

    out.matrices = boxes.distinct_matrices()
    for k in range(len(boxes.radii)):
        out.matrix_radius_sum += boxes.radii[k][0] + boxes.radii[k][1] + boxes.radii[k][2]

    for s in range(len(corpus)):
        var key = substitution_key(reversed_substitution(corpus[s].sigma))
        if key not in index:
            out.reversal_missing += 1
        elif out.holds[index[key]] != out.holds[s]:
            out.reversal_mismatches += 1
    return out^
