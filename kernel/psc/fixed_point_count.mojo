"""Fixed points of the inflation on a one-dimensional substitution tiling
space, counted exactly in two ways (Theorem FP).

docs/c4-rank-two-wall-2026-11-16.md, Theorem FP. Let `sigma` be a primitive
substitution on `d >= 2` letters with incidence matrix `M`
(`M[i][j]` = occurrences of `i` in `sigma(j)`), `ell` a positive left Perron
vector (tile lengths) and `beta > 1` its eigenvalue. `Omega` is the space of
tilings of the line by half-open tiles `[y, y + ell_a)` of type `a` all of
whose finite patches are legal (occur in some `sigma^k(c)`), and `Phi` the
inflation: scale by `beta`, then replace each tile of type `a` by the patch
`sigma(a)`. `g` and `g_R` are the first- and last-letter maps.

    Theorem FP.  For every n >= 1,
    |Fix(Phi^n)| = tr(M^n) - #Fix(g^n) - #Fix(g_R^n)
                   + #{ legal two-letter words ba : g_R^n(b) = b, g^n(a) = a }.

Only primitivity is used: no irreducibility, no Pisot hypothesis, and
periodic primitive substitutions are included. Attribution: this is the
count behind the Anderson--Putnam zeta function of a substitution tiling
space, restated; it is standard and no novelty is claimed. The record of this
increment located it through secondary citations; the primary text was not
read. Status: recorded proof (elementary, no import), single prover plus
independent adversarial re-derivation within the session of 2026-11-16, not
machine-checked, independent human review pending.

Two computations
----------------
`fixed_point_formula` evaluates the right-hand side: `tr(M^n)` from checked
powers of the incidence matrix (`psc.periodic_pair.incidence_power` on three
letters; on other alphabets `matrix_power`, the same checked `matmul` product
of `finite_linear_algebra.integer_matrix`, and the regression compares the
two on every three-letter fixture), the two endpoint maps iterated `n` times,
and the legal two-letter words of `psc.h1_census.legal_two_words` (the
closure of the two-factors of the images under
`xy -> last(sigma x) first(sigma y)`). No word `sigma^n(a)` is built.

`literal_fixed_tilings` counts the fixed tilings from the definition, with no
trace, no endpoint map and no classification into types. A tiling is a
bi-infinite word `u` and the position `x` in `[0, ell_{u_0})` of the origin
in its tile `u_0`. `Phi^n` places the patch `sigma^n(u_0)` at `-beta^n x`;
the origin falls in its `k`-th tile, where `ell(P_k) <= beta^n x < ell(P_{k+1})`
for the prefixes `P_k` of `sigma^n(u_0)`, at position `beta^n x - ell(P_k)`.
A *pointed window* is `(w, k)` with `w = u_{-r} ... u_r` a legal word of
length `2r + 1` and `0 <= k < |sigma^n(u_0)|`; it is *reproduced* when the
`2r + 1` letters of `sigma^n(u_{-r}) ... sigma^n(u_r)` centred at the `k`-th
letter of `sigma^n(u_0)` spell `w` again. Each image is nonempty, so those
letters lie inside that word and the test is a comparison of finite words.

*Lemma L (reproduced windows are the fixed tilings).* For `r >= 1`,
`T -> (its window, its k)` is a bijection from `Fix(Phi^n)` onto the
reproduced pointed windows with `k <= |sigma^n(u_0)| - 2`.

1. If `Phi^n(T) = T`, the tile at the origin and its neighbours are the same
   before and after, so the window is reproduced, and
   `x = beta^n x - ell(P_k)` gives `x = ell(P_k) / (beta^n - 1)`. With
   `sigma^n(u_0) = P_k u_0 S_k`, `ell(P_k) + ell_{u_0} + ell(S_k) = beta^n ell_{u_0}`,
   so `x < ell_{u_0}` exactly when `S_k` is nonempty: `k` is not the last
   index.
2. Conversely let `(w, k)` be reproduced with `k` not last, put
   `x = ell(P_k) / (beta^n - 1)` in `[0, ell_{u_0})` and let `Q_0` be the patch
   `w` with its middle tile at `[-x, ell_{u_0} - x)`. The `k`-th tile of
   `sigma^n(u_0)` placed at `-beta^n x` starts at `-beta^n x + ell(P_k) = -x`,
   so `Q_0` is a sub-patch of `Phi^n(Q_0)`, and `Q_i = Phi^{ni}(Q_0)` increase.
   The support of `Q_0` contains the origin in its interior (there is a tile
   on each side of the middle one), so the supports `beta^{ni} supp(Q_0)`
   exhaust the line. The union is a tiling, legal because `w` is, fixed by
   `Phi^n`, with window `w` and index `k`; any fixed tiling with that pointed
   window contains `Q_0`, hence every `Q_i`, hence is this one.
3. Two reproduced pointed windows of one tiling have the same `w` and the
   same `x`, hence the same `k` (`ell > 0`).

So `|Fix(Phi^n)|` is the number of reproduced pointed windows with `k` not
last, for every radius `r >= 1`; the regression compares `r = 1` and `r = 2`.
Tile lengths are never computed: the count is on words. Status of Lemma L:
recorded proof in this docstring, not machine-checked, independent human
review pending.

Candidates on prototiles and on seams, and the ones that coincide
-----------------------------------------------------------------
A reproduced pointed window is a fixed point of the piecewise expanding map
of the *closed* prototile `u_0`, at `ell(P_k) / (beta^n - 1)` in
`[0, ell_{u_0}]`, together with its two neighbours. `literal_fixed_tilings`
enumerates all of them, the last index included, and sorts them:

- `0 < k <` last: an interior fixed point, one tiling (`interior`, by letter);
- `k = 0`: the origin is the left vertex of the tile, the seam is
  `u_{-1}.u_0` (`left_vertex`, `left_seams`);
- `k =` last: the origin is the right vertex, the seam is `u_0.u_1`
  (`right_vertex`, `right_seams`).

A tiling whose origin is a vertex is one tiling and two candidates: it is
seen once from the tile on its right (`k = 0`) and once from the tile on its
left (`k =` last). Identifying them is the half-open convention, and
`total()` counts `interior + left_vertex`. That the two lists of seams are
equal is checked on every call and raises otherwise.

The windows come from `substitution_dynamics.return_lattice.factor_set` (the
closure of the windows of a seed word under `u -> windows of sigma(u)`), and
the words `sigma^n(a)` from literal substitution. The two functions share
only the validation gate `primitive_incidence`.

What the counts are not
-----------------------
These are counts of periodic points of the inflation. They certify no
coincidence rank, no strong coincidence and no pure discrete spectrum, and
change no claim status. The use the record makes of them (Theorems TT and NI
of the rank-two note compare `tr N^n` with `tr M^{Pn}` through this count)
is a written proof, not this module.

Fail closed (all in the "refuse to conclude" column)
----------------------------------------------------
An erasing image, a letter outside the alphabet, fewer than two or more than
`MAX_LETTERS` letters and a non-primitive incidence matrix raise: outside
primitivity the language of the formula and the hull of the tilings are not
the objects of the theorem. A power below one raises. All integer arithmetic
of the formula is checked (`finite_exact.checked_int`, and the checked
`matmul`): an unrepresentable trace raises instead of wrapping. The literal
count raises when an image `sigma^n(a)` is longer than its word cap (an
exhausted budget is not a count), when a letter is its own `n`-th image, and
when the left and right seam lists differ. It also raises on a window radius
outside `1..MAX_RADIUS`, on a word cap below one, and on two impossible
states: an image whose length is not the one its incidence matrix gives, and
a window that leaves its patch. Nothing here deletes or overwrites anything,
so every refusal is a refusal to proceed.
"""

from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from finite_linear_algebra.integer_matrix import is_primitive, matmul
from psc.h1_census import MAX_LETTERS, legal_two_words
from psc.periodic_pair import incidence_power
from substitution_dynamics.return_lattice import factor_set
from substitution_dynamics.substitution import Substitution

# The longest image `sigma^n(a)` the literal count builds before it refuses.
comptime LITERAL_WORD_CAP = 1000000

# Window radii of the literal count: one neighbour on each side, or two.
comptime MAX_RADIUS = 2


def primitive_incidence(sigma: List[List[Int]]) raises -> List[Int]:
    """The row-major incidence matrix of `sigma`, after the gate of Theorem
    FP: non-erasing images over the alphabet `0..d-1`, `2 <= d <= MAX_LETTERS`,
    and a primitive incidence matrix. Raises otherwise."""
    var s = Substitution.checked(sigma)
    if s.size < 2:
        raise Error("fixed-point count: Theorem FP needs at least two letters")
    if s.size > MAX_LETTERS:
        raise Error("fixed-point count: alphabet size must lie in 2.." + String(MAX_LETTERS))
    var m = s.incidence()
    if not is_primitive(m, s.size):
        raise Error("fixed-point count: the substitution is not primitive")
    return m^


def _require_power(n: Int) raises:
    if n < 1:
        raise Error("fixed-point count: the power of the inflation is at least one")


def iterated_map(h: List[Int], n: Int) -> List[Int]:
    """`h^n` as a list, for a self-map `h` of `0..len(h)-1` and `n >= 0`."""
    var out = List[Int]()
    for a in range(len(h)):
        var x = a
        for _ in range(n):
            x = h[x]
        out.append(x)
    return out^


def matrix_power(m: List[Int], size: Int, n: Int) raises -> List[Int]:
    """`M^n` for `n >= 1` and a row-major `size x size` matrix, by `n - 1`
    checked products: `psc.periodic_pair.incidence_power` without the fixed
    dimension."""
    _require_power(n)
    var p = m.copy()
    for _ in range(n - 1):
        p = matmul(p, m, size)
    return p^


def _incidence_power(sigma: List[List[Int]], m: List[Int], size: Int, n: Int) raises -> List[Int]:
    """`M^n`, row-major: the existing three-letter helper where it applies,
    `matrix_power` otherwise. Both are checked."""
    if size == 3:
        return incidence_power(sigma, n).e.copy()
    return matrix_power(m, size, n)


struct FixedPointCount(Copyable, Movable):
    """The terms of Theorem FP at one power `n`.

    `trace = tr(M^n)`; `first_fixed = #Fix(g^n)`; `last_fixed = #Fix(g_R^n)`;
    `seam_keys` lists `d * b + a`, increasing, for the legal two-letter words
    `ba` with `g_R^n(b) = b` and `g^n(a) = a`, and `seams` is their number.
    `interior[j] = (M^n)_{jj} - [g^n(j) = j] - [g_R^n(j) = j]` is the number of
    occurrences of `j` strictly inside `sigma^n(j)`, read off the matrix."""

    var power: Int
    var trace: Int
    var first_fixed: Int
    var last_fixed: Int
    var seams: Int
    var interior: List[Int]
    var seam_keys: List[Int]

    def __init__(
        out self,
        power: Int,
        trace: Int,
        first_fixed: Int,
        last_fixed: Int,
        interior: List[Int],
        seam_keys: List[Int],
    ):
        self.power = power
        self.trace = trace
        self.first_fixed = first_fixed
        self.last_fixed = last_fixed
        self.seams = len(seam_keys)
        self.interior = interior.copy()
        self.seam_keys = seam_keys.copy()

    def total(self) raises -> Int:
        """`|Fix(Phi^n)| = tr(M^n) - #Fix(g^n) - #Fix(g_R^n) + seams`."""
        return checked_add(
            checked_sub(checked_sub(self.trace, self.first_fixed), self.last_fixed), self.seams
        )


def fixed_point_formula(sigma: List[List[Int]], n: Int) raises -> FixedPointCount:
    """The right-hand side of Theorem FP for the primitive `sigma` at the
    power `n >= 1`, from the incidence matrix, the endpoint maps and the
    legal two-letter words. Raises on input outside the gate of
    `primitive_incidence`, on `n < 1` and on an unrepresentable integer."""
    _require_power(n)
    var m = primitive_incidence(sigma)
    var size = len(sigma)
    var s = Substitution(sigma.copy(), size)
    var p = _incidence_power(sigma, m, size, n)
    var first = iterated_map(s.prefix_endpoint_map(), n)
    var last = iterated_map(s.suffix_endpoint_map(), n)
    var trace = 0
    var first_fixed = 0
    var last_fixed = 0
    var interior = List[Int]()
    for j in range(size):
        var inside = p[size * j + j]
        trace = checked_add(trace, inside)
        if first[j] == j:
            first_fixed += 1
            inside = checked_sub(inside, 1)
        if last[j] == j:
            last_fixed += 1
            inside = checked_sub(inside, 1)
        if inside < 0:
            # sigma^n(j) = j: the first and the last occurrence are one.
            raise Error("fixed-point count: a letter is its own n-th image, impossible for a primitive substitution")
        interior.append(inside)
    var legal = legal_two_words(sigma)
    var seam_keys = List[Int]()
    for b in range(size):
        for a in range(size):
            if legal[size * b + a] and last[b] == b and first[a] == a:
                seam_keys.append(size * b + a)
    return FixedPointCount(n, trace, first_fixed, last_fixed, interior, seam_keys)


def image_lengths(m: List[Int], size: Int, n: Int, word_cap: Int) raises -> List[Int]:
    """`|sigma^n(a)|` for every letter, from the incidence matrix `m`:
    `|sigma^{k+1}(a)| = sum_i |sigma^k(i)| M[i][a]`, checked. Raises as soon
    as a length passes `word_cap`; the lengths do not decrease with `k`, so
    the image at level `n` would pass it too."""
    if word_cap < 1:
        raise Error("fixed-point count: the word cap must be positive")
    var lengths = List[Int](length=size, fill=1)
    for _ in range(n):
        var longer = List[Int]()
        for a in range(size):
            var total = 0
            for i in range(size):
                total = checked_add(total, checked_mul(lengths[i], m[size * i + a]))
            if total > word_cap:
                raise Error(
                    "fixed-point count: an image sigma^n(a) is longer than the word cap; inconclusive, not a count"
                )
            longer.append(total)
        lengths = longer^
    return lengths^


struct LiteralFixedTilings(Copyable, Movable):
    """The reproduced pointed windows of radius `radius` at the power `n`
    (Lemma L of the module docstring), sorted by the index `k` of the tile of
    `sigma^n(u_0)` that holds the origin.

    `windows` is the number of legal words of length `2 radius + 1`.
    `interior[j]`: reproduced windows with middle letter `j` and
    `0 < k <` last. `left_vertex`, `left_seams`: those with `k = 0`, and the
    keys `d * u_{-1} + u_0` of their seams, increasing. `right_vertex`,
    `right_seams`: the closed-tile candidates with `k =` last, keys
    `d * u_0 + u_1`. The two seam lists are equal (checked at construction
    time by `literal_fixed_tilings`): each vertex-type tiling is seen from
    both of its tiles."""

    var power: Int
    var radius: Int
    var windows: Int
    var interior: List[Int]
    var left_vertex: Int
    var right_vertex: Int
    var left_seams: List[Int]
    var right_seams: List[Int]

    def __init__(
        out self,
        power: Int,
        radius: Int,
        windows: Int,
        interior: List[Int],
        left_seams: List[Int],
        right_seams: List[Int],
    ):
        self.power = power
        self.radius = radius
        self.windows = windows
        self.interior = interior.copy()
        self.left_vertex = len(left_seams)
        self.right_vertex = len(right_seams)
        self.left_seams = left_seams.copy()
        self.right_seams = right_seams.copy()

    def interior_total(self) -> Int:
        var n = 0
        for j in range(len(self.interior)):
            n += self.interior[j]
        return n

    def total(self) -> Int:
        """`|Fix(Phi^n)|`: the reproduced windows with `k` not last. A tiling
        whose origin is a vertex is counted once, from the tile on its right."""
        return self.interior_total() + self.left_vertex


def _keys_with_multiplicity(counts: List[Int]) -> List[Int]:
    """Every key `i` repeated `counts[i]` times, increasing. A seam reproduced
    by two windows would appear twice: nothing is merged."""
    var out = List[Int]()
    for key in range(len(counts)):
        for _ in range(counts[key]):
            out.append(key)
    return out^


def literal_fixed_tilings(
    sigma: List[List[Int]], n: Int, radius: Int = 1, word_cap: Int = LITERAL_WORD_CAP
) raises -> LiteralFixedTilings:
    """The `Phi^n`-fixed tilings of the primitive `sigma`, enumerated as
    reproduced pointed windows of the given radius: for every legal word
    `w = u_{-r} ... u_r` and every index `k` of `sigma^n(u_0)`, the word
    `sigma^n(u_{-r}) ... sigma^n(u_r)` is built and its `2r + 1` letters
    centred at the `k`-th letter of `sigma^n(u_0)` are compared with `w`.

    Raises on input outside the gate of `primitive_incidence`, on `n < 1`, on
    a radius outside `1..MAX_RADIUS`, when an image is longer than
    `word_cap`, and when the left and right seam lists differ."""
    _require_power(n)
    if radius < 1 or radius > MAX_RADIUS:
        raise Error("fixed-point count: the window radius must lie in 1.." + String(MAX_RADIUS))
    var m = primitive_incidence(sigma)
    var size = len(sigma)
    var lengths = image_lengths(m, size, n, word_cap)
    var s = Substitution(sigma.copy(), size)
    var images = List[List[Int]]()
    for a in range(size):
        var letter: List[Int] = [a]
        var image = s.apply_n(letter, n)
        if len(image) != lengths[a]:
            raise Error("fixed-point count: an image does not have the length its incidence matrix gives")
        if len(image) == 1 and image[0] == a:
            raise Error("fixed-point count: a letter is its own n-th image, impossible for a primitive substitution")
        images.append(image^)

    var windows = factor_set(s, 2 * radius + 1)
    var interior = List[Int](length=size, fill=0)
    var left = List[Int](length=size * size, fill=0)
    var right = List[Int](length=size * size, fill=0)
    for w in range(len(windows)):
        ref word = windows[w]
        var middle = word[radius]
        # sigma^n of the window, and where the image of its middle letter starts.
        var patch = List[Int]()
        var start = 0
        for i in range(len(word)):
            if i == radius:
                start = len(patch)
            ref image = images[word[i]]
            for t in range(len(image)):
                patch.append(image[t])
        var last = lengths[middle] - 1
        for k in range(last + 1):
            var centre = start + k
            if patch[centre] != middle:
                continue
            # Each image is nonempty, so the 2 radius + 1 letters lie in the patch.
            if centre - radius < 0 or centre + radius >= len(patch):
                raise Error("fixed-point count: a window left its patch")
            var reproduced = True
            for i in range(len(word)):
                if patch[centre - radius + i] != word[i]:
                    reproduced = False
                    break
            if not reproduced:
                continue
            if k == last:
                right[size * middle + word[radius + 1]] += 1
            elif k == 0:
                left[size * word[radius - 1] + middle] += 1
            else:
                interior[middle] += 1
    if left != right:
        raise Error("fixed-point count: a vertex-type fixed tiling was not seen from both of its tiles")
    return LiteralFixedTilings(
        n, radius, len(windows), interior, _keys_with_multiplicity(left), _keys_with_multiplicity(right)
    )
