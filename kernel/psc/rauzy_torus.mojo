"""The Rauzy fractal of a unimodular alphabet-3 Pisot substitution, on its 2-torus.

Let `M` be the incidence matrix, `beta` its Perron root and `f = v / |v|_1` the
letter-frequency vector (`M v = beta v`). Write `H = {x : x_0 + x_1 + x_2 = 0}`
and `H_Z = H ∩ Z^3`, a rank-2 lattice with basis `e_0 - e_2, e_1 - e_2`. The
projection of `R^3` onto `H` along the expanding line `R v` is

    x  ↦  x - |x|_1 f,

so the `n`-th vertex `p_n` of the stepped line of a fixed point goes to its
discrepancy vector `D_n = p_n - n f`, read in the coordinates `(D_n0, D_n1)`.
The closure of `{D_n}` is the Rauzy fractal, linearly equivalent to the usual
picture in the contracting plane; the subtile `R(i)` collects the `D_n` whose
next letter is `i`. Modulo `H_Z = Z^2` this is the orbit `n ↦ -n (f_0, f_1)`
of the Kronecker rotation on `T^2 = H / H_Z`: the straight-line flow along
`v` in `T^3`, cut by the transversal `T^2`.

Every quantity is exact. `f_i` is held as the certified integer
`F_i = floor(S f_i)` with `S = 2^FREQUENCY_SCALE_BITS`, decided by Sturm--Tarski
sign queries in `Q(beta)` (`psc.perron_field3`); then

    S D_ni ∈ [S p_ni - n F_i - n,  S p_ni - n F_i],

an integer enclosure of width `n`. A grid cell is assigned only when the whole
enclosure lies in it; otherwise the point is counted as undecided and left out.

The lift profile counts, for each cell of a `G x G` grid on `T^2`, the distinct
integer translates of it that the sampled fractal meets. A periodic tiling by
`Z^2` (the Pisot conjecture for `sigma`) puts every interior cell at one lift;
cells on a tile boundary may show two or more. The profile is a finite sample
at one resolution: it never certifies a covering degree, in either direction.
"""

from finite_linear_algebra.mat3 import Mat3
from psc.bpa import apply_substitution, substitution_incidence
from psc.histogram import Histogram
from psc.perron_field3 import (
    CubicElt,
    PerronField3,
    build_perron_field3,
    cubic_add_checked,
    cubic_scale_checked,
    cubic_sub_checked,
    perron_tile_lengths_in,
    sign_at_perron,
)
from psc.words import ALPHABET

comptime FREQUENCY_SCALE_BITS = 40
comptime FREQUENCY_SCALE = 1 << FREQUENCY_SCALE_BITS
# `n <= 2^16` keeps the enclosure width `n / S <= 2^-24` and `S p_n` inside `Int`.
comptime MAX_POINTS = 1 << 16
# Lifts are encoded in a `LIFT_SPAN x LIFT_SPAN` window centred on the origin,
# so one torus cell meets at most `LIFT_SPAN * LIFT_SPAN` distinct lifts.
comptime LIFT_SPAN = 256
comptime MAX_LIFTS_PER_CELL = LIFT_SPAN * LIFT_SPAN
comptime MAX_FIXED_POINT_ROUNDS = 64


struct FrequencyFrame(ImplicitlyCopyable, Copyable, Movable):
    """`F_i = floor(S f_i)` for the three letter frequencies, certified."""

    var scale: Int
    var f0: Int
    var f1: Int
    var f2: Int

    def __init__(out self, scale: Int, f0: Int, f1: Int, f2: Int):
        self.scale = scale
        self.f0 = f0
        self.f1 = f1
        self.f2 = f2


struct RauzyPoint(ImplicitlyCopyable, Copyable, Movable):
    """`S D_ni ∈ [hi_i - n, hi_i]`; `letter` is the next letter, the subtile."""

    var n: Int
    var letter: Int
    var hi0: Int
    var hi1: Int

    def __init__(out self, n: Int, letter: Int, hi0: Int, hi1: Int):
        self.n = n
        self.letter = letter
        self.hi0 = hi0
        self.hi1 = hi1


struct LiftProfile(Copyable, Movable):
    """Per torus cell, the number of distinct lifts the sample meets."""

    var grid: Int
    var lifts: List[Int]
    var undecided: Int

    def __init__(out self, grid: Int, var lifts: List[Int], undecided: Int):
        self.grid = grid
        self.lifts = lifts^
        self.undecided = undecided

    def occupied(self) -> Int:
        var n = 0
        for c in self.lifts:
            if c > 0:
                n += 1
        return n

    def histogram(self) raises -> Histogram:
        """Occupied cells by lift count; sized for every count the encoded
        window admits, so a valid profile never raises here."""
        var h = Histogram(MAX_LIFTS_PER_CELL + 1)
        for c in self.lifts:
            if c > 0:
                h.record(c)
        return h^


def transpose3(m: Mat3) -> Mat3:
    var e = List[Int]()
    for i in range(3):
        for j in range(3):
            e.append(m.at(j, i))
    return Mat3(e)


def _sign_of_offset(field: PerronField3, scaled: CubicElt, denominator: CubicElt, f: Int) raises -> Int:
    """Sign of `scale * numerator - f * denominator` at the Perron embedding.
    Zero would make the frequency a dyadic rational, impossible for an
    irrational one; it raises rather than guessing a side."""
    var sign = sign_at_perron(field, cubic_sub_checked(scaled, cubic_scale_checked(denominator, f)))
    if sign == 0:
        raise Error("a letter frequency is a dyadic rational: impossible in an irreducible cubic field")
    return sign


def _scaled_floor(
    field: PerronField3, numerator: CubicElt, denominator: CubicElt, scale: Int, guess: Int
) raises -> Int:
    """`floor(scale * numerator / denominator)` for `0 < numerator < denominator`
    at the Perron embedding. `guess` is only a hint: it is accepted after the
    two sign queries that certify it, and otherwise the floor is found by
    bisection over `[0, scale)` on the same exact queries."""
    var scaled = cubic_scale_checked(numerator, scale)
    if guess >= 0 and guess < scale:
        if _sign_of_offset(field, scaled, denominator, guess) > 0 and _sign_of_offset(
            field, scaled, denominator, guess + 1
        ) < 0:
            return guess
    var lo = 0
    var hi = scale
    while hi - lo > 1:
        var mid = lo + (hi - lo) // 2
        if _sign_of_offset(field, scaled, denominator, mid) > 0:
            lo = mid
        else:
            hi = mid
    return lo


def _scaled_ratio(c: Int, total: Int, bits: Int) -> Int:
    """`floor(2^bits c / total)` for `0 <= c <= total < 2^62`, by long division."""
    var q = c // total
    var r = c - q * total
    for _ in range(bits):
        r *= 2
        q *= 2
        if r >= total:
            r -= total
            q += 1
    return q


def _frequency_guesses(m: Mat3) -> List[Int]:
    """Uncertified hints for `floor(S f_i)`: the letter proportions of `M^k e_0`
    once its total passes `2^56`. They converge to `f` geometrically for a
    Pisot matrix, but nothing here relies on that: `_scaled_floor` checks."""
    var c: List[Int] = [1, 0, 0]
    while c[0] + c[1] + c[2] < (1 << 56):
        c = m.apply(c)
    var total = c[0] + c[1] + c[2]
    return [
        _scaled_ratio(c[0], total, FREQUENCY_SCALE_BITS),
        _scaled_ratio(c[1], total, FREQUENCY_SCALE_BITS),
        _scaled_ratio(c[2], total, FREQUENCY_SCALE_BITS),
    ]


def frequency_frame(m: Mat3) raises -> FrequencyFrame:
    """Certified scaled letter frequencies of a unimodular PIP incidence matrix.

    A non-unimodular matrix is refused: its representation space carries a
    `p`-adic factor, the quotient is a solenoid rather than `T^2`, and no
    picture drawn here would be the right one."""
    var det = m.det()
    if det != 1 and det != -1:
        raise Error("the torus picture needs a unimodular incidence matrix (|det M| = 1)")
    var field = build_perron_field3(m)
    # The left Perron eigenvector of M^T is the right one of M: M v = beta v.
    var v = perron_tile_lengths_in(field, transpose3(m))
    var total = cubic_add_checked(cubic_add_checked(v.l0, v.l1), v.l2)
    var guesses = _frequency_guesses(m)
    var floors = List[Int]()
    var sum = 0
    for i in range(ALPHABET):
        var f = _scaled_floor(field, v.at(i), total, FREQUENCY_SCALE, guesses[i])
        floors.append(f)
        sum += f
    # sum f_i = 1 and no S f_i is an integer, so the floors lose strictly
    # between 0 and 3 units.
    if sum < FREQUENCY_SCALE - 2 or sum > FREQUENCY_SCALE - 1:
        raise Error("scaled frequency floors do not sum to S - 1 or S - 2")
    return FrequencyFrame(FREQUENCY_SCALE, floors[0], floors[1], floors[2])


def _first_letter_power(sigma: List[List[Int]]) raises -> List[Int]:
    """`[a, k]` with `sigma^k(a)` beginning with `a`, least `k`, then least `a`."""
    for k in range(1, ALPHABET + 1):
        for a in range(ALPHABET):
            var b = a
            for _ in range(k):
                b = sigma[b][0]
            if b == a:
                return [a, k]
    raise Error("the first-letter map has no periodic point of period <= 3")


def fixed_point_prefix(sigma: List[List[Int]], length: Int) raises -> List[Int]:
    """The length-`length` prefix of the one-sided fixed point of `sigma^k`
    starting with `a`, for the `[a, k]` of `_first_letter_power`."""
    if length < 1 or length > MAX_POINTS:
        raise Error("fixed-point prefix length lies outside 1..MAX_POINTS")
    var ak = _first_letter_power(sigma)
    var w: List[Int] = [ak[0]]
    for _ in range(MAX_FIXED_POINT_ROUNDS):
        if len(w) >= length:
            break
        var next = w.copy()
        for _ in range(ak[1]):
            next = apply_substitution(sigma, next)
            if len(next) > length:
                next.resize(length, 0)
        if len(next) <= len(w):
            raise Error("the fixed-point prefix stopped growing")
        w = next^
    if len(w) < length:
        raise Error("fixed-point prefix round budget exhausted")
    w.resize(length, 0)
    return w^


def rauzy_points(sigma: List[List[Int]], frame: FrequencyFrame, count: Int) raises -> List[RauzyPoint]:
    """The enclosures of `D_0, ..., D_{count-1}` along the fixed point."""
    var word = fixed_point_prefix(sigma, count)
    var s = frame.scale
    var p0 = 0
    var p1 = 0
    var out = List[RauzyPoint](capacity=count)
    for n in range(count):
        out.append(
            RauzyPoint(n, word[n], s * p0 - n * frame.f0, s * p1 - n * frame.f1)
        )
        if word[n] == 0:
            p0 += 1
        elif word[n] == 1:
            p1 += 1
    return out^


def enclosure_cell(hi: Int, width: Int, cell_size: Int) -> List[Int]:
    """`[cell]` when `[hi - width, hi]` lies inside one cell of side `cell_size`
    (Int `//` floors), and `[]` when the enclosure straddles a grid line."""
    var top = hi // cell_size
    if (hi - width) // cell_size != top:
        return []
    return [top]


def _floor_mod(a: Int, b: Int) -> Int:
    return a - (a // b) * b


def lift_profile_of_cells(cells: List[List[Int]], grid: Int, undecided: Int = 0) raises -> LiftProfile:
    """Distinct-lift counts per torus cell, for cells `(cx, cy)` of the plane."""
    var lifts = List[Int](length=grid * grid, fill=0)
    var seen = Dict[Int, Bool]()
    var half = LIFT_SPAN // 2
    for c in cells:
        var lx = c[0] // grid
        var ly = c[1] // grid
        if lx < -half or lx >= half or ly < -half or ly >= half:
            raise Error("a lift lies outside the encoded window")
        var torus = _floor_mod(c[0], grid) * grid + _floor_mod(c[1], grid)
        var key = (torus * LIFT_SPAN + lx + half) * LIFT_SPAN + ly + half
        if key not in seen:
            seen[key] = True
            lifts[torus] += 1
    return LiftProfile(grid, lifts^, undecided)


def lift_profile(points: List[RauzyPoint], scale: Int, grid: Int) raises -> LiftProfile:
    """The lift profile of sampled fractal points on a `grid x grid` torus."""
    if grid < 1 or scale % grid != 0:
        raise Error("the grid must divide the frequency scale")
    var cell_size = scale // grid
    var cells = List[List[Int]]()
    var undecided = 0
    for p in points:
        var cx = enclosure_cell(p.hi0, p.n, cell_size)
        var cy = enclosure_cell(p.hi1, p.n, cell_size)
        if len(cx) == 0 or len(cy) == 0:
            undecided += 1
        else:
            cells.append([cx[0], cy[0]])
    return lift_profile_of_cells(cells, grid, undecided)


def sup_discrepancy_bound(points: List[RauzyPoint]) -> Int:
    """An integer `B` with `S |D_ni| <= B` for every sampled point and `i in
    {0, 1, 2}` (`D_n2 = -D_n0 - D_n1`)."""
    var bound = 0
    for p in points:
        var lo0 = p.hi0 - p.n
        var lo1 = p.hi1 - p.n
        for x in [p.hi0, lo0, p.hi1, lo1, -(lo0 + lo1), -(p.hi0 + p.hi1)]:
            var a = x if x >= 0 else -x
            if a > bound:
                bound = a
    return bound


def incidence_of(sigma: List[List[Int]]) -> Mat3:
    return Mat3(substitution_incidence(sigma))
