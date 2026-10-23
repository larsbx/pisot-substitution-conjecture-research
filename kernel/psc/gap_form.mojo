"""Gap forms in Z[l, d, r] and residue regimes of the class-A gap family (#139, gaps d >= 5).

A *gap form* `c1 + cl l + cd d + cld l d + cr r` is the shape of every integer
quantity of the class-A ray certificate once the gap `d` and the residue `r`
of `n = d l + r` are kept symbolic: row endpoints (`l`-affine), run lengths
`d l + r + {d, 0, eps}`, the child-index base `d (k_lo + s) + r s + eps y`
and prefix-count ranges. A *regime* pins `r`: `r = j` (low), `r = d - j`
(high) or `j <= r <= d - j1` (middle), for every integer `l >= l0`, `d >= d0`.

Two lemmas decide forms on a regime exactly (docs/class-a-gap-uniform-certificate-design-2026-10-23.md):

  * Lemma 1. `g = c1 + cl l + cd d + cld l d >= 0` for all integers `l >= l0`,
    `d >= d0` iff `g(l0, d0) >= 0`, `cl + cld d0 >= 0`, `cd + cld l0 >= 0`,
    `cld >= 0`. A form with `cr != 0` is affine in `r`, so it is decided at
    the regime's `r` endpoints (`j`; `d - j`; both `j0` and `d - j1`).
  * Lemma 2. `N / d` for `N` without a pure `l` term equals
    `cld l + cd + v(r)/d`, `v(r) = cr r + c1`; the rounding of `v(r)/d` is
    one constant on the whole regime in the listed cases and the division
    *refuses* otherwise. The quotient is then `l`-affine.

Everything here is exact integer arithmetic; an undecidable comparison or
rounding raises rather than guessing.
"""

comptime KIND_LOW = 0
comptime KIND_HIGH = 1
comptime KIND_MIDDLE = 2


struct GapForm(ImplicitlyCopyable, Copyable, Movable, Equatable, Writable):
    var c1: Int
    var cl: Int
    var cd: Int
    var cld: Int
    var cr: Int

    def __init__(out self, c1: Int, cl: Int, cd: Int, cld: Int, cr: Int):
        self.c1 = c1
        self.cl = cl
        self.cd = cd
        self.cld = cld
        self.cr = cr

    def add(self, o: GapForm) -> GapForm:
        return GapForm(self.c1 + o.c1, self.cl + o.cl, self.cd + o.cd, self.cld + o.cld, self.cr + o.cr)

    def sub(self, o: GapForm) -> GapForm:
        return GapForm(self.c1 - o.c1, self.cl - o.cl, self.cd - o.cd, self.cld - o.cld, self.cr - o.cr)

    def scale(self, c: Int) -> GapForm:
        return GapForm(c * self.c1, c * self.cl, c * self.cd, c * self.cld, c * self.cr)

    def at(self, l: Int, d: Int, r: Int) -> Int:
        return self.c1 + self.cl * l + self.cd * d + self.cld * l * d + self.cr * r

    def is_zero(self) -> Bool:
        return self.c1 == 0 and self.cl == 0 and self.cd == 0 and self.cld == 0 and self.cr == 0

    def is_l_affine(self) -> Bool:
        return self.cd == 0 and self.cld == 0 and self.cr == 0

    def __eq__(self, o: GapForm) -> Bool:
        return (self.c1 == o.c1 and self.cl == o.cl and self.cd == o.cd
                and self.cld == o.cld and self.cr == o.cr)

    def __ne__(self, o: GapForm) -> Bool:
        return not (self == o)

    def write_to(self, mut w: Some[Writer]):
        w.write("(", self.c1, " + ", self.cl, " l + ", self.cd, " d + ", self.cld, " l d + ", self.cr, " r)")


def gap_const(c: Int) -> GapForm:
    return GapForm(c, 0, 0, 0, 0)


def gap_lin(a: Int, b: Int) -> GapForm:
    """`a l + b`."""
    return GapForm(b, a, 0, 0, 0)


def quadrant_nonneg(g: GapForm, l0: Int, d0: Int) raises -> Bool:
    """Lemma 1 for an `r`-free form on `l >= l0`, `d >= d0`."""
    if g.cr != 0:
        raise Error("quadrant criterion needs an r-free form")
    return (g.at(l0, d0, 0) >= 0 and g.cl + g.cld * d0 >= 0
            and g.cd + g.cld * l0 >= 0 and g.cld >= 0)


def _round_low(v0: Int, d0: Int, ceil: Bool) raises -> Int:
    """`ceil(v0/d)` (or floor) for a constant `v0`, provided it is one value for every `d >= d0`."""
    if ceil:
        if -d0 < v0 and v0 <= 0:
            return 0
        if 0 < v0 and v0 <= d0:
            return 1
    else:
        if 0 <= v0 and v0 < d0:
            return 0
        if -d0 <= v0 and v0 < 0:
            return -1
    raise Error("UNDECIDED division: rounding of " + String(v0) + "/d varies for d >= " + String(d0))


struct Regime(ImplicitlyCopyable, Copyable, Movable):
    """`eps`, the residue regime (`kind`, `j`, `j1`) and the parameter floors `l0 <= l`, `d0 <= d`."""
    var eps: Int
    var kind: Int
    var j: Int
    var j1: Int
    var l0: Int
    var d0: Int

    def __init__(out self, eps: Int, kind: Int, j: Int, j1: Int, l0: Int, d0: Int):
        self.eps = eps
        self.kind = kind
        self.j = j
        self.j1 = j1
        self.l0 = l0
        self.d0 = d0

    def check(self) raises:
        if self.eps != 1 and self.eps != -1:
            raise Error("class-A line requires eps = +-1")
        if self.l0 < 1 or self.d0 < 1 or self.l0 > 64 or self.d0 > 64:
            raise Error("regime floors must satisfy 1 <= l0, d0 <= 64")
        if self.kind == KIND_LOW:
            if self.j < 0 or self.j >= self.d0 or self.j1 != 0:
                raise Error("low regime needs 0 <= j < d0 and j1 = 0")
        elif self.kind == KIND_HIGH:
            if self.j < 1 or self.j > self.d0 or self.j1 != 0:
                raise Error("high regime needs 1 <= j <= d0 and j1 = 0")
        elif self.kind == KIND_MIDDLE:
            if self.j < 0 or self.j1 < 1 or self.d0 < self.j + self.j1:
                raise Error("middle regime needs j >= 0, j1 >= 1 and d0 >= j + j1")
        else:
            raise Error("regime kind must be 0 (low), 1 (high) or 2 (middle)")

    def name(self) -> String:
        if self.kind == KIND_LOW:
            return "low:r=" + String(self.j)
        if self.kind == KIND_HIGH:
            return "high:r=d-" + String(self.j)
        return "middle:" + String(self.j) + "<=r<=d-" + String(self.j1)

    def contains(self, l: Int, d: Int, r: Int) -> Bool:
        """Membership of the integer point `(l, d, r)`; for tests and brute force."""
        if l < self.l0 or d < self.d0 or r < 0 or r >= d:
            return False
        if self.kind == KIND_LOW:
            return r == self.j
        if self.kind == KIND_HIGH:
            return r == d - self.j
        return self.j <= r and r <= d - self.j1

    def r_endpoints(self) -> List[GapForm]:
        """`r` as `r`-free forms: `j`; `d - j`; both `j0` and `d - j1`."""
        var out = List[GapForm]()
        if self.kind == KIND_LOW:
            out.append(gap_const(self.j))
        elif self.kind == KIND_HIGH:
            out.append(GapForm(-self.j, 0, 1, 0, 0))
        else:
            out.append(gap_const(self.j))
            out.append(GapForm(-self.j1, 0, 1, 0, 0))
        return out^

    def substitutions(self, f: GapForm) -> List[GapForm]:
        """`f` with `r` replaced by each endpoint form (the result is `r`-free)."""
        var out = List[GapForm]()
        for e in self.r_endpoints():
            out.append(GapForm(f.c1 + f.cr * e.c1, f.cl, f.cd + f.cr * e.cd, f.cld, 0))
        return out^

    def nonneg(self, f: GapForm) raises -> Bool:
        """`f >= 0` at every integer point of the regime (Lemma 1 after the `r` reduction)."""
        for g in self.substitutions(f):
            if not quadrant_nonneg(g, self.l0, self.d0):
                return False
        return True

    def le(self, u: GapForm, v: GapForm) raises -> Int:
        """`1` if `u <= v` on the whole regime, `0` if `u > v` on the whole regime, `-1` otherwise."""
        if self.nonneg(v.sub(u)):
            return 1
        if self.nonneg(u.sub(v).sub(gap_const(1))):
            return 0
        return -1

    def _divide(self, f: GapForm, ceil: Bool) raises -> GapForm:
        if f.cl != 0:
            raise Error("gap form has a pure l term: not divisible by the gap")
        var quotient_const = f.cd
        var kappa = 0
        if self.kind == KIND_LOW:
            kappa = _round_low(f.cr * self.j + f.c1, self.d0, ceil)
        elif self.kind == KIND_HIGH:
            # r = d - j: v = cr d + (c1 - cr j), so v/d = cr + (c1 - cr j)/d.
            quotient_const += f.cr
            kappa = _round_low(f.c1 - f.cr * self.j, self.d0, ceil)
        else:
            var j0 = self.j
            var j1 = self.j1
            var c1 = f.c1
            if f.cr == 0:
                kappa = _round_low(c1, self.d0, ceil)
            elif f.cr == 1:
                # v = r + c1 ranges over [j0 + c1, d - j1 + c1].
                if ceil and 1 - j0 <= c1 and c1 <= j1:
                    kappa = 1
                elif (not ceil) and -j0 <= c1 and c1 <= j1 - 1:
                    kappa = 0
                else:
                    raise Error("UNDECIDED division: rounding of (r + " + String(c1) + ")/d varies on the middle regime")
            elif f.cr == -1:
                # v = c1 - r ranges over [c1 - d + j1, c1 - j0].
                if ceil and 1 - j1 <= c1 and c1 <= j0:
                    kappa = 0
                elif (not ceil) and -j1 <= c1 and c1 <= j0 - 1:
                    kappa = -1
                else:
                    raise Error("UNDECIDED division: rounding of (" + String(c1) + " - r)/d varies on the middle regime")
            else:
                raise Error("UNDECIDED division: |r coefficient| >= 2 spans several multiples of d")
        return GapForm(quotient_const + kappa, f.cld, 0, 0, 0)

    def div_ceil(self, f: GapForm) raises -> GapForm:
        """Lemma 2: `ceil(f / d)` as an `l`-affine form, or refuse."""
        return self._divide(f, True)

    def div_floor(self, f: GapForm) raises -> GapForm:
        """Lemma 2: `floor(f / d)` as an `l`-affine form, or refuse."""
        return self._divide(f, False)

    def max(self, u: GapForm, v: GapForm) raises -> GapForm:
        if self.le(u, v) == 1:
            return v
        if self.le(v, u) == 1:
            return u
        raise Error("UNDECIDED maximum on the regime")

    def min(self, u: GapForm, v: GapForm) raises -> GapForm:
        if self.le(u, v) == 1:
            return u
        if self.le(v, u) == 1:
            return v
        raise Error("UNDECIDED minimum on the regime")

    def run(self, letter: Int) raises -> GapForm:
        """Length of the `y` run of `sigma(letter)`: `d l + r + d`, `d l + r`, `d l + r + eps`."""
        if letter == 0:
            return GapForm(0, 0, 1, 1, 1)
        if letter == 1:
            return GapForm(0, 0, 0, 1, 1)
        if letter == 2:
            return GapForm(self.eps, 0, 0, 1, 1)
        raise Error("tile letter outside 0..2")
