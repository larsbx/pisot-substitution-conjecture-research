"""Exact census of the A1' normal form: does the hard tail scale?

Proposition D of docs/p1a-a1-prime-2026-10-05.md. On the catch-up-free
`|det M| = 2` class the surviving aligned template of Theorem C forces the odd
letter set to be exactly the bad edge `{x, c}`, so with `y` the third letter

    sigma(x) = x y^p s_x,   sigma(c) = c y^q s_c,   sigma(y) = t y^r s_y

with `p, q, r >= 0` and `s_x, s_c, t, s_y` in `{x, c}`. The parameters are
unbounded, so the family reaches substitutions past every censused specimen
domain, and this census asks A1' of each member: is the bad edge `{x, c}`
eventually coincident?

The decision is `psc.coincidence_formula.coincidence_level`, the canonical
exact procedure, finite by the Pisot property -- so a negative would be a
verdict and not an exhausted budget. The screen is `psc.pisot.is_pip`, exact.
Nothing is reimplemented here: the driver only enumerates, screens, and folds.

What the census reports, and why those columns: the level histogram, the
deepest level, and the members at level at least `DEEP_LEVEL`. The point of the
sweep is whether that **tail moves** as the parameter bound grows. If the deep
members are the same few at every bound while only the shallow counts grow,
then the hard cases do not scale with the parameters, which is what a uniform
level bound would have to exploit. A growing tail would say the opposite.

Residual-vs-merged is reported too (`first_letter_merge_level`): under this
normal form `h` fixes both `x` and `c`, so no member may be merged, and a
merged one would contradict Proposition A. The driver raises if it sees one.

Usage: `mojo run -I . a1_normal_form_census.mojo [bound]` (default 5), or
`pixi run a1-normal-form-census`. A bound beyond `MAX_BOUND` is refused rather
than silently truncated.
"""

from std.sys import argv
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.coincidence_formula import coincidence_level, first_letter_merge_level
from psc.histogram import Histogram
from psc.pisot import CubicScreen

comptime MAX_BOUND = 14
comptime DEEP_LEVEL = 4
comptime LEVEL_CAP = 64

# Letters: 0 = x (the bad-edge letter), 1 = c (the hub), 2 = y (the only even one).
comptime X = 0
comptime C = 1
comptime Y = 2


def normal_form(p: Int, q: Int, r: Int, sx: Int, sc: Int, t: Int, sy: Int) raises -> List[List[Int]]:
    """`sigma(x) = x y^p s_x`, `sigma(c) = c y^q s_c`, `sigma(y) = t y^r s_y`."""
    var sigma = List[List[Int]]()
    var img_x = List[Int]([X])
    for _ in range(p):
        img_x.append(Y)
    img_x.append(sx)
    var img_c = List[Int]([C])
    for _ in range(q):
        img_c.append(Y)
    img_c.append(sc)
    var img_y = List[Int]([t])
    for _ in range(r):
        img_y.append(Y)
    img_y.append(sy)
    sigma.append(img_x^)
    sigma.append(img_c^)
    sigma.append(img_y^)
    return sigma^


struct DeepMember(Copyable, Movable, Writable):
    var level: Int
    var p: Int
    var q: Int
    var r: Int
    var sx: Int
    var sc: Int
    var t: Int
    var sy: Int

    def __init__(out self, level: Int, p: Int, q: Int, r: Int, sx: Int, sc: Int, t: Int, sy: Int):
        self.level = level
        self.p = p
        self.q = q
        self.r = r
        self.sx = sx
        self.sc = sc
        self.t = t
        self.sy = sy

    def write_to[W: Writer](self, mut w: W):
        var name = List[String](["x", "c", "y"])
        w.write("level ", self.level, "  sigma(x)=x")
        for _ in range(self.p):
            w.write("y")
        w.write(name[self.sx], " sigma(c)=c")
        for _ in range(self.q):
            w.write("y")
        w.write(name[self.sc], " sigma(y)=", name[self.t])
        for _ in range(self.r):
            w.write("y")
        w.write(name[self.sy], "  (p,q,r)=(", self.p, ",", self.q, ",", self.r, ")")


struct NormalFormCensus(Copyable, Movable):
    var members: Int
    var levels: Histogram
    var deep: List[DeepMember]
    var max_level: Int

    def __init__(out self) raises:
        self.members = 0
        self.levels = Histogram(LEVEL_CAP)
        self.deep = List[DeepMember]()
        self.max_level = -1


def census(bound: Int) raises -> NormalFormCensus:
    if bound < 0 or bound > MAX_BOUND:
        raise Error("the A1' normal-form bound must lie in 0..", String(MAX_BOUND))
    var screen = CubicScreen()
    var out = NormalFormCensus()
    for p in range(bound + 1):
        for q in range(bound + 1):
            for r in range(bound + 1):
                for sx in range(2):
                    for sc in range(2):
                        for t in range(2):
                            for sy in range(2):
                                var sigma = normal_form(p, q, r, sx, sc, t, sy)
                                var m = Mat3(substitution_incidence(sigma))
                                if not screen.is_pip(m):
                                    continue
                                if abs(m.det()) != 2:
                                    continue
                                out.members += 1
                                # Proposition A: h fixes x and c here, so the
                                # pair can never be merged.
                                if first_letter_merge_level(sigma, X, C) >= 0:
                                    raise Error("a normal-form member merged at the endpoint, against Proposition A")
                                var lev = coincidence_level(sigma, X, C)
                                if lev < 0:
                                    raise Error("A1' REFUTED: the bad edge is not eventually coincident")
                                out.levels.record(lev)
                                if lev > out.max_level:
                                    out.max_level = lev
                                if lev >= DEEP_LEVEL:
                                    out.deep.append(DeepMember(lev, p, q, r, sx, sc, t, sy))
    return out^


def main() raises:
    var args = argv()
    var bound = Int(String(args[1])) if len(args) > 1 else 5
    var r = census(bound)
    print("A1' normal-form census, parameter bound p,q,r <=", bound)
    print("PIP members with |det M| = 2:", r.members)
    print("members merged at the endpoint: 0 (Proposition A forbids any; one would have raised)")
    print("A1' refutations:", 0, " (a negative would have raised: the decision is exact and finite)")
    print("coincidence level histogram:")
    for k in range(LEVEL_CAP):
        if r.levels.count(k) != 0:
            print("    level", k, ":", r.levels.count(k), "members")
    print("deepest level:", r.max_level)
    print("members at level >=", DEEP_LEVEL, ":", len(r.deep))
    for i in range(len(r.deep)):
        print("   ", r.deep[i])
    print()
    print("The tail is the point: run this at two bounds and compare the")
    print("level-", DEEP_LEVEL, "-and-up rows. Identical rows mean the hard cases do not")
    print("scale with the parameters; a growing tail would mean they do.")
