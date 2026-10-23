"""Regime fits of class-A label datasets across gaps (experiment step (a)).

`docs/class-a-gap-uniformity-stopgo-2026-10-23.md` conjectures that, for each
sign `eps`, the complete swap-seed graph of `(n+d, n, n+eps)` with
`n = d l + r` has a label set that is a union of typed k-intervals whose
endpoints are affine in `(n, l, d, r)` on finitely many regimes:

  * `low j`:  `r = j`         (fixed `j >= 0`),
  * `high j`: `r = d - j`     (fixed `j >= 1`),
  * `middle`: `j0 <= r <= d - j1`.

An endpoint `k = alpha n + a l + b d + g r + c` is linear in the unknown
coefficients, and `n = d l + r` is the bilinear term a fit in `(l, d, r)`
alone would miss. `fit_regime` takes every dataset member of a regime with
`d >= d_min` and `l >= l_min`. It requires one row structure (the ordered
typed slices) for all of them. Each endpoint is solved exactly over Q
(`finite_linear_algebra.qlinalg.rref` on the augmented system of every
member) and must be consistent with integer coefficients. Otherwise the fit
refuses and names the first obstruction. A fit is a finite observation over
the dataset, not a proof for larger `l` or `d`.
"""
from finite_exact.rat_q import Q
from finite_linear_algebra.qlinalg import rref
from finite_linear_algebra.scalar import q_is_zero
from psc.exact import q_string
from psc.class_a_gap_dataset import MemberRecord, load_dataset

comptime LOW = 0
comptime HIGH = 1
comptime MIDDLE = 2


struct Sample(Copyable, Movable):
    var d: Int
    var n: Int
    var rows: List[List[Int]]

    def __init__(out self, d: Int, n: Int, rows: List[List[Int]]):
        self.d = d
        self.n = n
        self.rows = rows.copy()

    def l(self) -> Int:
        return self.n // self.d

    def r(self) -> Int:
        return self.n % self.d


def in_regime(kind: Int, j: Int, j1: Int, d: Int, r: Int) -> Bool:
    if kind == LOW:
        return r == j
    if kind == HIGH:
        return r == d - j
    return j <= r and r <= d - j1


def regime_name(kind: Int, j: Int, j1: Int) -> String:
    if kind == LOW:
        return "low r=" + String(j)
    if kind == HIGH:
        return "high r=d-" + String(j)
    return "middle " + String(j) + "<=r<=d-" + String(j1)


def basis(kind: Int, s: Sample) -> List[Int]:
    """`[n, l, d, r, 1]` on the middle regime; `r` is fixed (low) or `d - j` (high) otherwise."""
    if kind == MIDDLE:
        return [s.n, s.l(), s.d, s.r(), 1]
    return [s.n, s.l(), s.d, 1]


struct RegimeFit(Copyable, Movable):
    """`ok`; on failure `reason`; on success `rows` = `[top, bottom, s, y]`
    followed by the coefficients of `k_lo`, then of `k_hi`, over the basis."""
    var ok: Bool
    var reason: String
    var samples: Int
    var gaps: Int
    var rank: Int
    var rows: List[List[Int]]

    def __init__(out self):
        self.ok = False
        self.reason = String()
        self.samples = 0
        self.gaps = 0
        self.rank = 0
        self.rows = List[List[Int]]()


def _solve(kind: Int, samples: List[Sample], row: Int, col: Int, mut rank: Int) raises -> List[Int]:
    """Integer coefficients of endpoint `col` of row `row`, or raise naming the obstruction."""
    var m = List[List[Q]]()
    for s in samples:
        var e = List[Q]()
        for x in basis(kind, s):
            e.append(Q.from_int(Int64(x)))
        e.append(Q.from_int(Int64(s.rows[row][col])))
        m.append(e^)
    var width = len(m[0]) - 1
    var reduced = rref(m)
    var r = reduced[0].copy()
    var pivots = reduced[1].copy()
    for p in pivots:
        if p == width:
            raise Error("endpoint is not affine on the regime")
    rank = len(pivots)
    var coeff = List[Int](length=width, fill=0)
    for i in range(len(pivots)):
        var text = q_string(r[i][width])
        if "/" in text:
            raise Error("endpoint has a non-integral coefficient " + text)
        coeff[pivots[i]] = Int(text)
    return coeff^


def fit_regime(eps: Int, kind: Int, j: Int, j1: Int, d_min: Int, d_max: Int, l_min: Int,
               dir: String) raises -> RegimeFit:
    var out = RegimeFit()
    var samples = List[Sample]()
    var gaps = 0
    for d in range(d_min, d_max + 1):
        var path = dir + "/labels-d" + String(d) + "-eps" + String(eps) + ".txt"
        var counted = False
        for rec in load_dataset(path, d, eps):
            if rec.n // d >= l_min and in_regime(kind, j, j1, d, rec.n % d):
                samples.append(Sample(d, rec.n, rec.rows))
                if not counted:
                    gaps += 1
                    counted = True
    out.samples = len(samples)
    out.gaps = gaps
    if len(samples) == 0:
        out.reason = "no members in the regime"
        return out^
    # One row structure: the same ordered typed slices for every member.
    var shape = samples[0].rows.copy()
    for s in samples:
        if len(s.rows) != len(shape):
            out.reason = "row count " + String(len(s.rows)) + " at d=" + String(s.d) + " n=" + String(s.n) + " differs from " + String(len(shape))
            return out^
        for i in range(len(shape)):
            for t in range(4):
                if s.rows[i][t] != shape[i][t]:
                    out.reason = "row " + String(i) + " slice differs at d=" + String(s.d) + " n=" + String(s.n)
                    return out^
    for i in range(len(shape)):
        var row = List[Int]()
        for t in range(4):
            row.append(shape[i][t])
        for col in [4, 5]:
            var rank = 0
            try:
                var c = _solve(kind, samples, i, col, rank)
                row.extend(c^)
                out.rank = max(out.rank, rank)
            except e:
                out.reason = "row " + String(i) + " " + ("k_lo" if col == 4 else "k_hi") + ": " + String(e)
                return out^
        out.rows.append(row^)
    out.ok = True
    return out^
