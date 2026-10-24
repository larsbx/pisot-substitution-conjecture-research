"""Exploratory profile of class B's top layer: is it residue-ray shaped?

docs/class-b-top-layer-stopgo-2026-10-23.md (lateral move 2). Theorem C
(docs/p1b-symbolic-cone-2026-10-08.md) leaves open, in class B
`sigma(x) = x y^p x, sigma(c) = c y^q x, sigma(y) = c y^r x`,

    plus  r = q + 1,  max(2q + 13, (5q + 10)/2) < p < 3q + 12,
    minus r = q - 1,  max(2q + 7,  (5q - 5)/2)  < p < 3q.

Write `p = 3q + 11 - d` (plus) or `p = 3q - 1 - d` (minus), `d >= 0`. Each fixed
`d` is a line in `q`, like class A's gap lines. For one line and every PIP
member with `q <= QMAX` outside Theorem C's region, this builds the complete
canonical swap-seed graph and records its vertex count, whether every vertex
has an offset-zero descendant, and the deepest first-hit depth. It then asks,
for each modulus `k = 1..6`, whether the counts on every residue class of `q`
mod `k` are affine in `q` on the last FIT points of that class.

This is a bounded exploratory probe, not a certificate. A capped graph raises.
A vertex without an offset-zero descendant raises as a candidate counterexample
to boundary hitting (it would also contradict nothing proved: the top layer is
open). "no affine fit" is a finite verdict on the probed window only.

Mode `barge DMAX QMAX` counts the PIP top-layer members with d <= DMAX, q <= QMAX
on both branches that have a Barge power/rotation witness up to power 3 (the
prior-art shortcut of `substitution_dynamics.barge_class`); no witness proves
nothing about the spectrum.

Mode `labels plus|minus D QMAX` is the step-1 stop condition. A label is the
integral offset `w = (k, c, y)` of a vertex with its tile pair. Class A's
datasets group labels as k-intervals at fixed `(top, bottom, k + c + y, y)`.
On class B's top layer every raw coordinate grows with q, so that grouping
cannot fit. The bounded functionals are instead `u = 3k + c + y` and
`v = 3k - c`, with growth along `(1, 3, -6)`. `(k, c, y) -> (u, v, k)` is
unimodular, so the typed k-intervals `(top, bottom, u, v, k_lo, k_hi)` are
lossless (`psc.class_a_gap_dataset.typed_intervals` on `[top, bottom, u, v, k]`).
For every residue class of q mod g (g = d + 1) the mode finds the least floor
from which, over *all* later members of the class (at least FIT), the interval
keys are identical and every endpoint is affine in q. A class with no such
floor in the window is reported as unfitted; that is a finite verdict.

Usage: `mojo run -I . class_b_top_layer_profile.mojo plus|minus D QMAX | labels plus|minus D QMAX | barge DMAX QMAX`.
"""

from std.sys import argv
from finite_linear_algebra.mat3 import Mat3
from a1_normal_form_census import CLASS_B, class_member
from lateral_conjugacy_census import theorem_c_region
from psc.bpa import substitution_incidence
from psc.class_a_gap_dataset import typed_intervals
from psc.overlap_seed_patch import build_seed_overlap_graph_from_tables, build_seed_overlap_tables_screened, first_left_aligned_depths
from psc.vertex_coincidence import length_matrix, offset_vector
from psc.pisot import CubicScreen
from substitution_dynamics.barge_class import barge_witness
from substitution_dynamics.substitution import Substitution


comptime GRAPH_CAP = 20000
comptime MAX_QMAX = 48
comptime FIT = 3


struct Point(Copyable, Movable):
    var q: Int
    var vertices: Int
    var depth: Int

    def __init__(out self, q: Int, vertices: Int, depth: Int):
        self.q = q
        self.vertices = vertices
        self.depth = depth


def top_layer_member(plus: Bool, d: Int, q: Int) -> Tuple[Int, Int, Int]:
    var p = 3 * q + 11 - d if plus else 3 * q - 1 - d
    var r = q + 1 if plus else q - 1
    return (p, q, r)


def in_open_top_layer(plus: Bool, p: Int, q: Int) -> Bool:
    if plus:
        return p < 3 * q + 12 and p > 2 * q + 13 and 2 * p > 5 * q + 10
    return p < 3 * q and p > 2 * q + 7 and 2 * p > 5 * q - 5


def profile(plus: Bool, d: Int, qmax: Int) raises -> List[Point]:
    if d < 0 or qmax < 1 or qmax > MAX_QMAX:
        raise Error("need d >= 0 and 1 <= QMAX <= ", MAX_QMAX)
    var screen = CubicScreen()
    var out = List[Point]()
    for q in range(1, qmax + 1):
        var t = top_layer_member(plus, d, q)
        var p = t[0]
        var r = t[2]
        if r < 0 or not in_open_top_layer(plus, p, q):
            continue
        if theorem_c_region(p, q, r):
            raise Error("open top-layer point inside Theorem C's region at q=", q)
        var sigma = class_member(CLASS_B, p, q, r)
        var m = Mat3(substitution_incidence(sigma))
        if abs(m.det()) != 2 or not screen.is_pip(m):
            continue
        var a = build_seed_overlap_graph_from_tables(build_seed_overlap_tables_screened(sigma), GRAPH_CAP)
        if a.capped:
            raise Error("graph capped at q=", q, "; budget exhausted, no verdict")
        var deepest = 0
        for x in first_left_aligned_depths(a):
            if x < 0:
                raise Error("CANDIDATE COUNTEREXAMPLE: a vertex without an offset-zero descendant at (p,q,r)=(", p, ",", q, ",", r, ")")
            deepest = max(deepest, x)
        out.append(Point(q, a.size(), deepest))
    return out^


def affine_tail(pts: List[Point], k: Int, residue: Int) -> Tuple[Bool, Int, Int, Int]:
    """Whether the last FIT points with q = residue mod k are affine in q.
    Returns (fits, slope numerator per k-step, first q of the window, count)."""
    var qs = List[Int]()
    var vs = List[Int]()
    for i in range(len(pts)):
        if pts[i].q % k == residue:
            qs.append(pts[i].q)
            vs.append(pts[i].vertices)
    var n = len(qs)
    if n < FIT:
        return (False, 0, 0, n)
    var a = n - FIT
    var step = vs[a + 1] - vs[a]
    for i in range(a + 1, n):
        if vs[i] - vs[i - 1] != step * ((qs[i] - qs[i - 1]) // k):
            return (False, 0, qs[a], n)
    return (True, step, qs[a], n)


def member_rows(sigma: List[List[Int]]) raises -> List[List[Int]]:
    """Typed k-intervals of the complete graph; raises on a cap or a non-hitting vertex."""
    var tables = build_seed_overlap_tables_screened(sigma)
    var a = build_seed_overlap_graph_from_tables(tables, GRAPH_CAP)
    if a.capped:
        raise Error("graph capped; budget exhausted, no verdict")
    for x in first_left_aligned_depths(a):
        if x < 0:
            raise Error("CANDIDATE COUNTEREXAMPLE: a vertex without an offset-zero descendant")
    var lm = length_matrix(tables)
    var labels = List[List[Int]]()
    for v in a.states:
        var w = offset_vector(lm, v.shift)
        labels.append([v.top, v.bottom, 3 * w[0] + w[1] + w[2], 3 * w[0] - w[1], w[0]])
    return typed_intervals(labels^)


def _same_keys(a: List[List[Int]], b: List[List[Int]]) -> Bool:
    if len(a) != len(b):
        return False
    for i in range(len(a)):
        for j in range(4):
            if a[i][j] != b[i][j]:
                return False
    return True


def _affine_from(rows: List[List[List[Int]]], start: Int) -> Bool:
    """Members start.. (consecutive in the residue class) share keys and every
    endpoint changes by a constant per member."""
    for m in range(start + 1, len(rows)):
        if not _same_keys(rows[m], rows[start]):
            return False
    for m in range(start + 2, len(rows)):
        for i in range(len(rows[m])):
            for e in [4, 5]:
                if rows[m][i][e] - rows[m - 1][i][e] != rows[start + 1][i][e] - rows[start][i][e]:
                    return False
    return True


def label_fit(plus: Bool, d: Int, qmax: Int) raises -> List[Tuple[Int, Int, Int, Int]]:
    """Per residue class of q mod g: (residue, members, fitted floor q or -1, rows)."""
    if d < 0 or qmax < 1 or qmax > MAX_QMAX:
        raise Error("need d >= 0 and 1 <= QMAX <= ", MAX_QMAX)
    var g = d + 1
    var screen = CubicScreen()
    var qs = List[List[Int]]()
    var rows = List[List[List[List[Int]]]]()
    for _ in range(g):
        qs.append(List[Int]())
        rows.append(List[List[List[Int]]]())
    for q in range(1, qmax + 1):
        var t = top_layer_member(plus, d, q)
        if t[2] < 0 or not in_open_top_layer(plus, t[0], q):
            continue
        var sigma = class_member(CLASS_B, t[0], t[1], t[2])
        var m = Mat3(substitution_incidence(sigma))
        if abs(m.det()) != 2 or not screen.is_pip(m):
            continue
        if len(qs[q % g]) > 0 and qs[q % g][len(qs[q % g]) - 1] != q - g:
            raise Error("residue class has a gap at q=", q, "; consecutive members are required")
        qs[q % g].append(q)
        rows[q % g].append(member_rows(sigma))
    var out = List[Tuple[Int, Int, Int, Int]]()
    for res in range(g):
        var n = len(qs[res])
        var floor = -1
        var nrows = 0
        var start = n - FIT
        while start >= 0 and _affine_from(rows[res], start):
            floor = qs[res][start]
            nrows = len(rows[res][start])
            start -= 1
        out.append((res, n, floor, nrows))
    return out^


def barge_count(dmax: Int, qmax: Int) raises -> Tuple[Int, Int]:
    """(PIP top-layer members, members with a Barge witness up to power 3)."""
    if dmax < 0 or qmax < 1 or qmax > MAX_QMAX:
        raise Error("need DMAX >= 0 and 1 <= QMAX <= ", MAX_QMAX)
    var screen = CubicScreen()
    var members = 0
    var witnessed = 0
    for plus in [True, False]:
        for d in range(dmax + 1):
            for q in range(1, qmax + 1):
                var t = top_layer_member(plus, d, q)
                if t[2] < 0 or not in_open_top_layer(plus, t[0], q):
                    continue
                var sigma = class_member(CLASS_B, t[0], t[1], t[2])
                var m = Mat3(substitution_incidence(sigma))
                if abs(m.det()) != 2 or not screen.is_pip(m):
                    continue
                members += 1
                if barge_witness(Substitution(sigma^, 3), 3).found():
                    witnessed += 1
    return (members, witnessed)


def main() raises:
    var args = argv()
    if len(args) > 1 and String(args[1]) == "labels":
        var lplus = String(args[2]) == "plus"
        var ld = Int(String(args[3]))
        var lq = Int(String(args[4]))
        var fits = label_fit(lplus, ld, lq)
        print("class B top layer labels,", "plus" if lplus else "minus", "g =", ld + 1, "q <=", lq)
        var all_fit = True
        for f in fits:
            if f[2] < 0:
                all_fit = False
            print("  q mod", ld + 1, "=", f[0], ":", f[1], "members,",
                  ("typed rows affine in q from q=" + String(f[2]) + " (" + String(f[3]) + " rows)") if f[2] >= 0 else "no affine floor in window")
        print("  ALL RESIDUES FIT" if all_fit else "  NOT ALL RESIDUES FIT")
        return
    if len(args) > 1 and String(args[1]) == "barge":
        var dmax = Int(String(args[2])) if len(args) > 2 else 11
        var qmax = Int(String(args[3])) if len(args) > 3 else 40
        var c = barge_count(dmax, qmax)
        print("class B top layer, d <=", dmax, "q <=", qmax, ": PIP members", c[0], ", with a Barge power/rotation witness (power <= 3)", c[1])
        return
    if len(args) < 4:
        raise Error("usage: plus|minus D QMAX")
    var plus = String(args[1]) == "plus"
    var d = Int(String(args[2]))
    var qmax = Int(String(args[3]))
    var pts = profile(plus, d, qmax)
    print("class B top layer,", "plus" if plus else "minus", "d =", d, "q <=", qmax, ":", len(pts), "PIP members, every vertex hits offset zero")
    for i in range(len(pts)):
        print("  q", pts[i].q, "vertices", pts[i].vertices, "max first-hit depth", pts[i].depth)
    for k in range(1, 7):
        var all_fit = True
        var line = String("  mod ") + String(k) + ":"
        for res in range(k):
            var f = affine_tail(pts, k, res)
            if not f[0]:
                all_fit = False
            line += String(" r") + String(res) + ("=+" + String(f[1]) + "/step from q" + String(f[2]) if f[0] else "=no(" + String(f[3]) + " pts)")
        print(line + (" ALL AFFINE" if all_fit else ""))
