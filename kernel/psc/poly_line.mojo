"""Polynomial line mode: witness paths whose offsets are polynomials.

docs/p1a-a1-prime-2026-10-05.md §3l. Line mode (`psc.cone_witness`) keeps the
offset on a line `c + lambda (e_z - e_y)` and needs `M gamma` affine. In a
cell with `Delta` fixed that holds, as `M (e_z - e_y) = (0, -Delta, -s)` is a
constant. With `Delta = 1 + e` symbolic, a variable `lambda` makes
`lambda M (e_z - e_y)` quadratic, and affine line mode refuses the step.

Here offsets, states and the conditions on them are integer polynomials in
the region's variables, of degree at most `POLY_DEGREE`. The search stays
at a point, in ordinary line mode; only the lift and the verifier are
polynomial. Nothing else changes: a path is verified by recomputing every state from the step data,
each condition is proved on the region (`poly_nonneg_under`: the polynomial
less multiples of at most two of the region's affine assumptions has every
coefficient `>= 0`, so it is `>= 0` at every point), and the end offset must
vanish on the region. A lift carves by a condition's affine part only when
the rest has every coefficient `>= 0` (then the affine part being `>= 0`
suffices); the re-verification proves each condition again.
"""

from std.collections import Dict
from finite_exact.rat_q import Q
from finite_linear_algebra.qlinalg import rref
from finite_linear_algebra.scalar import q_int, q_is_zero
from psc.cone_witness import (
    ConeFamily,
    Prover,
    SEG_LETTER,
    SEG_OPAQUE,
    WitnessStep,
    aff_const,
    aff_eval,
    aff_nonneg,
    aff_sub,
    apply_step_line,
    _is_zero,
    _line_candidates,
    _multipliers,
    _within,
)

comptime POLY_DEGREE = 8  # the largest degree a state, offset or condition may reach
comptime LIFT_NODES = 4000  # nodes of the lift's depth-first search over candidates


# ---------------------------------------------------------------------------
# Sparse integer polynomials. A monomial is the ascending list of its
# variables' indices (0-based, repeats for powers); its key joins them by
# "."; the constant's key is "".
# ---------------------------------------------------------------------------


def _mono_key(vars: List[Int]) -> String:
    var out = String()
    for k in range(len(vars)):
        if k > 0:
            out += "."
        out += String(vars[k])
    return out


def _mono_vars(key: String) raises -> List[Int]:
    var out = List[Int]()
    if key == "":
        return out^
    for part in key.split("."):
        out.append(Int(String(part)))
    return out^


struct Poly(Copyable, Movable):
    """An integer polynomial: monomial key -> nonzero coefficient."""

    var terms: Dict[String, Int]

    def __init__(out self):
        self.terms = Dict[String, Int]()

    def add_term(mut self, key: String, c: Int):
        if c == 0:
            return
        var v = self.terms.get(key, 0) + c
        if v == 0:
            _ = self.terms.pop(key, 0)
        else:
            self.terms[key] = v


def poly_const(c: Int) -> Poly:
    var p = Poly()
    p.add_term("", c)
    return p^


def poly_from_aff(a: List[Int]) -> Poly:
    """`a[0] + sum a[k] n_(k-1)`."""
    var p = Poly()
    p.add_term("", a[0])
    for k in range(1, len(a)):
        p.add_term(String(k - 1), a[k])
    return p^


def poly_add(p: Poly, q: Poly) -> Poly:
    var out = p.copy()
    for e in q.terms.items():
        out.add_term(e.key, e.value)
    return out^


def poly_scale(p: Poly, s: Int) -> Poly:
    var out = Poly()
    for e in p.terms.items():
        out.add_term(e.key, s * e.value)
    return out^


def poly_sub(p: Poly, q: Poly) -> Poly:
    return poly_add(p, poly_scale(q, -1))


def poly_mul(p: Poly, q: Poly) raises -> Poly:
    var out = Poly()
    for e in p.terms.items():
        var a = _mono_vars(e.key)
        for f in q.terms.items():
            var v = a.copy()
            for x in _mono_vars(f.key):
                v.append(x)
            sort(v)
            out.add_term(_mono_key(v), e.value * f.value)
    return out^


def poly_degree(p: Poly) raises -> Int:
    var d = 0
    for e in p.terms.items():
        d = max(d, len(_mono_vars(e.key)))
    return d


def poly_eval(p: Poly, ns: List[Int]) raises -> Int:
    var total = 0
    for e in p.terms.items():
        var t = e.value
        for x in _mono_vars(e.key):
            t *= ns[x]
        total += t
    return total


def poly_is_zero(p: Poly) -> Bool:
    return len(p.terms) == 0


def poly_is_const(p: Poly) -> Bool:
    for e in p.terms.items():
        if e.key != "":
            return False
    return True


def poly_affine_part(p: Poly, m: Int) raises -> List[Int]:
    var out = aff_const(m, 0)
    for e in p.terms.items():
        var v = _mono_vars(e.key)
        if len(v) == 0:
            out[0] += e.value
        elif len(v) == 1:
            out[v[0] + 1] += e.value
    return out^


def poly_higher(p: Poly) raises -> Poly:
    """The terms of degree at least 2."""
    var out = Poly()
    for e in p.terms.items():
        if len(_mono_vars(e.key)) >= 2:
            out.add_term(e.key, e.value)
    return out^


def poly_nonneg(p: Poly) -> Bool:
    """Every coefficient `>= 0`: then `p >= 0` on the orthant."""
    for e in p.terms.items():
        if e.value < 0:
            return False
    return True


def poly_nonneg_under(p: Poly, prover: Prover) raises -> Bool:
    """`p >= 0` on a region: `p`, or `p` less multiples of one or two of its
    affine assumptions (multipliers as in `Prover.nonneg`, read off `p`'s
    affine part), has every coefficient `>= 0`."""
    if poly_nonneg(p):
        return True
    ref A = prover.assume
    for i in range(len(A)):
        var m = len(A[i]) - 1
        var li = _multipliers(poly_affine_part(p, m), A[i])
        for x in range(len(li)):
            var g = poly_sub(p, poly_scale(poly_from_aff(A[i]), li[x]))
            if poly_nonneg(g):
                return True
            for j in range(i, len(A)):
                var lj = _multipliers(poly_affine_part(g, m), A[j])
                for y in range(len(lj)):
                    if poly_nonneg(poly_sub(g, poly_scale(poly_from_aff(A[j]), lj[y]))):
                        return True
    return False


def poly_vanishes_under(p: Poly, prover: Prover) raises -> Bool:
    return poly_nonneg_under(p, prover) and poly_nonneg_under(poly_scale(p, -1), prover)


def poly_key(p: Poly) -> String:
    """A canonical rendering, for deduplication and diagnostics."""
    var keys = List[String]()
    for e in p.terms.items():
        keys.append(e.key)
    sort(keys)
    var out = String()
    for k in range(len(keys)):
        out += "[" + keys[k] + "]" + String(p.terms.get(keys[k], 0)) + " "
    return out^


# ---------------------------------------------------------------------------
# Line mode over polynomials.
# ---------------------------------------------------------------------------


struct PolyStep(Copyable, Movable):
    """A step: segment `seg_a` of `sigma(a)` at offset `off_a`, and the same
    for `b`; offsets are polynomials (0 for a letter segment)."""

    var seg_a: Int
    var off_a: Poly
    var seg_b: Int
    var off_b: Poly

    def __init__(out self, seg_a: Int, var off_a: Poly, seg_b: Int, var off_b: Poly):
        self.seg_a = seg_a
        self.off_a = off_a^
        self.seg_b = seg_b
        self.off_b = off_b^


struct PolyState(Copyable, Movable):
    """The state a step leads to and the conditions (polynomials that must be
    `>= 0`) under which it is a step; `ok` false if structurally refused."""

    var ok: Bool
    var a: Int
    var b: Int
    var gamma: List[Poly]
    var conds: List[Poly]

    def __init__(out self):
        self.ok = False
        self.a = -1
        self.b = -1
        self.gamma = List[Poly]()
        self.conds = List[Poly]()


def m_times_poly(fam: ConeFamily, gamma: List[Poly]) raises -> List[Poly]:
    """`M gamma`, or an empty list past `POLY_DEGREE`."""
    var out = List[Poly]()
    for i in range(3):
        var acc = Poly()
        for j in range(3):
            acc = poly_add(acc, poly_mul(poly_from_aff(fam.incidence[3 * i + j]), gamma[j]))
        if poly_degree(acc) > POLY_DEGREE:
            return List[Poly]()
        out.append(acc^)
    return out^


def _offset_conditions(fam: ConeFamily, a: Int, s: Int, off: Poly, mut conds: List[Poly]) raises -> Bool:
    """The conditions placing `off` inside segment `s`; false if impossible."""
    ref seg = fam.images[a][s]
    if seg.kind == SEG_OPAQUE:
        return False
    if seg.kind == SEG_LETTER:
        return poly_is_zero(off)
    conds.append(off.copy())
    conds.append(poly_sub(poly_sub(poly_from_aff(seg.length), off), poly_const(1)))
    return True


def poly_step(fam: ConeFamily, a: Int, b: Int, gamma: List[Poly], step: PolyStep) raises -> PolyState:
    """`gamma' = M gamma + pi(sigma(a)[:i]) - pi(sigma(b)[:k])`, with the
    run offsets added in their letters' coordinates, and the offset
    conditions."""
    var out = PolyState()
    if step.seg_a < 0 or step.seg_a >= len(fam.images[a]) or step.seg_b < 0 or step.seg_b >= len(fam.images[b]):
        return out^
    if not _offset_conditions(fam, a, step.seg_a, step.off_a, out.conds) or not _offset_conditions(fam, b, step.seg_b, step.off_b, out.conds):
        return out^
    var mg = m_times_poly(fam, gamma)
    if len(mg) == 0:
        return out^
    var pa = fam.prefix_before(a, step.seg_a)
    var pb = fam.prefix_before(b, step.seg_b)
    ref sa = fam.images[a][step.seg_a]
    ref sb = fam.images[b][step.seg_b]
    for i in range(3):
        var d = poly_sub(poly_add(mg[i], poly_from_aff(pa[i])), poly_from_aff(pb[i]))
        if sa.is_run() and sa.letter == i:
            d = poly_add(d, step.off_a)
        if sb.is_run() and sb.letter == i:
            d = poly_sub(d, step.off_b)
        if poly_degree(d) > POLY_DEGREE:
            return PolyState()
        out.gamma.append(d^)
    out.ok = True
    out.a = sa.letter
    out.b = sb.letter
    return out^


def verify_witness_poly(fam: ConeFamily, a0: Int, b0: Int, steps: List[PolyStep], prover: Prover) raises -> Bool:
    """Re-derive every state from the steps alone; true iff every offset
    condition is proved on the region and the path ends at `(a, a, 0)` with
    the offset proved to vanish there."""
    if len(steps) == 0:
        return False
    var a = a0
    var b = b0
    var gamma = List[Poly]()
    for _ in range(3):
        gamma.append(Poly())
    for l in range(len(steps)):
        var r = poly_step(fam, a, b, gamma, steps[l])
        if not r.ok:
            return False
        for k in range(len(r.conds)):
            if not poly_nonneg_under(r.conds[k], prover):
                return False
        a = r.a
        b = r.b
        gamma = r.gamma.copy()
    if a != b:
        return False
    for i in range(3):
        if not poly_vanishes_under(gamma[i], prover):
            return False
    return True


def _anchors(fam: ConeFamily, a: Int, s: Int, v: Int, ns: List[Int]) -> List[Poly]:
    """Offsets into segment `s` of `sigma(a)` taking the value `v` at `ns`:
    `v` itself, and `v` counted from the segment's end."""
    var out = List[Poly]()
    ref seg = fam.images[a][s]
    if not seg.is_run():
        out.append(Poly())
        return out^
    out.append(poly_const(v))
    var end = poly_add(poly_sub(poly_from_aff(seg.length), poly_const(aff_eval(seg.length, ns))), poly_const(v))
    out.append(end^)
    return out^


def _lift_candidates(fam: ConeFamily, a: Int, b: Int, gamma: List[Poly], sa: Int, va: Int, sb: Int, vb: Int, target: List[Int], ns: List[Int], ly: Int, lz: Int) raises -> List[PolyStep]:
    """Steps on segments `sa`, `sb` whose offsets take the point's values
    `va`, `vb` at `ns`: each offset anchored at the segment's start or end,
    or solved so that its letter's coordinate of the new state is the
    constant `target` (the point's new state), or, for two runs in the line
    letters, one solved from the other so that the `ly + lz` sum is
    constant. Candidates are filtered by their values at `ns`."""
    var out = List[PolyStep]()
    var mg = m_times_poly(fam, gamma)
    if len(mg) == 0:
        return out^
    ref ga = fam.images[a][sa]
    ref gb = fam.images[b][sb]
    if ga.kind == SEG_OPAQUE or gb.kind == SEG_OPAQUE:
        return out^
    var pa = fam.prefix_before(a, sa)
    var pb = fam.prefix_before(b, sb)
    var d = List[Poly]()
    for i in range(3):
        d.append(poly_sub(poly_add(mg[i], poly_from_aff(pa[i])), poly_from_aff(pb[i])))
    var la = ga.letter if ga.is_run() else -1
    var lb = gb.letter if gb.is_run() else -1
    var offs_a = _anchors(fam, a, sa, va, ns)
    var offs_b = _anchors(fam, b, sb, vb, ns)
    if la >= 0 and la != lb:
        offs_a.append(poly_sub(poly_const(target[la]), d[la]))
    if lb >= 0 and lb != la:
        offs_b.append(poly_sub(d[lb], poly_const(target[lb])))
    var base_a = len(offs_a)
    var base_b = len(offs_b)
    if (la == ly or la == lz) and (lb == ly or lb == lz):
        var need = poly_sub(poly_const(target[ly] + target[lz]), poly_add(d[ly], d[lz]))
        for k in range(base_b):
            offs_a.append(poly_add(need, offs_b[k]))
        for k in range(base_a):
            offs_b.append(poly_sub(offs_a[k], need))
    for i in range(len(offs_a)):
        if poly_eval(offs_a[i], ns) != va:
            continue
        for j in range(len(offs_b)):
            if poly_eval(offs_b[j], ns) != vb:
                continue
            out.append(PolyStep(sa, offs_a[i].copy(), sb, offs_b[j].copy()))
    return out^


struct PolyLift(Copyable, Movable):
    var ok: Bool
    var steps: List[PolyStep]
    var ineqs: List[List[Int]]  # affine carving forms, each >= 0 at the base point
    var a: Int
    var b: Int
    var gamma: List[Poly]
    var why: String

    def __init__(out self):
        self.ok = False
        self.steps = List[PolyStep]()
        self.ineqs = List[List[Int]]()
        self.a = -1
        self.b = -1
        self.gamma = List[Poly]()
        self.why = String()


def carving_forms_of(conds: List[Poly], m: Int, ns: List[Int], mut ineqs: List[List[Int]]) raises -> Bool:
    """Affine forms implying each condition: its affine part, usable when the
    rest has every coefficient `>= 0` and the part is `>= 0` at `ns`."""
    for k in range(len(conds)):
        if not poly_nonneg(poly_higher(conds[k])):
            return False
        var f = poly_affine_part(conds[k], m)
        if aff_eval(f, ns) < 0:
            return False
        if not aff_nonneg(f):
            ineqs.append(f^)
    return True


struct _LiftFrame(Copyable, Movable):
    var level: Int
    var a: Int
    var b: Int
    var gamma: List[Poly]
    var steps: List[PolyStep]
    var ineqs: List[List[Int]]

    def __init__(out self, level: Int, a: Int, b: Int, var gamma: List[Poly], var steps: List[PolyStep], var ineqs: List[List[Int]]):
        self.level = level
        self.a = a
        self.b = b
        self.gamma = gamma^
        self.steps = steps^
        self.ineqs = ineqs^


def _affine_end(gamma: List[Poly]) raises -> Bool:
    for i in range(3):
        if not poly_is_zero(poly_higher(gamma[i])):
            return False
    return True


def lift_path_poly(fam: ConeFamily, point: ConeFamily, ns: List[Int], a0: Int, b0: Int, steps: List[WitnessStep], ly: Int, lz: Int) raises -> PolyLift:
    """`psc.cone_witness.lift_path` over polynomials: replay the point
    family's `steps` on the region family. At each level the candidates are
    built from the point's step (`_lift_candidates`, offsets agreeing with
    the point's) and must reach the point's letters and carve by affine
    forms. A depth-first search over them (lowest degree, then fewest forms,
    first; at most `LIFT_NODES` nodes) returns the first lift whose end
    offset has no term of degree >= 2, so that it can vanish on a region."""
    var out = PolyLift()
    # the point path's states, level by level
    var targets = List[List[Int]]()
    var letters = List[List[Int]]()
    var ap = a0
    var bp = b0
    var gp = List[List[Int]]()
    for _ in range(3):
        gp.append(aff_const(0, 0))
    for l in range(len(steps)):
        var rp = apply_step_line(point, ap, bp, gp, steps[l])
        if not rp.ok:
            out.why = "level " + String(l) + ": the point path does not replay"
            return out^
        var t = List[Int]()
        for i in range(3):
            t.append(rp.gamma[i][0])
        targets.append(t^)
        letters.append(List[Int]([rp.a, rp.b]))
        ap = rp.a
        bp = rp.b
        gp = rp.gamma.copy()
    var zero = List[Poly]()
    for _ in range(3):
        zero.append(Poly())
    var stack = List[_LiftFrame]()
    stack.append(_LiftFrame(0, a0, b0, zero^, List[PolyStep](), List[List[Int]]()))
    var nodes = 0
    var deepest = 0
    var non_affine_ends = 0
    while len(stack) > 0 and nodes < LIFT_NODES:
        nodes += 1
        var fr = stack.pop()
        var l = fr.level
        if l == len(steps):
            if _affine_end(fr.gamma):
                out.ok = True
                out.a = fr.a
                out.b = fr.b
                out.steps = fr.steps.copy()
                out.ineqs = fr.ineqs.copy()
                out.gamma = fr.gamma.copy()
                return out^
            non_affine_ends += 1
            continue
        deepest = max(deepest, l)
        var cands = _lift_candidates(fam, fr.a, fr.b, fr.gamma, steps[l].seg_a, steps[l].off_a[0], steps[l].seg_b, steps[l].off_b[0], targets[l], ns, ly, lz)
        var children = List[_LiftFrame]()
        var ranks = List[Int]()
        for c in range(len(cands)):
            var rc = poly_step(fam, fr.a, fr.b, fr.gamma, cands[c])
            if not rc.ok or rc.a != letters[l][0] or rc.b != letters[l][1]:
                continue
            var forms = fr.ineqs.copy()
            var before = len(forms)
            if not carving_forms_of(rc.conds, fam.m, ns, forms):
                continue
            var degree = 0
            for i in range(3):
                degree = max(degree, poly_degree(rc.gamma[i]))
            var st = fr.steps.copy()
            st.append(cands[c].copy())
            ranks.append(64 * degree + len(forms) - before)
            children.append(_LiftFrame(l + 1, rc.a, rc.b, rc.gamma.copy(), st^, forms^))
        # push the worst first, so the best is explored first
        while len(children) > 0:
            var worst = 0
            for k in range(1, len(children)):
                if ranks[k] > ranks[worst]:
                    worst = k
            stack.append(children[worst].copy())
            _ = children.pop(worst)
            _ = ranks.pop(worst)
    out.why = "no lift with an affine end (" + String(nodes) + " nodes, deepest level " + String(deepest) + ", " + String(non_affine_ends) + " non-affine ends)"
    return out^


def poly_steps(steps: List[WitnessStep]) -> List[PolyStep]:
    """Affine steps as polynomial ones."""
    var out = List[PolyStep]()
    for k in range(len(steps)):
        out.append(PolyStep(steps[k].seg_a, poly_from_aff(steps[k].off_a), steps[k].seg_b, poly_from_aff(steps[k].off_b)))
    return out^


def steps_at(steps: List[PolyStep], ns: List[Int]) raises -> List[WitnessStep]:
    """The steps at a point: constant offsets (forms over no variables), for
    the point family's ordinary verifier."""
    var out = List[WitnessStep]()
    for k in range(len(steps)):
        out.append(WitnessStep(steps[k].seg_a, List[Int]([poly_eval(steps[k].off_a, ns)]), steps[k].seg_b, List[Int]([poly_eval(steps[k].off_b, ns)])))
    return out^


# ---------------------------------------------------------------------------
# Lifting by linear algebra. Fix the point path's segments; then the letters
# of every state are fixed, and the end offset is linear in the run offsets:
# gamma_L = P_0 + sum over unknowns t_j of t_j P_j, each offset an unknown
# affine form o = c + sum u_k n_k. "gamma_L = 0 identically" and "each
# offset takes the point's value at ns" are linear equations over Q in the
# unknowns. A solution (free unknowns 0) that is integral gives a path on
# the whole region whose only conditions are the offsets' affine bounds.
# ---------------------------------------------------------------------------


def _q_to_int(x: Q) raises -> Int:
    """An exact rational that is a small integer, or raise."""
    if x.rejected:
        raise Error("a rejected rational in a lift")
    if x.den.limb_count() != 1 or x.den.limb(0) != 1:
        raise Error("not an integer")
    if x.num.is_zero():
        return 0
    if x.num.limb_count() != 1 or x.num.limb(0) > UInt64(1 << 40):
        raise Error("an integer too large for a lift")
    var v = Int(x.num.limb(0))
    return v if x.num.sign > 0 else -v


def solve_lift(fam: ConeFamily, point: ConeFamily, ns: List[Int], a0: Int, b0: Int, steps: List[WitnessStep]) raises -> PolyLift:
    """The point path's segments, with affine offsets solving `gamma_L = 0`
    identically on the region and agreeing with the point's offsets at `ns`;
    `ineqs` are the offsets' affine bounds not already nonnegative."""
    var out = PolyLift()
    var m = fam.m
    var L = len(steps)
    # the point path: letters and offsets
    var la = List[Int]()
    var lb = List[Int]()
    var ap = a0
    var bp = b0
    var gp = List[List[Int]]()
    for _ in range(3):
        gp.append(aff_const(0, 0))
    var letters_a = List[Int]([a0])
    var letters_b = List[Int]([b0])
    for l in range(L):
        var rp = apply_step_line(point, ap, bp, gp, steps[l])
        if not rp.ok:
            out.why = "the point path does not replay"
            return out^
        ap = rp.a
        bp = rp.b
        gp = rp.gamma.copy()
        letters_a.append(ap)
        letters_b.append(bp)
    if ap != bp:
        out.why = "the point path ends off the diagonal"
        return out^
    # unknowns: for each level and side with a run segment, m + 1 of them
    var owner_level = List[Int]()
    var owner_side = List[Int]()
    var first = List[Int]()  # per level and side (2 l + side): first unknown, or -1
    var count = 0
    for l in range(L):
        for side in range(2):
            var a = letters_a[l] if side == 0 else letters_b[l]
            var sg = steps[l].seg_a if side == 0 else steps[l].seg_b
            if fam.images[a][sg].kind == SEG_OPAQUE:
                out.why = "a step names an opaque segment"
                return out^
            if fam.images[a][sg].is_run():
                first.append(count)
                for _ in range(m + 1):
                    owner_level.append(l)
                    owner_side.append(side)
                count += m + 1
            else:
                first.append(-1)
    # gamma as parts: index 0 the constant part, 1 + j the coefficient of t_j
    var parts = List[List[Poly]]()
    for _ in range(count + 1):
        var z = List[Poly]()
        for _ in range(3):
            z.append(Poly())
        parts.append(z^)
    for l in range(L):
        var a = letters_a[l]
        var b = letters_b[l]
        ref sa = fam.images[a][steps[l].seg_a]
        ref sb = fam.images[b][steps[l].seg_b]
        var pa = fam.prefix_before(a, steps[l].seg_a)
        var pb = fam.prefix_before(b, steps[l].seg_b)
        for j in range(count + 1):
            var mg = List[Poly]()
            for i in range(3):
                var acc = Poly()
                for k in range(3):
                    acc = poly_add(acc, poly_mul(poly_from_aff(fam.incidence[3 * i + k]), parts[j][k]))
                mg.append(acc^)
            if j == 0:
                for i in range(3):
                    mg[i] = poly_sub(poly_add(mg[i], poly_from_aff(pa[i])), poly_from_aff(pb[i]))
            parts[j] = mg^
        # this level's offsets enter linearly
        for side in range(2):
            var f = first[2 * l + side]
            if f < 0:
                continue
            var letter = sa.letter if side == 0 else sb.letter
            var sign = 1 if side == 0 else -1
            parts[1 + f][letter] = poly_add(parts[1 + f][letter], poly_const(sign))
            for k in range(m):
                var mono = Poly()
                mono.add_term(String(k), sign)
                parts[1 + f + 1 + k][letter] = poly_add(parts[1 + f + 1 + k][letter], mono)
        for j in range(count + 1):
            for i in range(3):
                if poly_degree(parts[j][i]) > POLY_DEGREE:
                    out.why = "the end offset's degree exceeds the cap"
                    return out^
    # equations: every monomial of every coordinate of gamma_L vanishes
    var keys = List[String]()
    var seen = Dict[String, Int]()
    for j in range(count + 1):
        for i in range(3):
            for e in parts[j][i].terms.items():
                var key = String(i) + "|" + e.key
                if key not in seen:
                    seen[key] = len(keys)
                    keys.append(key)
    var rows = List[List[Q]]()
    for r in range(len(keys)):
        var row = List[Q]()
        for _ in range(count + 1):
            row.append(q_int(0))
        rows.append(row^)
    for j in range(count + 1):
        for i in range(3):
            for e in parts[j][i].terms.items():
                var r = seen[String(i) + "|" + e.key]
                if j == 0:
                    rows[r][count] = q_int(-e.value)  # right-hand side
                else:
                    rows[r][j - 1] = q_int(e.value)
    # agreement with the point's offsets
    for l in range(L):
        for side in range(2):
            var f = first[2 * l + side]
            if f < 0:
                continue
            var row = List[Q]()
            for _ in range(count + 1):
                row.append(q_int(0))
            row[f] = q_int(1)
            for k in range(m):
                row[f + 1 + k] = q_int(ns[k])
            row[count] = q_int(steps[l].off_a[0] if side == 0 else steps[l].off_b[0])
            rows.append(row^)
    var red = rref(rows)
    ref R = red[0]
    ref pivots = red[1]
    var t = List[Int](length=count, fill=0)
    for r in range(len(pivots)):
        if pivots[r] == count:
            out.why = "no affine offsets make the end offset vanish on the region"
            return out^
        try:
            t[pivots[r]] = _q_to_int(R[r][count])
        except:
            out.why = "the solving offsets are not integral"
            return out^
    # the offsets, the path, and its conditions
    for l in range(L):
        var offs = List[Poly]()
        for side in range(2):
            var f = first[2 * l + side]
            if f < 0:
                offs.append(Poly())
                continue
            var c = List[Int]()
            for k in range(m + 1):
                c.append(t[f + k])
            offs.append(poly_from_aff(c))
        out.steps.append(PolyStep(steps[l].seg_a, offs[0].copy(), steps[l].seg_b, offs[1].copy()))
    var gamma = List[Poly]()
    for _ in range(3):
        gamma.append(Poly())
    var a = a0
    var b = b0
    for l in range(L):
        var r = poly_step(fam, a, b, gamma, out.steps[l])
        if not r.ok:
            out.why = "the solved path does not step"
            return out^
        if not carving_forms_of(r.conds, m, ns, out.ineqs):
            out.why = "the solved offsets leave the region's runs at the point"
            return out^
        a = r.a
        b = r.b
        gamma = r.gamma.copy()
    out.ok = True
    out.a = a
    out.b = b
    out.gamma = gamma^
    return out^


def enumerate_point_paths(point: ConeFamily, a0: Int, b0: Int, bound: Int, max_level: Int, ly: Int, lz: Int, max_paths: Int, max_nodes: Int) -> List[List[WitnessStep]]:
    """Witness paths of a point family (constant offsets), by depth-first
    search over the line candidates, shortest first by iterative deepening:
    each depth limit up to `max_level` in turn, at most `max_paths` paths and
    `max_nodes` nodes in all. Distinct paths may share states: `solve_lift`
    asks only for their segments."""
    var out = List[List[WitnessStep]]()
    var nodes = 0
    for depth in range(1, max_level + 1):
        var zero = List[List[Int]]()
        for _ in range(3):
            zero.append(aff_const(point.m, 0))
        # frames: state and the path so far
        var sa = List[Int]([a0])
        var sb = List[Int]([b0])
        var sg = List[List[List[Int]]]()
        sg.append(zero^)
        var sp = List[List[WitnessStep]]()
        sp.append(List[WitnessStep]())
        while len(sa) > 0:
            if nodes >= max_nodes or len(out) >= max_paths:
                return out^
            nodes += 1
            var a = sa.pop()
            var b = sb.pop()
            var g = sg.pop()
            var path = sp.pop()
            if len(path) == depth:
                continue
            var cands = _line_candidates(point, a, b, g, bound, ly, lz)
            for c in range(len(cands)):
                var r = apply_step_line(point, a, b, g, cands[c])
                if not r.ok or not _within(r.gamma, bound):
                    continue
                var p2 = path.copy()
                p2.append(cands[c].copy())
                if r.a == r.b and _is_zero(r.gamma):
                    if len(p2) == depth:
                        out.append(p2^)
                    continue
                sa.append(r.a)
                sb.append(r.b)
                sg.append(r.gamma.copy())
                sp.append(p2^)
    return out^
