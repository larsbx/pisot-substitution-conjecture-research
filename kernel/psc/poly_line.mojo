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
    _multipliers,
)

comptime POLY_DEGREE = 3  # the largest degree a state, offset or condition may reach


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


def lift_path_poly(fam: ConeFamily, point: ConeFamily, ns: List[Int], a0: Int, b0: Int, steps: List[WitnessStep], ly: Int, lz: Int) raises -> PolyLift:
    """`psc.cone_witness.lift_path` over polynomials: replay the point
    family's `steps` on the region family. At each level the candidates are
    built from the point's step (`_lift_candidates`, offsets agreeing with
    the point's); the one taken reaches the point's letters, carves by
    affine forms, and has the lowest degree, then the fewest forms."""
    var out = PolyLift()
    var a = a0
    var b = b0
    var gr = List[Poly]()
    var gp = List[List[Int]]()
    for _ in range(3):
        gr.append(Poly())
        gp.append(aff_const(0, 0))
    var ap = a0
    var bp = b0
    for l in range(len(steps)):
        var rp = apply_step_line(point, ap, bp, gp, steps[l])
        if not rp.ok:
            out.why = "level " + String(l) + ": the point path does not replay"
            return out^
        var target = List[Int]()
        for i in range(3):
            target.append(rp.gamma[i][0])
        var cands = _lift_candidates(fam, a, b, gr, steps[l].seg_a, steps[l].off_a[0], steps[l].seg_b, steps[l].off_b[0], target, ns, ly, lz)
        var best = -1
        var best_rank = 1 << 30
        var best_state = PolyState()
        var best_forms = List[List[Int]]()
        var reaching = 0
        for c in range(len(cands)):
            var rc = poly_step(fam, a, b, gr, cands[c])
            if not rc.ok or rc.a != rp.a or rc.b != rp.b:
                continue
            reaching += 1
            var forms = List[List[Int]]()
            if not carving_forms_of(rc.conds, fam.m, ns, forms):
                continue
            var degree = 0
            for i in range(3):
                degree = max(degree, poly_degree(rc.gamma[i]))
            var rank = 64 * degree + len(forms)  # lowest degree first, then fewest forms
            if rank < best_rank:
                best = c
                best_rank = rank
                best_state = rc^
                best_forms = forms^
        if best < 0:
            out.why = "level " + String(l) + ": of " + String(len(cands)) + " polynomial candidates agreeing with the point, " + String(reaching) + " step, none carves by affine forms"
            return out^
        out.steps.append(cands[best].copy())
        for k in range(len(best_forms)):
            out.ineqs.append(best_forms[k].copy())
        a = best_state.a
        b = best_state.b
        gr = best_state.gamma.copy()
        ap = rp.a
        bp = rp.b
        gp = rp.gamma.copy()
    out.ok = True
    out.a = a
    out.b = b
    out.gamma = gr^
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
