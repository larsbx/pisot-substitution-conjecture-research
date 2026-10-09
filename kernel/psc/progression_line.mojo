"""Progression certificates: boundary hitting on a line whose seed graph grows.

docs/p1b-edge-progressions-2026-10-09.md. Near a Lemma P1 edge the seed graph
of a line is not bounded: it is a finite *skeleton* times an index. Lemma EP
gives a parameter-free integer vector `u` with `M u = s u + k e_y` (`s = +1` at
the `f(1)` edge, `-1` at the `f(-1)` edge, `k = -f(+-1) >= 1`), and every
overlap is `w = w0 + j u` with `j = phi(w)` for a coordinate functional `phi`
(`phi(u) = 1`, `phi(e_y) = 0`). A *state* is `(a, b, w0)` with `phi(w0) = 0`;
its members are `w0 + j u` for `j` in a set of integer intervals whose ends are
affine in the line parameter `q`.

Everything is decided for every `q` above a certified threshold, with the
line engine's sign reads (`psc.symbolic_line.SymbolicClosure`), so this module
adds no new sign machinery:

1. **Edges.** A child of member `(S, j)` is `B0 + j s u + j k e_y + m e_y` for a
   segment pair, `B0 = M w0 + prefix difference`. Inside a run the position
   `m` absorbs `j k`: with `m' = m + j k` the child is the state
   `(a', b', B0 - phi(B0) u + m' e_y)` at index `j' = phi(B0) + s j`. Its
   validity (realness, and the run bounds `rlo <= m' - j k <= rhi`) is a
   `j`-interval with affine ends, fitted and certified like run positions.
   Outside a run the child's state depends on `j` and only a bounded window of
   `j` is real; each such `j` is a child of its own.
2. **Members.** States and index sets are closed together from the seeds (a
   state is expanded once it has a member), by a fixed point with widening
   toward each state's realness interval. Widening only
   enlarges them, and a superset of the reachable members is enough: what is
   proved below is proved for every member of the superset.
3. **Ranking.** For translation (`s = +1`): every member with `|j| >= 2`
   has an edge to a member of smaller `|j|`, or a drift-0 edge to a member
   already ranked (a monotone fixed point). This is checked as interval
   cover statements, uniformly in `q`.
4. **Core.** The members with `|j| <= 1` are finitely many explicit
   vertices. Each must reach offset zero inside the core.

Then every member reaches offset zero. A path that keeps to ranked edges
strictly lowers `(|j|, tie order)` until it enters the core, and the core
hits. Any failure raises. A capped or unsupported situation (a run bound
that `k` does not divide, a non-constant drift, a range that is not affine)
also raises; none is a verdict.
"""

from std.collections import Dict
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from psc.exact import q_string
from psc.symbolic_line import (
    QX,
    TPoly,
    Eventual,
    Line,
    LineCertificate,
    SymbolicClosure,
    certify_line,
    certify_wedge_pisot,
    qx_add,
    qx_at,
    qx_const,
    qx_const_term,
    qx_is_const,
    qx_is_zero,
    qx_key,
    qx_neg,
    qx_norm,
    qx_scale,
    qx_sub,
    tp_add,
    tp_scale,
    tp_sub,
    w_add,
    w_sub,
    w_unit,
)

comptime STATE_CAP = 5000
comptime WIDEN_AFTER = 4
comptime FIXPOINT_CAP = 200


# ---------------------------------------------------------------------------
# Integer intervals with ends affine in q, compared eventually.
# ---------------------------------------------------------------------------


def small_int(x: Q) raises -> Int:
    """`x` as a machine integer; raises unless it is an integer of one limb."""
    if x.den.limb_count() != 1 or x.den.limb(0) != 1 or x.num.limb_count() > 1:
        raise Error("not a small integer")
    return x.num.sign * Int(x.num.limb(0))


def qx_div_round(p: QX, k: Int, up: Bool) raises -> QX:
    """`ceil(p / k)` (`up`) or `floor(p / k)` for an integer `p` affine in `q`:
    exact and affine when `k` divides every non-constant coefficient. Raises
    otherwise; restrict the line to a sublattice of its parameter."""
    var f = qx_norm(p)
    if k == 1 or len(f) == 0:
        return f^
    if len(f) > 1:
        raise Error("a run bound depends on a second parameter")
    var row = List[Q]()
    for i in range(len(f[0])):
        var c = small_int(f[0][i])
        if i == 0:
            row.append(q_int(-((-c) // k) if up else c // k))
        elif c % k != 0:
            raise Error("k does not divide a run bound: restrict the line to a sublattice")
        else:
            row.append(q_int(c // k))
    return qx_norm([row^])


struct Interval(Copyable, Movable):
    var lo: QX  # inclusive
    var hi: QX  # inclusive

    def __init__(out self, lo: QX, hi: QX):
        self.lo = lo.copy()
        self.hi = hi.copy()

    def key(self) -> String:
        return "[" + qx_key(self.lo) + ":" + qx_key(self.hi) + "]"


def _le(mut ev: Eventual, x: QX, y: QX) raises -> Bool:
    return ev.sign(qx_sub(y, x)) >= 0


def _qmax(mut ev: Eventual, x: QX, y: QX) raises -> QX:
    return x.copy() if _le(ev, y, x) else y.copy()


def _qmin(mut ev: Eventual, x: QX, y: QX) raises -> QX:
    return x.copy() if _le(ev, x, y) else y.copy()


def iv_intersect(mut ev: Eventual, x: Interval, y: Interval) raises -> List[Interval]:
    var lo = _qmax(ev, x.lo, y.lo)
    var hi = _qmin(ev, x.hi, y.hi)
    var out = List[Interval]()
    if _le(ev, lo, hi):
        out.append(Interval(lo, hi))
    return out^


def set_intersect(mut ev: Eventual, xs: List[Interval], ys: List[Interval]) raises -> List[Interval]:
    var out = List[Interval]()
    for i in range(len(xs)):
        for j in range(len(ys)):
            out.extend(iv_intersect(ev, xs[i], ys[j]))
    return normalize_set(ev, out)


def normalize_set(mut ev: Eventual, xs: List[Interval]) raises -> List[Interval]:
    """Sort by lower end and merge overlapping or adjacent intervals."""
    var items = xs.copy()
    # insertion sort with eventual comparisons (the sets are small)
    for i in range(1, len(items)):
        var j = i
        while j > 0 and not _le(ev, items[j - 1].lo, items[j].lo):
            var t = items[j - 1].copy()
            items[j - 1] = items[j].copy()
            items[j] = t^
            j -= 1
    var out = List[Interval]()
    for i in range(len(items)):
        if len(out) > 0 and _le(ev, items[i].lo, qx_add(out[len(out) - 1].hi, qx_const(1))):
            out[len(out) - 1].hi = _qmax(ev, out[len(out) - 1].hi, items[i].hi)
        else:
            out.append(items[i].copy())
    return out^


def set_union(mut ev: Eventual, xs: List[Interval], ys: List[Interval]) raises -> List[Interval]:
    var all = xs.copy()
    all.extend(ys.copy())
    return normalize_set(ev, all)


def set_subset(mut ev: Eventual, xs: List[Interval], ys: List[Interval]) raises -> Bool:
    """Every interval of `xs` lies in one interval of normalized `ys`."""
    var n = normalize_set(ev, ys)
    for i in range(len(xs)):
        var inside = False
        for j in range(len(n)):
            if _le(ev, n[j].lo, xs[i].lo) and _le(ev, xs[i].hi, n[j].hi):
                inside = True
                break
        if not inside:
            return False
    return True


def set_key(xs: List[Interval]) -> String:
    var out = String("")
    for i in range(len(xs)):
        out += xs[i].key()
    return out^


def set_map(xs: List[Interval], c: Int, s: Int) -> List[Interval]:
    """The image of `j -> c + s j`."""
    var out = List[Interval]()
    for i in range(len(xs)):
        var a = qx_add(qx_const(c), qx_scale(xs[i].lo, q_int(s)))
        var b = qx_add(qx_const(c), qx_scale(xs[i].hi, q_int(s)))
        out.append(Interval(a, b) if s > 0 else Interval(b, a))
    return out^


def set_clamp(mut ev: Eventual, xs: List[Interval], lo: Int, hi: Int, below: Bool) raises -> List[Interval]:
    """The part of `xs` with `j <= hi` (`below`) or `j >= lo`: a half-line, unbounded in `q`."""
    var out = List[Interval]()
    for i in range(len(xs)):
        var x = xs[i].copy()
        var iv = Interval(x.lo, _qmin(ev, x.hi, qx_const(hi))) if below else Interval(_qmax(ev, x.lo, qx_const(lo)), x.hi)
        if _le(ev, iv.lo, iv.hi):
            out.append(iv^)
    return out^


def set_far(mut ev: Eventual, xs: List[Interval], j0: Int) raises -> List[Interval]:
    """The part of `xs` with `|j| > j0`."""
    return normalize_set(ev, set_clamp(ev, xs, 0, -j0 - 1, True) + set_clamp(ev, xs, j0 + 1, 0, False))


def _member_count(ms: List[List[Interval]]) -> Int:
    var n = 0
    for i in range(len(ms)):
        n += len(ms[i])
    return n


def set_has(mut ev: Eventual, xs: List[Interval], j: Int) raises -> Bool:
    for i in range(len(xs)):
        if _le(ev, xs[i].lo, qx_const(j)) and _le(ev, qx_const(j), xs[i].hi):
            return True
    return False


# ---------------------------------------------------------------------------
# States and edges.
# ---------------------------------------------------------------------------


def _key_at(top: Int, bottom: Int, w: List[QX], q: Int) -> String:
    var key = String(top) + "|" + String(bottom) + "|"
    for k in range(3):
        key += q_string(qx_at(w[k], q)) + ("," if k < 2 else "")
    return key^


struct PState(Copyable, Movable):
    var top: Int
    var bottom: Int
    var w0: List[QX]

    def __init__(out self, top: Int, bottom: Int, var w0: List[QX]):
        self.top = top
        self.bottom = bottom
        self.w0 = w0^

    def key(self) -> String:
        var out = String(self.top) + "|" + String(self.bottom)
        for i in range(3):
            out += "|" + qx_key(self.w0[i])
        return out^

    def is_zero(self) -> Bool:
        for i in range(3):
            if not qx_is_zero(self.w0[i]):
                return False
        return True


struct PEdge(Copyable, Movable):
    var src: Int
    var dst: Int
    var drift: Int  # j' = drift + s j
    var valid: List[Interval]  # the j of the source for which the child exists

    def __init__(out self, src: Int, dst: Int, drift: Int, var valid: List[Interval]):
        self.src = src
        self.dst = dst
        self.drift = drift
        self.valid = valid^


struct ProgressionVerdict(Copyable, Movable):
    var holds: Bool
    var q0: Int
    var states: Int
    var edges: Int
    var core: Int
    var members_key: String

    def __init__(out self):
        self.holds = False
        self.q0 = -1
        self.states = 0
        self.edges = 0
        self.core = 0
        self.members_key = String("")


struct ProgressionLine:
    var cl: SymbolicClosure
    var u: List[Int]
    var s: Int
    var k: Int
    var phi_index: Int
    var eps: TPoly  # <ell, u>, positive at beta
    var states: List[PState]
    var index: Dict[String, Int]
    var edges: List[PEdge]
    var real: List[List[Interval]]  # realness interval of each state's members
    var members: List[List[Interval]]
    var trace: Bool  # one diagnostic line per closure round

    def __init__(out self, var line: Line, u: List[Int], s: Int) raises:
        var ev = Eventual()
        var cert = certify_wedge_pisot(line, ev) if line.norm_mode() else certify_line(line, ev)
        if not cert.holds:
            raise Error("the line's PIP property was not certified")
        self.cl = SymbolicClosure(line^, cert.ell_sign, ev^)
        self.u = u.copy()
        self.s = s
        self.k = 0
        self.trace = False
        self.eps = TPoly()
        self.states = List[PState]()
        self.index = Dict[String, Int]()
        self.edges = List[PEdge]()
        self.real = List[List[Interval]]()
        self.members = List[List[Interval]]()
        self.phi_index = -1
        for i in range(3):
            if i != self.cl.line.y and (u[i] == 1 or u[i] == -1):
                self.phi_index = i
                break
        if self.phi_index < 0:
            raise Error("u has no unit coordinate off the run letter")
        # M u = s u + k e_y with k a positive constant (Lemma EP)
        var uq = self._uq()
        var r = w_sub(self.cl.line.mw(uq), self._scaled(uq, s))
        for i in range(3):
            if i != self.cl.line.y and not qx_is_zero(r[i]):
                raise Error("M u - s u is not a multiple of e_y")
        if not qx_is_const(r[self.cl.line.y]):
            raise Error("k is not constant on the line")
        var kq = qx_const_term(r[self.cl.line.y])
        self.k = small_int(kq)
        if self.k < 1:
            raise Error("k = -f(+-1) must be positive (Lemma P1)")
        self.eps = self.cl.line.t_of(uq)
        if self.cl.positive(self.eps) <= 0:
            raise Error("<ell, u> is not positive at beta")

    def _uq(self) -> List[QX]:
        var out = List[QX]()
        for i in range(3):
            out.append(qx_const(self.u[i]))
        return out^

    def _scaled(self, w: List[QX], c: Int) -> List[QX]:
        var out = List[QX]()
        for i in range(3):
            out.append(qx_scale(w[i], q_int(c)))
        return out^

    def state_keys_at(self, q: Int) -> Dict[String, Int]:
        """State index by `top|bottom|w0` with `w0` evaluated at `q`."""
        var out = Dict[String, Int]()
        for i in range(len(self.states)):
            out[_key_at(self.states[i].top, self.states[i].bottom, self.states[i].w0, q)] = i
        return out^

    def has_member_at(self, top: Int, bottom: Int, w: List[Int], q: Int, keys: Dict[String, Int]) raises -> Bool:
        """Whether the overlap `(top, bottom, w)` of the member at `q` is a member."""
        var j = w[self.phi_index] * self.u[self.phi_index]
        var w0 = List[QX]()
        for i in range(3):
            w0.append(qx_const(w[i] - j * self.u[i]))
        var key = _key_at(top, bottom, w0, q)
        if key not in keys:
            return False
        ref ms = self.members[keys[key]]
        for k in range(len(ms)):
            if qx_at(ms[k].lo, q).le(q_int(j)) and q_int(j).le(qx_at(ms[k].hi, q)):
                return True
        return False


    def phi(self, w: List[QX]) raises -> QX:
        return qx_scale(w[self.phi_index], q_int(self.u[self.phi_index]))

    def split(self, w: List[QX]) raises -> Tuple[List[QX], QX]:
        """`w = w0 + j u` with `phi(w0) = 0`."""
        var j = self.phi(w)
        var w0 = List[QX]()
        for i in range(3):
            w0.append(qx_sub(w[i], qx_scale(j, q_int(self.u[i]))))
        return (w0^, j^)

    def intern(mut self, a: Int, b: Int, var w0: List[QX]) raises -> Int:
        var st = PState(a, b, w0^)
        var key = st.key()
        if key in self.index:
            return self.index[key]
        if len(self.states) >= STATE_CAP:
            raise Error("progression closure exceeded its state cap")
        var i = len(self.states)
        self.index[key] = i
        self.real.append(self._realness(st))
        self.states.append(st^)
        self.members.append(List[Interval]())
        return i

    def _realness(mut self, st: PState) raises -> List[Interval]:
        """The `j` with `-ell_b < t(w0) + j eps < ell_a`."""
        var t = self.cl.line.t_of(st.w0)
        var ell = self.cl.line.ell.copy()
        var lo = self.cl.least_m(tp_add(ell[st.bottom], t), self.eps, True)
        var hi = qx_sub(self.cl.least_m(tp_sub(t, ell[st.top]), self.eps, False), qx_const(1))
        var out = List[Interval]()
        if _le(self.cl.ev, lo, hi):
            out.append(Interval(lo, hi))
        return out^

    def expand(mut self, i: Int) raises:
        """Every edge out of state `i`, with its validity interval."""
        var st = self.states[i].copy()
        var line_y = self.cl.line.y
        var ell = self.cl.line.ell.copy()
        var mw = self.cl.line.mw(st.w0)
        var tw0 = self.cl.line.t_of(st.w0)
        var ky = qx_const(self.k)
        for sa in range(3):
            if sa == 1 and not self.cl.has_run(st.top):
                continue
            for sb in range(3):
                if sb == 1 and not self.cl.has_run(st.bottom):
                    continue
                var b0 = w_sub(w_add(mw, self.cl.prefix(st.bottom, sb)), self.cl.prefix(st.top, sa))
                var a2 = self.cl.letter(st.top, sa)
                var b2 = self.cl.letter(st.bottom, sb)
                var phib = self.phi(b0)
                if not qx_is_const(phib):
                    raise Error("a drift phi(B0) is not constant on the line")
                var drift = small_int(qx_const_term(phib))
                var base0 = self.split(b0)[0].copy()
                var tb = self.cl.line.t_of(base0)
                if sa != 1 and sb != 1:
                    # child B0 + j (s u + k e_y): a bounded window of j, each its own state
                    var h1 = tp_add(tp_scale(self.eps, qx_const(self.s)), tp_scale(ell[line_y], ky))
                    var tb0 = self.cl.line.t_of(b0)
                    var jlo = self.cl.least_m(tp_add(ell[b2], tb0), h1, True)
                    var jhi = qx_sub(self.cl.least_m(tp_sub(tb0, ell[a2]), h1, False), qx_const(1))
                    var gap = qx_sub(jhi, jlo)
                    if not qx_is_const(gap):
                        raise Error("a non-run window of j grows with q")
                    var width = small_int(qx_const_term(gap))
                    for d in range(width + 1):
                        var jq = qx_add(jlo, qx_const(d))
                        var only = List[Interval]()
                        only.append(Interval(jq, jq))
                        var valid = set_intersect(self.cl.ev, only, self.real[i])
                        if len(valid) == 0:
                            continue
                        var w0c = w_add(base0, w_unit(line_y, qx_scale(jq, q_int(self.k))))
                        var dst = self.intern(a2, b2, w0c^)
                        self.edges.append(PEdge(i, dst, drift, valid^))
                    continue
                # run child: with m' = m + j k the child is base0 + m' e_y at index
                # j' = drift + s j, so t(child) = t(b0) + m' ell_y + s j eps.
                var ra = self.real[i].copy()
                if len(ra) == 0:
                    continue
                var tbd = self.cl.line.t_of(b0)
                # the parent t(w0) + j eps and the child pin m' to a bounded window:
                # s = +1: child - parent = t(b0) - t(w0) + m' ell_y in (-ell_b2 - ell_top, ell_a2 + ell_bottom)
                # s = -1: child + parent = t(b0) + t(w0) + m' ell_y in (-ell_b2 - ell_bottom, ell_a2 + ell_top)
                var pair = tp_sub(tbd, tw0) if self.s > 0 else tp_add(tbd, tw0)
                var below = ell[st.top if self.s > 0 else st.bottom].copy()
                var above = ell[st.bottom if self.s > 0 else st.top].copy()
                var mlo = self.cl.least_m(tp_add(tp_add(ell[b2], below), pair), ell[line_y], True)
                var mhi = qx_sub(self.cl.least_m(tp_sub(tp_sub(pair, ell[a2]), above), ell[line_y], False), qx_const(1))
                var mgap = qx_sub(mhi, mlo)
                if not qx_is_const(mgap):
                    raise Error("a run window of m' grows with q")
                var mwidth = small_int(qx_const_term(mgap))
                var rlo = qx_neg(qx_sub(self.cl.line.run[st.top], qx_const(1))) if sa == 1 else List[List[Q]]()
                var rhi = qx_sub(self.cl.line.run[st.bottom], qx_const(1)) if sb == 1 else List[List[Q]]()
                for d in range(mwidth + 1):
                    var mp = qx_add(mlo, qx_const(d))
                    var tm = tp_add(tb, tp_scale(ell[line_y], mp))
                    # realness of the child in its own index j': -ell_b2 < t(base0) + m' ell_y + j' eps < ell_a2
                    var child_iv = List[Interval]()
                    child_iv.append(Interval(
                        self.cl.least_m(tp_add(ell[b2], tm), self.eps, True),
                        qx_sub(self.cl.least_m(tp_sub(tm, ell[a2]), self.eps, False), qx_const(1)),
                    ))
                    # back to the parent's j = s (j' - drift)
                    var parent_iv = normalize_set(self.cl.ev, set_map(child_iv, -self.s * drift, self.s))
                    # run bounds: rlo <= m' - j k <= rhi, i.e. ceil((m' - rhi) / k) <= j <= floor((m' - rlo) / k)
                    var runs = List[Interval]()
                    runs.append(Interval(qx_div_round(qx_sub(mp, rhi), self.k, True), qx_div_round(qx_sub(mp, rlo), self.k, False)))
                    var valid = set_intersect(self.cl.ev, set_intersect(self.cl.ev, parent_iv, runs), ra)
                    if len(valid) == 0:
                        continue
                    var w0c = w_add(base0, w_unit(line_y, mp))
                    var dst = self.intern(a2, b2, w0c^)
                    self.edges.append(PEdge(i, dst, drift, valid^))

    def close(mut self) raises:
        """States and members closed under the edges, from the seeds.

        A state is expanded once it has a member, so only states reachable
        through valid edges are built; members are widened toward each
        realness interval after `WIDEN_AFTER` changes."""
        self.cl.seeds()
        for v in range(len(self.cl.vertices)):
            ref sv = self.cl.vertices[v]
            var parts = self.split(sv.w)
            var i = self.intern(sv.top, sv.bottom, parts[0].copy())
            var one = List[Interval]()
            one.append(Interval(parts[1], parts[1]))
            self.members[i] = set_union(self.cl.ev, self.members[i], one)
        var expanded = List[Bool]()
        var changes = List[Int]()
        for _ in range(FIXPOINT_CAP):
            var moved = False
            var i = 0
            while i < len(self.states):
                if len(expanded) <= i:
                    expanded.append(False)
                    changes.append(0)
                if not expanded[i] and len(self.members[i]) > 0:
                    self.expand(i)
                    expanded[i] = True
                    moved = True
                i += 1
            for e in range(len(self.edges)):
                var src = self.edges[e].src
                var dst = self.edges[e].dst
                var src_in = set_intersect(self.cl.ev, self.members[src], self.edges[e].valid)
                if len(src_in) == 0:
                    continue
                var img = set_map(src_in, self.edges[e].drift, self.s)
                var grown = set_union(self.cl.ev, self.members[dst], img)
                if set_key(grown) != set_key(self.members[dst]):
                    while len(changes) <= dst:
                        changes.append(0)
                        expanded.append(False)
                    changes[dst] += 1
                    if changes[dst] > WIDEN_AFTER:
                        grown = self._widen(dst, grown)
                    self.members[dst] = grown^
                    moved = True
            if self.trace:
                print("closure round: states", len(self.states), "edges", len(self.edges), "members", _member_count(self.members))
            if not moved:
                return
        raise Error("the closure did not settle")

    def _widen(mut self, i: Int, xs: List[Interval]) raises -> List[Interval]:
        """Push the hull to the state's realness interval."""
        if len(self.real[i]) == 0:
            raise Error("members outside the realness of their state")
        var hull = List[Interval]()
        hull.append(Interval(xs[0].lo, xs[len(xs) - 1].hi))
        var r = self.real[i][0].copy()
        var wide = List[Interval]()
        wide.append(Interval(_qmin(self.cl.ev, hull[0].lo, r.lo), _qmax(self.cl.ev, hull[0].hi, r.hi)))
        return set_intersect(self.cl.ev, wide, self.real[i])

    def steps(mut self) raises -> List[PEdge]:
        """Edges as translations `j -> j + drift`: the edges themselves for `s = +1`,
        and for `s = -1` every composite of two edges (`sigma^2`), valid on
        `{j in V1 : d1 - j in V2}` with drift `d2 - d1`."""
        if self.s > 0:
            return self.edges.copy()
        var out = List[PEdge]()
        for e1 in range(len(self.edges)):
            for e2 in range(len(self.edges)):
                if self.edges[e2].src != self.edges[e1].dst:
                    continue
                var d1 = self.edges[e1].drift
                var back = normalize_set(self.cl.ev, set_map(self.edges[e2].valid, d1, -1))
                var valid = set_intersect(self.cl.ev, self.edges[e1].valid, back)
                if len(valid) > 0:
                    out.append(PEdge(self.edges[e1].src, self.edges[e2].dst, self.edges[e2].drift - d1, valid^))
        return out^

    def ranked(mut self, steps: List[PEdge], j0: Int) raises -> List[List[Interval]]:
        """Members with `|j| > j0` that strictly lower `|j|` by a step, closed under
        drift-0 ties. A step of drift `d != 0` lowers `|j|` once `|j| > |d| / 2`."""
        var good = List[List[Interval]]()
        for _ in range(len(self.states)):
            good.append(List[Interval]())
        for e in range(len(steps)):
            var d = steps[e].drift
            if d == 0:
                continue
            if 2 * (j0 + 1) <= abs(d):
                raise Error("a step drift is too wide for the core")
            var region = set_clamp(self.cl.ev, steps[e].valid, j0 + 1, 0, False) if d < 0 else set_clamp(self.cl.ev, steps[e].valid, 0, -j0 - 1, True)
            good[steps[e].src] = set_union(self.cl.ev, good[steps[e].src], region)
        for _ in range(FIXPOINT_CAP):
            var moved = False
            for e in range(len(steps)):
                if steps[e].drift != 0:
                    continue
                var add = set_intersect(self.cl.ev, steps[e].valid, good[steps[e].dst])
                var grown = set_union(self.cl.ev, good[steps[e].src], add)
                if set_key(grown) != set_key(good[steps[e].src]):
                    good[steps[e].src] = grown^
                    moved = True
            if not moved:
                return good^
        raise Error("the ranking fixed point did not settle")

    def certify(mut self) raises -> ProgressionVerdict:
        self.close()
        var steps = self.steps()
        var dmax = 0
        for e in range(len(steps)):
            dmax = max(dmax, abs(steps[e].drift))
        var j0 = max(1, dmax // 2)  # least j0 >= 1 with 2 (j0 + 1) > dmax
        var good = self.ranked(steps, j0)
        for i in range(len(self.states)):
            var far = set_far(self.cl.ev, self.members[i], j0)
            if not set_subset(self.cl.ev, far, good[i]):
                raise Error("a member with |j| > j0 has no ranked descent: " + self.states[i].key())
        # core: members with |j| <= j0 must reach offset zero inside the core (single edges)
        var core_state = List[Int]()
        var core_j = List[Int]()
        var core_index = Dict[String, Int]()
        for i in range(len(self.states)):
            for j in range(-j0, j0 + 1):
                if set_has(self.cl.ev, self.members[i], j):
                    core_index[String(i) + "@" + String(j)] = len(core_state)
                    core_state.append(i)
                    core_j.append(j)
        var hit = List[Bool](length=len(core_state), fill=False)
        for c in range(len(core_state)):
            hit[c] = core_j[c] == 0 and self.states[core_state[c]].is_zero()
        for _ in range(len(core_state) + 1):
            var moved = False
            for e in range(len(self.edges)):
                ref ed = self.edges[e]
                for jj in range(-j0, j0 + 1):
                    var src_key = String(ed.src) + "@" + String(jj)
                    if src_key not in core_index or not set_has(self.cl.ev, ed.valid, jj):
                        continue
                    var j2 = ed.drift + self.s * jj
                    var dst_key = String(ed.dst) + "@" + String(j2)
                    if dst_key in core_index and hit[core_index[dst_key]] and not hit[core_index[src_key]]:
                        hit[core_index[src_key]] = True
                        moved = True
            if not moved:
                break
        for c in range(len(core_state)):
            if not hit[c]:
                raise Error("a core member does not reach offset zero inside the core")
        var out = ProgressionVerdict()
        out.holds = True
        var n = 0
        while not self.cl.ev.threshold.lt(q_int(n)):
            n += 1
        out.q0 = n
        out.states = len(self.states)
        out.edges = len(self.edges)
        out.core = len(core_state)
        var key = String("")
        for i in range(len(self.states)):
            key += self.states[i].key() + "=" + set_key(self.members[i]) + ";"
        out.members_key = key^
        return out^
