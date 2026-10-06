"""Parametric witness paths: one exact check that proves a shared tile on a
whole cone of substitutions.

A *cone family* is a three-letter substitution whose images are sequences of
segments -- a single letter, or a run of the letter `y = 2` whose length is an
affine form in cone variables `n_1, ..., n_m >= 0`. The incidence matrix `M`
then has affine entries.

A *witness path* from the pair `(a_0, b_0)` is a sequence of steps; step `l`
picks a position in `sigma(a_l)` and one in `sigma(b_l)`, each a segment and
an affine offset inside it, and moves to the letters there with Parikh offset

    gamma_(l+1) = M gamma_l + pi(sigma(a_l)[:i_l]) - pi(sigma(b_l)[:k_l]).

If every `gamma_l` is a *constant* vector, every condition of the path -- an
offset lies inside its run, `gamma_(l+1)` is the constant the path says -- is
an affine identity or an affine inequality in the `n_k`, and an affine form is
nonnegative on all of `Z_{>=0}^m` iff its constant and its coefficients are
(sufficiency is all that is used). A path ending at `(a, a, 0)` after `n`
steps is then a shared tile of `sigma^n(a_0)` and `sigma^n(b_0)` for **every**
member of the cone at once: unrolling the recursion, `gamma_n` is the
difference of the Parikh vectors of the two prefixes in front of the two
positions, and the letters there are equal.

`search_witness` finds a path by breadth-first search over the finitely many
states `(a, b, gamma)` with `|gamma_i| <= bound`; `verify_witness` re-derives
every state from the step data alone and checks every condition. The search
is a means of finding a certificate; the verification is the certificate.
A failed search is reported as such and is never a verdict about the cone.
"""

comptime Y_LETTER = 2


def aff_const(m: Int, c: Int) -> List[Int]:
    var out = List[Int](length=m + 1, fill=0)
    out[0] = c
    return out^


def aff_add(a: List[Int], b: List[Int]) -> List[Int]:
    var out = List[Int]()
    for k in range(len(a)):
        out.append(a[k] + b[k])
    return out^


def aff_sub(a: List[Int], b: List[Int]) -> List[Int]:
    var out = List[Int]()
    for k in range(len(a)):
        out.append(a[k] - b[k])
    return out^


def aff_scale(a: List[Int], s: Int) -> List[Int]:
    var out = List[Int]()
    for k in range(len(a)):
        out.append(s * a[k])
    return out^


def aff_is_const(a: List[Int]) -> Bool:
    for k in range(1, len(a)):
        if a[k] != 0:
            return False
    return True


def aff_nonneg(a: List[Int]) -> Bool:
    """Sufficient for `a(n) >= 0` on all of `Z_{>=0}^m`."""
    for k in range(len(a)):
        if a[k] < 0:
            return False
    return True


def aff_eval(a: List[Int], ns: List[Int]) -> Int:
    var v = a[0]
    for k in range(len(ns)):
        v += a[k + 1] * ns[k]
    return v


struct Segment(Copyable, Movable):
    """A single `letter`, or (`run`) a run of `y` of affine `length`."""

    var run: Bool
    var letter: Int
    var length: List[Int]

    def __init__(out self, run: Bool, letter: Int, var length: List[Int]):
        self.run = run
        self.letter = letter
        self.length = length^


def letter_segment(m: Int, letter: Int) -> Segment:
    return Segment(False, letter, aff_const(m, 1))


def run_segment(var length: List[Int]) -> Segment:
    return Segment(True, Y_LETTER, length^)


struct ConeFamily(Copyable, Movable):
    var m: Int
    var images: List[List[Segment]]
    var incidence: List[List[Int]]  # entry 3 i + j: count of letter i in sigma(j)

    def __init__(out self, m: Int, var images: List[List[Segment]]) raises:
        if len(images) != 3:
            raise Error("a cone family has three images")
        self.m = m
        self.images = images^
        self.incidence = List[List[Int]]()
        for _ in range(9):
            self.incidence.append(aff_const(m, 0))
        for j in range(3):
            for s in range(len(self.images[j])):
                ref seg = self.images[j][s]
                if len(seg.length) != m + 1:
                    raise Error("a segment length has the wrong number of cone variables")
                if seg.run:
                    self.incidence[3 * Y_LETTER + j] = aff_add(self.incidence[3 * Y_LETTER + j], seg.length)
                else:
                    self.incidence[3 * seg.letter + j] = aff_add(self.incidence[3 * seg.letter + j], aff_const(m, 1))

    def m_times(self, gamma: List[Int]) -> List[List[Int]]:
        """`M gamma` for a constant `gamma`, as three affine forms."""
        var out = List[List[Int]]()
        for i in range(3):
            var acc = aff_const(self.m, 0)
            for j in range(3):
                acc = aff_add(acc, aff_scale(self.incidence[3 * i + j], gamma[j]))
            out.append(acc^)
        return out^

    def prefix_before(self, a: Int, s: Int) -> List[List[Int]]:
        """Parikh vector of the segments of `sigma(a)` before segment `s`."""
        var pre = List[List[Int]]()
        for _ in range(3):
            pre.append(aff_const(self.m, 0))
        for k in range(s):
            ref seg = self.images[a][k]
            if seg.run:
                pre[Y_LETTER] = aff_add(pre[Y_LETTER], seg.length)
            else:
                pre[seg.letter] = aff_add(pre[seg.letter], aff_const(self.m, 1))
        return pre^

    def start_of(self, a: Int, s: Int) -> List[Int]:
        """Index of the first letter of segment `s` in `sigma(a)`."""
        var st = aff_const(self.m, 0)
        for k in range(s):
            st = aff_add(st, self.images[a][k].length)
        return st^

    def instantiate(self, ns: List[Int]) raises -> List[List[Int]]:
        """The member of the cone at `ns`, as a plain substitution."""
        if len(ns) != self.m:
            raise Error("wrong number of cone coordinates")
        var sigma = List[List[Int]]()
        for a in range(3):
            var img = List[Int]()
            for s in range(len(self.images[a])):
                ref seg = self.images[a][s]
                if seg.run:
                    var n = aff_eval(seg.length, ns)
                    if n < 0:
                        raise Error("a run length is negative at this cone point")
                    for _ in range(n):
                        img.append(Y_LETTER)
                else:
                    img.append(seg.letter)
            sigma.append(img^)
        return sigma^


struct WitnessStep(Copyable, Movable):
    """Segment and affine offset inside it, on each side."""

    var seg_a: Int
    var off_a: List[Int]
    var seg_b: Int
    var off_b: List[Int]

    def __init__(out self, seg_a: Int, var off_a: List[Int], seg_b: Int, var off_b: List[Int]):
        self.seg_a = seg_a
        self.off_a = off_a^
        self.seg_b = seg_b
        self.off_b = off_b^


struct WitnessSearch(Copyable, Movable):
    var found: Bool
    var steps: List[WitnessStep]

    def __init__(out self):
        self.found = False
        self.steps = List[WitnessStep]()


def _offset_ok(fam: ConeFamily, a: Int, s: Int, off: List[Int]) -> Bool:
    ref seg = fam.images[a][s]
    if not seg.run:
        for k in range(len(off)):
            if off[k] != 0:
                return False
        return True
    # 0 <= off <= length - 1
    return aff_nonneg(off) and aff_nonneg(aff_sub(aff_sub(seg.length, off), aff_const(fam.m, 1)))


struct StepResult(Copyable, Movable):
    """The state a step leads to; `ok` is false if any condition failed, and
    `why` then says which."""

    var ok: Bool
    var why: String
    var a: Int
    var b: Int
    var gamma: List[Int]

    def __init__(out self, ok: Bool, why: String, a: Int, b: Int, var gamma: List[Int]):
        self.ok = ok
        self.why = why
        self.a = a
        self.b = b
        self.gamma = gamma^


def _refused(why: String) -> StepResult:
    return StepResult(False, why, -1, -1, List[Int]([0, 0, 0]))


def apply_step(fam: ConeFamily, a: Int, b: Int, gamma: List[Int], step: WitnessStep) -> StepResult:
    """The state a step leads to, with every condition of the step checked on
    the whole cone. Used by both the search and the verifier."""
    if step.seg_a < 0 or step.seg_a >= len(fam.images[a]) or step.seg_b < 0 or step.seg_b >= len(fam.images[b]):
        return _refused("a witness step names a segment that does not exist")
    if not _offset_ok(fam, a, step.seg_a, step.off_a) or not _offset_ok(fam, b, step.seg_b, step.off_b):
        return _refused("a witness offset is not provably inside its segment")
    var mg = fam.m_times(gamma)
    var pa = fam.prefix_before(a, step.seg_a)
    var pb = fam.prefix_before(b, step.seg_b)
    var g2 = List[Int]()
    for i in range(3):
        var d = aff_sub(aff_add(mg[i], pa[i]), pb[i])
        if i == Y_LETTER:
            if fam.images[a][step.seg_a].run:
                d = aff_add(d, step.off_a)
            if fam.images[b][step.seg_b].run:
                d = aff_sub(d, step.off_b)
        if not aff_is_const(d):
            return _refused("a witness Parikh offset is not constant on the cone")
        g2.append(d[0])
    return StepResult(True, "", fam.images[a][step.seg_a].letter, fam.images[b][step.seg_b].letter, g2^)


def _key(a: Int, b: Int, gamma: List[Int], bound: Int) -> Int:
    var w = 2 * bound + 1
    return (((a * 3 + b) * w + gamma[0] + bound) * w + gamma[1] + bound) * w + gamma[2] + bound


def _in_box(gamma: List[Int], bound: Int) -> Bool:
    for i in range(3):
        if gamma[i] < -bound or gamma[i] > bound:
            return False
    return True


def _candidates(fam: ConeFamily, a: Int, b: Int, gamma: List[Int], bound: Int) -> List[WitnessStep]:
    """Every step whose target offset is constant with entries in the box. With
    both positions in runs, one offset is pinned to 0, 1 or 2."""
    var out = List[WitnessStep]()
    var m = fam.m
    var mg = fam.m_times(gamma)
    for sa in range(len(fam.images[a])):
        var pa = fam.prefix_before(a, sa)
        var ra = fam.images[a][sa].run
        for sb in range(len(fam.images[b])):
            var pb = fam.prefix_before(b, sb)
            var rb = fam.images[b][sb].run
            var dx = aff_sub(aff_add(mg[0], pa[0]), pb[0])
            var dc = aff_sub(aff_add(mg[1], pa[1]), pb[1])
            if not aff_is_const(dx) or not aff_is_const(dc):
                continue
            var dy = aff_sub(aff_add(mg[2], pa[2]), pb[2])
            for ty in range(-bound, bound + 1):
                var d = aff_sub(aff_const(m, ty), dy)  # off_a - off_b must equal d
                if not ra and not rb:
                    if d == aff_const(m, 0):
                        out.append(WitnessStep(sa, aff_const(m, 0), sb, aff_const(m, 0)))
                elif ra and not rb:
                    out.append(WitnessStep(sa, d.copy(), sb, aff_const(m, 0)))
                elif not ra and rb:
                    out.append(WitnessStep(sa, aff_const(m, 0), sb, aff_scale(d, -1)))
                else:
                    for s in range(3):
                        out.append(WitnessStep(sa, aff_add(d, aff_const(m, s)), sb, aff_const(m, s)))
                        out.append(WitnessStep(sa, aff_const(m, s), sb, aff_sub(aff_const(m, s), d)))
    return out^


def search_witness(fam: ConeFamily, a0: Int, b0: Int, bound: Int, max_level: Int) -> WitnessSearch:
    """Breadth-first search for a constant-offset witness path from `(a0, b0, 0)`
    to some `(a, a, 0)`, of length at most `max_level`."""
    var w = 2 * bound + 1
    var size = 9 * w * w * w
    var seen = List[Bool](length=size, fill=False)
    var parent = List[Int](length=size, fill=-1)
    var via = List[WitnessStep]()
    var via_of = List[Int](length=size, fill=-1)
    var fa = List[Int]()
    var fb = List[Int]()
    var fg = List[List[Int]]()
    var zero = List[Int]([0, 0, 0])
    var k0 = _key(a0, b0, zero, bound)
    seen[k0] = True
    fa.append(a0)
    fb.append(b0)
    fg.append(zero.copy())
    var out = WitnessSearch()
    for _ in range(max_level):
        var na = List[Int]()
        var nb = List[Int]()
        var ng = List[List[Int]]()
        for f in range(len(fa)):
            var kf = _key(fa[f], fb[f], fg[f], bound)
            var cands = _candidates(fam, fa[f], fb[f], fg[f], bound)
            for c in range(len(cands)):
                var child = apply_step(fam, fa[f], fb[f], fg[f], cands[c])
                if not child.ok or not _in_box(child.gamma, bound):
                    continue
                var kc = _key(child.a, child.b, child.gamma, bound)
                if seen[kc]:
                    continue
                seen[kc] = True
                parent[kc] = kf
                via_of[kc] = len(via)
                via.append(cands[c].copy())
                if child.a == child.b and child.gamma == zero:
                    var rev = List[WitnessStep]()
                    var cur = kc
                    while cur != k0:
                        rev.append(via[via_of[cur]].copy())
                        cur = parent[cur]
                    for i in range(len(rev) - 1, -1, -1):
                        out.steps.append(rev[i].copy())
                    out.found = True
                    return out^
                na.append(child.a)
                nb.append(child.b)
                ng.append(child.gamma.copy())
        fa = na^
        fb = nb^
        fg = ng^
    return out^


def verify_witness(fam: ConeFamily, a0: Int, b0: Int, steps: List[WitnessStep]) -> Bool:
    """Re-derive every state from the steps alone; true iff every condition
    holds on the whole cone and the path ends at `(a, a, 0)`."""
    if len(steps) == 0:
        return False
    var a = a0
    var b = b0
    var gamma = List[Int]([0, 0, 0])
    for l in range(len(steps)):
        var child = apply_step(fam, a, b, gamma, steps[l])
        if not child.ok:
            return False
        a = child.a
        b = child.b
        gamma = child.gamma.copy()
    return a == b and gamma == List[Int]([0, 0, 0])


def witness_position(fam: ConeFamily, a0: Int, b0: Int, steps: List[WitnessStep], ns: List[Int]) raises -> Int:
    """The position of the shared tile in `sigma^n(a0)` at the cone point `ns`,
    for an independent check against the words themselves."""
    var sigma = fam.instantiate(ns)
    var a = a0
    var pos = 0
    var word = List[Int]([a0])
    for l in range(len(steps)):
        # position at level l + 1: length of sigma(word[:pos]) plus the offset
        var p2 = 0
        for k in range(pos):
            p2 += len(sigma[word[k]])
        var st = aff_eval(fam.start_of(a, steps[l].seg_a), ns)
        var off = aff_eval(steps[l].off_a, ns) if fam.images[a][steps[l].seg_a].run else 0
        p2 += st + off
        var nxt = List[Int]()
        for k in range(len(word)):
            for c in range(len(sigma[word[k]])):
                nxt.append(sigma[word[k]][c])
        word = nxt^
        pos = p2
        a = word[pos]
    return pos
