"""Theorem K's open family: two witness lemmas, a census, and a pattern tree.

docs/p1a-a1-prime-2026-10-05.md §3f. Theorem K leaves one family of the
catch-up-free `|det M| = 2` class, with one odd letter `o`:

    sigma(o) = y,   sigma(y) = o w_1 o,   sigma(z) = o w_2 o,   w_1, w_2 ∈ {y, z}*,

where all-pairs strong coincidence is equivalent to `{o, y}` being eventually
coincident. `det M = 2 (Z_1 - Z_2)`, with `Z_i` the number of `z` in `w_i`, so
membership forces `|Z_1 - Z_2| = 1`; primitivity forces `Z_1 >= 1`.

**The certificate part** (`named_path`, `family_census`). Lemma Φ1 (`w_1`
begins with `y`) and Lemma Φ2 (`w_1` begins with `z` and the Parikh walks of
`w_1` and `w_2 + e_y` cross) each name an explicit witness path from the words;
the census checks every named path with `verify_witness` on the concrete
substitution and against the words themselves, and decides every remaining
-- non-crossing -- member exactly with `coincidence_level`, raising on a
negative. The lemmas are proved in the note; the census is an exact finite
check on a stated domain, not a proof beyond it.

**The exploratory part** (`cover_family`). A partition tree of word patterns
-- a letter `z`, a maximal run `y^(c + n)`, a run of exactly `c` letters `y`,
or an opaque tail known only by its Parikh vector -- refined atom by atom and
then by relational splits `n_i > n_j | n_i = n_j | n_i < n_j` of the cone
variables. A node closes when a parametric witness path (`psc.cone_witness`)
certifies it, when no member can lie in it, when Lemma P1 cuts it, or when it
is one substitution decided exactly. Every certified leaf is a proof on its
whole region; a node still open at the depth limit is reported as open and
never counted as covered. The tree does **not** converge as it stands (the
open leaves grow with the depth), so it is an instrument, not a cover.

Usage: `mojo run -I . odd_letter_family_certificate.mojo [max_len] [tree_depth]`,
or `pixi run odd-letter-family-certificate`.
"""

from std.sys import argv
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.coincidence_formula import coincidence_level
from psc.cone_witness import (
    ConeFamily,
    Segment,
    WitnessStep,
    aff_const,
    letter_segment,
    opaque_segment,
    run_of,
    search_witness,
    verify_witness,
    witness_position,
)
from psc.cone_witness import aff_nonneg
from psc.pisot import CubicScreen
from a1_normal_form_census import f_at, shared_tile_between

comptime O = 0
comptime Y = 1
comptime Z = 2

comptime A_Z = 0  # the letter z
comptime A_RUN = 1  # a maximal run y^(c + n), n a fresh cone variable
comptime A_FIX = 2  # a maximal run of exactly c letters y
comptime A_TAIL = 3  # any word; opaque

comptime OFFSET_BOUND = 3
comptime MAX_LEVEL = 6
comptime RUN_CAP = 3  # runs are split until their minimum length reaches this
comptime DEFAULT_DEPTH = 14
comptime DEFAULT_SPLITS = 4

comptime LEAF_CERTIFIED = 0
comptime LEAF_EMPTY = 1
comptime LEAF_DECIDED = 2
comptime LEAF_NOT_MEMBER = 3
comptime LEAF_FAILED = 4
comptime LEAF_CUT = 5


struct Pattern(Copyable, Movable, Writable):
    """Atoms of a word pattern, with the run length `c` of each run atom."""

    var atoms: List[Int]
    var mins: List[Int]

    def __init__(out self, var atoms: List[Int], var mins: List[Int]):
        self.atoms = atoms^
        self.mins = mins^

    def is_open(self) -> Bool:
        return len(self.atoms) > 0 and self.atoms[len(self.atoms) - 1] == A_TAIL

    def zeds(self) -> Int:
        var n = 0
        for k in range(len(self.atoms)):
            if self.atoms[k] == A_Z:
                n += 1
        return n

    def variables(self) -> Int:
        var n = 0
        for k in range(len(self.atoms)):
            if self.atoms[k] == A_RUN:
                n += 1
            elif self.atoms[k] == A_TAIL:
                n += 2
        return n

    def write_to[W: Writer](self, mut w: W):
        if len(self.atoms) == 0:
            w.write("ε")
        for k in range(len(self.atoms)):
            var a = self.atoms[k]
            if a == A_Z:
                w.write("z")
            elif a == A_RUN:
                w.write("y^(", self.mins[k], "+)")
            elif a == A_FIX:
                if self.mins[k] == 1:
                    w.write("y")
                else:
                    w.write("y^", self.mins[k])
            else:
                w.write("*")


def any_word() -> Pattern:
    return Pattern(List[Int]([A_TAIL]), List[Int]([0]))


def _replace(p: Pattern, k: Int, atoms: List[Int], mins: List[Int]) -> Pattern:
    """`p` with atom `k` replaced by the given atoms."""
    var na = List[Int]()
    var nm = List[Int]()
    for i in range(len(p.atoms)):
        if i == k:
            for j in range(len(atoms)):
                na.append(atoms[j])
                nm.append(mins[j])
        else:
            na.append(p.atoms[i])
            nm.append(p.mins[i])
    return Pattern(na^, nm^)


def refinements(p: Pattern, k: Int, z_free: Bool) -> List[Pattern]:
    """The partition of atom `k`. With `z_free` false the tail may hold no
    more `z`, so only its two `z`-free parts are kept."""
    var out = List[Pattern]()
    if p.atoms[k] == A_TAIL:
        out.append(_replace(p, k, List[Int](), List[Int]()))
        out.append(_replace(p, k, List[Int]([A_RUN]), List[Int]([1])))
        if z_free:
            out.append(_replace(p, k, List[Int]([A_Z, A_TAIL]), List[Int]([0, 0])))
            out.append(_replace(p, k, List[Int]([A_RUN, A_Z, A_TAIL]), List[Int]([1, 0, 0])))
    elif p.atoms[k] == A_RUN:
        var c = p.mins[k]
        out.append(_replace(p, k, List[Int]([A_FIX]), List[Int]([c])))
        out.append(_replace(p, k, List[Int]([A_RUN]), List[Int]([c + 1])))
    return out^


def _segments(p: Pattern, m: Int, subst: List[List[Int]], mut slot: Int) -> List[Segment]:
    """`o w o` for the pattern `w`. Its variable slots, from `slot` on, read
    their affine forms over the `m` free variables from `subst`: one slot
    per run (the run is `y^(c + form)`), two per tail (its `y`- and
    `z`-counts)."""
    var segs = List[Segment]()
    segs.append(letter_segment(m, O))
    for k in range(len(p.atoms)):
        var a = p.atoms[k]
        if a == A_Z:
            segs.append(letter_segment(m, Z))
        elif a == A_FIX:
            segs.append(run_of(Y, aff_const(m, p.mins[k])))
        elif a == A_RUN:
            var len_form = subst[slot].copy()
            len_form[0] += p.mins[k]
            slot += 1
            segs.append(run_of(Y, len_form^))
        else:
            var par = List[List[Int]]()
            par.append(aff_const(m, 0))
            par.append(subst[slot].copy())
            par.append(subst[slot + 1].copy())
            slot += 2
            segs.append(opaque_segment(par^))
    segs.append(letter_segment(m, O))
    return segs^


def identity_subst(m: Int) -> List[List[Int]]:
    var out = List[List[Int]]()
    for k in range(m):
        var f = aff_const(m, 0)
        f[k + 1] = 1
        out.append(f^)
    return out^


def family_of(p1: Pattern, p2: Pattern, subst: List[List[Int]]) raises -> ConeFamily:
    var m = len(subst)
    var images = List[List[Segment]]()
    var img_o = List[Segment]()
    img_o.append(letter_segment(m, Y))
    images.append(img_o^)
    var slot = 0
    images.append(_segments(p1, m, subst, slot))
    images.append(_segments(p2, m, subst, slot))
    return ConeFamily(m, images^)


def member_sigma(w1: List[Int], w2: List[Int]) -> List[List[Int]]:
    var s = List[List[Int]]()
    s.append(List[Int]([Y]))
    var iy = List[Int]([O])
    for k in range(len(w1)):
        iy.append(w1[k])
    iy.append(O)
    var iz = List[Int]([O])
    for k in range(len(w2)):
        iz.append(w2[k])
    iz.append(O)
    s.append(iy^)
    s.append(iz^)
    return s^


def matches(p: Pattern, w: List[Int]) -> Bool:
    """Does the word `w` belong to the pattern? Runs are maximal, so the match
    is greedy and unique."""
    var i = 0
    for k in range(len(p.atoms)):
        var a = p.atoms[k]
        if a == A_TAIL:
            return True
        if a == A_Z:
            if i >= len(w) or w[i] != Z:
                return False
            i += 1
            continue
        var run = 0
        while i < len(w) and w[i] == Y:
            run += 1
            i += 1
        if a == A_FIX and run != p.mins[k]:
            return False
        if a == A_RUN and run < p.mins[k]:
            return False
    return i == len(w)


def _f_value(fam: ConeFamily, ns: List[Int], t: Int) raises -> Int:
    return f_at(Mat3(substitution_incidence(fam.instantiate(ns))), t)


def pisot_cut(fam: ConeFamily) raises -> Int:
    """`t` in `{1, -1}` if `f(t) = det(tI - M)` is affine on the node with all
    coefficients nonnegative, so that Lemma P1 (`f(1) < 0`, `f(-1) < 0` for a
    PIP member) leaves no member; 0 otherwise. Affinity is checked at the
    base, the unit points, every sum of two unit points and every doubled one
    -- enough for a polynomial of degree at most two in each pair of
    variables, which `f` is, the variables sitting in two rows of `M`."""
    var m = fam.m
    for t in [1, -1]:
        var zero = List[Int](length=m, fill=0)
        var f0 = _f_value(fam, zero, t)
        var form = List[Int]([f0])
        for k in range(m):
            var e = zero.copy()
            e[k] = 1
            form.append(_f_value(fam, e, t) - f0)
        var affine = True
        for j in range(m):
            for k in range(j, m):
                var e = zero.copy()
                e[j] += 1
                e[k] += 1
                if _f_value(fam, e, t) != f0 + form[j + 1] + form[k + 1]:
                    affine = False
        if affine and aff_nonneg(form):
            return t
    return 0


struct Node(Copyable, Movable, Writable):
    """A region of the family: two patterns, the affine forms of their variable
    slots over the free variables, and the free-variable pairs already split
    relationally."""

    var p1: Pattern
    var p2: Pattern
    var subst: List[List[Int]]
    var compared: List[Int]
    var depth: Int

    def __init__(out self, var p1: Pattern, var p2: Pattern, var subst: List[List[Int]], var compared: List[Int], depth: Int):
        self.p1 = p1^
        self.p2 = p2^
        self.subst = subst^
        self.compared = compared^
        self.depth = depth

    def write_to[W: Writer](self, mut w: W):
        w.write("w1 = ", self.p1, "  w2 = ", self.p2)
        if len(self.compared) > 0:
            w.write("  slots")
            for k in range(len(self.subst)):
                w.write(" ", _form(self.subst[k]))


def _form(f: List[Int]) -> String:
    var out = String(f[0])
    for k in range(1, len(f)):
        if f[k] != 0:
            out += ("+" if f[k] > 0 else "") + String(f[k]) + "n" + String(k)
    return out


struct Leaf(Copyable, Movable):
    var kind: Int
    var node: Node
    var level: Int
    var steps: List[WitnessStep]

    def __init__(out self, kind: Int, var node: Node, level: Int, var steps: List[WitnessStep]):
        self.kind = kind
        self.node = node^
        self.level = level
        self.steps = steps^


struct FamilyCover(Copyable, Movable):
    var leaves: List[Leaf]
    var nodes: Int
    var certified: Int
    var empty: Int
    var decided: Int
    var not_member: Int
    var cut: Int
    var failed: Int

    def __init__(out self):
        self.leaves = List[Leaf]()
        self.nodes = 0
        self.certified = 0
        self.empty = 0
        self.decided = 0
        self.not_member = 0
        self.cut = 0
        self.failed = 0


def _no_member(p1: Pattern, p2: Pattern) -> Bool:
    """No member of the family lies in the node: `w_1` complete without `z`,
    or the revealed `z`-counts already force `|Z_1 - Z_2| != 1`."""
    var z1 = p1.zeds()
    var z2 = p2.zeds()
    if not p1.is_open() and z1 == 0:
        return True
    if not p1.is_open() and not p2.is_open():
        return abs(z1 - z2) != 1
    if not p1.is_open():
        return z2 > z1 + 1
    if not p2.is_open():
        return z1 > z2 + 1
    return False


def _z_free(p: Pattern, other: Pattern) -> Bool:
    """May the tail of `p` still hold a `z`? Not if `other` is complete and
    `p` already has `Z_other + 1` of them."""
    if other.is_open():
        return True
    return p.zeds() < other.zeds() + 1


def _pick(p1: Pattern, p2: Pattern) -> List[Int]:
    """The earliest refinable atom, `w_1` first on ties: `[word, index]`, or
    `[-1, -1]` if none."""
    var longest = max(len(p1.atoms), len(p2.atoms))
    for k in range(longest):
        for wi in range(2):
            ref p = p1 if wi == 0 else p2
            if k >= len(p.atoms):
                continue
            if p.atoms[k] == A_TAIL or (p.atoms[k] == A_RUN and p.mins[k] < RUN_CAP):
                return List[Int]([wi, k])
    return List[Int]([-1, -1])


def _live(subst: List[List[Int]], k: Int) -> Bool:
    for i in range(len(subst)):
        if subst[i][k + 1] != 0:
            return True
    return False


def _split(subst: List[List[Int]], i: Int, j: Int, which: Int) -> List[List[Int]]:
    """Substitute `n_i <- n_j + 1 + n_i` (case 0), `n_i <- n_j` (case 1) or
    `n_j <- n_i + 1 + n_j` (case 2) in every form: a partition of `(n_i, n_j)`
    into `n_i > n_j`, `n_i = n_j`, `n_i < n_j`."""
    var out = List[List[Int]]()
    for k in range(len(subst)):
        var f = subst[k].copy()
        if which == 0:
            f[0] += f[i + 1]
            f[j + 1] += f[i + 1]
        elif which == 1:
            f[j + 1] += f[i + 1]
            f[i + 1] = 0
        else:
            f[0] += f[j + 1]
            f[i + 1] += f[j + 1]
        out.append(f^)
    return out^


def _next_pair(node: Node) -> List[Int]:
    """The first pair of live free variables not yet split, or `[-1, -1]`."""
    var m = len(node.subst)
    for i in range(m):
        if not _live(node.subst, i):
            continue
        for j in range(i + 1, m):
            if not _live(node.subst, j):
                continue
            var code = i * 1000 + j
            var seen = False
            for c in range(len(node.compared)):
                if node.compared[c] == code:
                    seen = True
            if not seen:
                return List[Int]([i, j])
    return List[Int]([-1, -1])


def cover_family(depth_limit: Int, split_limit: Int) raises -> FamilyCover:
    """The partition tree. Atoms are refined first, up to `depth_limit`; a
    node whose patterns are fully refined (no tail, every run at `RUN_CAP`)
    is then split relationally, up to `split_limit` splits."""
    var out = FamilyCover()
    var screen = CubicScreen()
    var stack = List[Node]()
    stack.append(Node(any_word(), any_word(), identity_subst(4), List[Int](), 0))
    while len(stack) > 0:
        var node = stack.pop()
        out.nodes += 1
        if _no_member(node.p1, node.p2):
            out.leaves.append(Leaf(LEAF_EMPTY, node^, 0, List[WitnessStep]()))
            out.empty += 1
            continue
        var fam = family_of(node.p1, node.p2, node.subst)
        var cut = pisot_cut(fam)
        if cut != 0:
            out.leaves.append(Leaf(LEAF_CUT, node^, cut, List[WitnessStep]()))
            out.cut += 1
            continue
        var w = search_witness(fam, O, Y, OFFSET_BOUND, MAX_LEVEL, True)
        if w.found:
            if not verify_witness(fam, O, Y, w.steps):
                raise Error("a witness path the search found does not verify")
            out.leaves.append(Leaf(LEAF_CERTIFIED, node^, len(w.steps), w.steps.copy()))
            out.certified += 1
            continue
        var any_live = False
        for k in range(len(node.subst)):
            if _live(node.subst, k):
                any_live = True
        if not any_live:
            var sigma = fam.instantiate(List[Int](length=fam.m, fill=0))
            var mat = Mat3(substitution_incidence(sigma))
            if abs(mat.det()) != 2 or not screen.is_pip(mat):
                out.leaves.append(Leaf(LEAF_NOT_MEMBER, node^, 0, List[WitnessStep]()))
                out.not_member += 1
                continue
            var lev = coincidence_level(sigma, O, Y)
            if lev < 0:
                raise Error("SC REFUTED in Theorem K's family: {o, y} is not eventually coincident")
            out.leaves.append(Leaf(LEAF_DECIDED, node^, lev, List[WitnessStep]()))
            out.decided += 1
            continue
        var pick = _pick(node.p1, node.p2)
        if pick[0] >= 0:
            if node.depth >= depth_limit:
                out.leaves.append(Leaf(LEAF_FAILED, node^, 0, List[WitnessStep]()))
                out.failed += 1
                continue
            var kids = refinements(node.p1, pick[1], _z_free(node.p1, node.p2)) if pick[0] == 0 else refinements(node.p2, pick[1], _z_free(node.p2, node.p1))
            for c in range(len(kids)):
                var q1 = kids[c].copy() if pick[0] == 0 else node.p1.copy()
                var q2 = node.p2.copy() if pick[0] == 0 else kids[c].copy()
                var m = q1.variables() + q2.variables()
                stack.append(Node(q1^, q2^, identity_subst(m), List[Int](), node.depth + 1))
            continue
        var pair = _next_pair(node)
        if pair[0] < 0 or len(node.compared) >= split_limit:
            out.leaves.append(Leaf(LEAF_FAILED, node^, 0, List[WitnessStep]()))
            out.failed += 1
            continue
        for which in range(3):
            var comp = node.compared.copy()
            comp.append(pair[0] * 1000 + pair[1])
            stack.append(Node(node.p1.copy(), node.p2.copy(), _split(node.subst, pair[0], pair[1], which), comp^, node.depth))
    return out^


def slot_values(p: Pattern, w: List[Int]) -> List[Int]:
    """For a word the pattern matches, the values its variable slots take:
    `len - c` for each run, the `y`- and `z`-counts of the tail."""
    var out = List[Int]()
    var i = 0
    for k in range(len(p.atoms)):
        var a = p.atoms[k]
        if a == A_Z:
            i += 1
        elif a == A_TAIL:
            var ny = 0
            var nz = 0
            while i < len(w):
                if w[i] == Y:
                    ny += 1
                else:
                    nz += 1
                i += 1
            out.append(ny)
            out.append(nz)
        else:
            var run = 0
            while i < len(w) and w[i] == Y:
                run += 1
                i += 1
            if a == A_RUN:
                out.append(run - p.mins[k])
    return out^


def _reachable(subst: List[List[Int]], want: List[Int], k: Int, mut ns: List[Int], bound: Int) -> Bool:
    if k == len(ns):
        for s in range(len(subst)):
            var v = subst[s][0]
            for j in range(len(ns)):
                v += subst[s][j + 1] * ns[j]
            if v != want[s]:
                return False
        return True
    for x in range(bound + 1):
        ns[k] = x
        if _reachable(subst, want, k + 1, ns, bound):
            return True
    return False


def leaf_index(cov: FamilyCover, w1: List[Int], w2: List[Int], bound: Int) -> Int:
    """The leaf whose region contains `(w_1, w_2)`: the patterns match and the
    slot values are the node's forms at some point with coordinates at most
    `bound`. -1 if none."""
    for i in range(len(cov.leaves)):
        ref nd = cov.leaves[i].node
        if not matches(nd.p1, w1) or not matches(nd.p2, w2):
            continue
        var want = slot_values(nd.p1, w1)
        var v2 = slot_values(nd.p2, w2)
        for k in range(len(v2)):
            want.append(v2[k])
        if len(nd.compared) == 0:
            return i  # identity forms: a match is membership
        var ns = List[Int](length=len(nd.subst), fill=0)
        if _reachable(nd.subst, want, 0, ns, bound):
            return i
    return -1


def main() raises:
    var args = argv()
    var max_len = Int(String(args[1])) if len(args) > 1 else 6
    var c = family_census(max_len)
    print("Theorem K's family, |w_1|, |w_2| <=", max_len, ":", c.members, "PIP members with |det M| = 2")
    print("  Lemma Phi1 (w1 begins with y):", c.by_phi1, "  Lemma Phi2 (walks cross):", c.by_phi2, "  named path failed:", c.lemma_failed)
    print("  non-crossing, decided exactly:", c.non_crossing, " deepest level", c.max_level)
    for k in range(16):
        if c.levels[k] != 0:
            print("    level", k, ":", c.levels[k])
    if len(args) > 2:
        var depth = Int(String(args[2]))
        var cov = cover_family(depth, DEFAULT_SPLITS)
        print("exploratory pattern tree to depth", depth, ":", cov.nodes, "nodes; certified", cov.certified, " empty", cov.empty, " Lemma P1 cuts", cov.cut, " decided", cov.decided, " not members", cov.not_member, " OPEN", cov.failed)


# ---------------------------------------------------------------------------
# Lemmas Φ1 and Φ2 (docs/p1a-a1-prime-2026-10-05.md §3f): explicit witness
# paths named from the words, checked by `verify_witness` on the concrete
# substitution and against the words themselves. No search.
# ---------------------------------------------------------------------------


def concrete_family(sigma: List[List[Int]]) raises -> ConeFamily:
    """A single substitution as a cone family with no variables: one letter
    segment per letter, so a segment index is a position."""
    var images = List[List[Segment]]()
    for a in range(3):
        var img = List[Segment]()
        for k in range(len(sigma[a])):
            img.append(letter_segment(0, sigma[a][k]))
        images.append(img^)
    return ConeFamily(0, images^)


def _step(i: Int, k: Int) -> WitnessStep:
    return WitnessStep(i, aff_const(0, 0), k, aff_const(0, 0))


def crossing(w1: List[Int], w2: List[Int]) -> List[Int]:
    """The first `(i, k)` with `i, k >= 1` and `pi(w1[:i]) = pi(w2[:k]) + e_y`,
    or `[-1, -1]`: the Parikh walk of `w_1` meets that of `w_2` shifted by
    `e_y`. The lengths force `i = k + 1`, and then equal `y`-counts up to one
    give equal `z`-counts."""
    var py2 = List[Int]([0])
    for j in range(len(w2)):
        py2.append(py2[j] + (1 if w2[j] == Y else 0))
    var y1 = 0
    for i in range(1, len(w1) + 1):
        if w1[i - 1] == Y:
            y1 += 1
        var k = i - 1
        if k >= 1 and k <= len(w2) and y1 == py2[k] + 1:
            return List[Int]([i, k])
    return List[Int]([-1, -1])


def named_path(w1: List[Int], w2: List[Int]) -> List[WitnessStep]:
    """Lemma Φ1 (`w_1` begins with `y`) or Lemma Φ2 (`w_1` begins with `z` and
    the walks cross): the path the lemma names, or an empty list."""
    var steps = List[WitnessStep]()
    if len(w1) == 0:
        return steps^
    steps.append(_step(0, 1))  # sigma(o) = y at 0; sigma(y) = o w1 o at 1
    if w1[0] == Y:
        if len(w1) < 2:
            return List[WitnessStep]()
        steps.append(_step(2, 1))  # gamma = -e_y + pi(o y) - pi(o) = 0
        if w1[1] != Y:
            steps.append(_step(0, 0))  # (z, y, 0): both images begin with o
        return steps^
    var c = crossing(w1, w2)
    if c[0] < 0:
        return List[WitnessStep]()
    steps.append(_step(c[0], c[1]))  # gamma = e_b - e_a, letters w1[i-1], w2[k-1]
    if w1[c[0] - 1] != w2[c[1] - 1]:
        var a = w1[c[0] - 1]
        var b = w2[c[1] - 1]
        var la = len(w1) + 1 if a == Y else len(w2) + 1
        var lb = len(w1) + 1 if b == Y else len(w2) + 1
        steps.append(_step(la, lb))  # the two final o's
    return steps^


struct FamilyCensus(Copyable, Movable):
    var members: Int
    var by_phi1: Int
    var by_phi2: Int
    var non_crossing: Int
    var lemma_failed: Int
    var levels: List[Int]  # exact levels of the non-crossing members
    var max_level: Int

    def __init__(out self):
        self.members = 0
        self.by_phi1 = 0
        self.by_phi2 = 0
        self.non_crossing = 0
        self.lemma_failed = 0
        self.levels = List[Int](length=16, fill=0)
        self.max_level = 0


def _words(max_len: Int) -> List[List[Int]]:
    var out = List[List[Int]]()
    out.append(List[Int]())
    var start = 0
    for _ in range(max_len):
        var end = len(out)
        for k in range(start, end):
            for letter in [Y, Z]:
                var w = out[k].copy()
                w.append(letter)
                out.append(w^)
        start = end
    return out^


def family_census(max_len: Int) raises -> FamilyCensus:
    """Every PIP member with `|det M| = 2` and `|w_1|, |w_2| <= max_len`: the
    lemma's named path verifies and names a shared tile of the actual words,
    or the member is non-crossing and is decided by `coincidence_level`
    (a negative would raise)."""
    var out = FamilyCensus()
    var screen = CubicScreen()
    var words = _words(max_len)
    for a in range(len(words)):
        ref w1 = words[a]
        var z1 = 0
        for k in range(len(w1)):
            if w1[k] == Z:
                z1 += 1
        for b in range(len(words)):
            ref w2 = words[b]
            var z2 = 0
            for k in range(len(w2)):
                if w2[k] == Z:
                    z2 += 1
            if abs(z1 - z2) != 1:
                continue
            var sigma = member_sigma(w1, w2)
            var mat = Mat3(substitution_incidence(sigma))
            if abs(mat.det()) != 2 or not screen.is_pip(mat):
                continue
            out.members += 1
            var steps = named_path(w1, w2)
            if len(steps) > 0:
                var fam = concrete_family(sigma)
                var ok = verify_witness(fam, O, Y, steps)
                if ok:
                    var pos = witness_position(fam, O, Y, steps, List[Int]())
                    ok = shared_tile_between(sigma, O, Y, len(steps), pos)
                if not ok:
                    out.lemma_failed += 1
                elif w1[0] == Y:
                    out.by_phi1 += 1
                else:
                    out.by_phi2 += 1
                continue
            out.non_crossing += 1
            var lev = coincidence_level(sigma, O, Y)
            if lev < 0:
                raise Error("SC REFUTED in Theorem K's family: {o, y} is not eventually coincident")
            out.levels[min(lev, 15)] += 1
            if lev > out.max_level:
                out.max_level = lev
    return out^
