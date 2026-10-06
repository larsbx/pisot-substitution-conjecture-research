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

**The delta split** (`delta_census`, `phi_path`, `phi_census`; note §3g).
`delta = pi(w_1) - pi(w_2)`. Lemma Φ4 (Pisot signs) and Lemma Φ5 (the
`Z_1 = Z_2 + 1` non-crossing shape) are checked on every member; Lemmas
Φ6-Φ8 name paths at the common points of the walks of `w_1` and `w_2 + e_z`,
which close the cell `delta = e_z` (Theorem Φ) and are measured on the rest.
With the `signatures` option `delta_census` also tallies the offset sequence
of each non-crossing member's shortest witness -- exploratory, to find the
next lemma.

**Run-shape cover** (`solve_constraint`, `cover_shape`, `shape_catalog`; note
§3h). A run shape fixes the letters of the maximal runs of `w_1` and `w_2`;
the run lengths are cone variables. The constraints `Z_1 - Z_2 = s` and an
exact `Delta` (or a tail `|Delta| >= D`) are imposed by substitutions that
partition the solutions; each region closes by a constant-offset or a
line-mode witness path (`psc.cone_witness`), a Lemma Φ4 or quadratic Lemma P1
cut, relational and value splits, or an exact decision once no variable is
left. A region still open at the limits or past the budget is reported
open. A cell with no open region is a proof for its whole infinite family.

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

Usage: `mojo run -I . odd_letter_family_certificate.mojo [max_len] [tree_depth | phi | delta | catalog]`,
or `pixi run odd-letter-family-certificate`.
"""

from std.sys import argv
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from std.collections import Dict
from psc.coincidence_formula import coincidence_level, coincidence_witness, pair_paths
from psc.cone_witness import (
    ConeFamily,
    apply_step,
    Segment,
    WitnessStep,
    aff_const,
    letter_segment,
    opaque_segment,
    run_of,
    search_witness,
    search_crossing,
    search_witness_line,
    verify_crossing,
    verify_witness,
    verify_witness_line,
    witness_position,
)
from psc.cone_witness import aff_add, aff_eval, aff_nonneg, aff_scale, aff_sub, crossing_conditions, lift_path, monotone_paths_meet
from psc.prng import SplitMix64
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
comptime NO_DELTA = -1000000  # cover_shape: leave Y_1 - Y_2 free
comptime PEEL_LIMIT = 4  # cover_shape: value splits n = 0 | n >= 1 beyond the relational ones
comptime REGION_BUDGET = 600  # cover_shape: regions examined per cell before reporting the rest open
comptime RUN_TREE_MAX_RUNS = 6  # run_tree: a pattern with this many revealed runs is not refined further
comptime RUN_TREE_SPLITS = 3  # run_tree: relational split depth per pattern
comptime RUN_TREE_PEEL = 3  # run_tree: value splits per pattern
comptime REVEAL_MAX_LEVEL = 6  # reveal census: witness depth before the Lemma X closure counts
comptime REVEAL_CAP = 8  # reveal census: largest r tried before reporting capped
comptime RUN_TREE_BUDGET = 300  # run_tree: regions examined per pattern before reporting the rest open


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
    if len(args) > 2 and String(args[2]) == "catalog":
        var cat = shape_catalog(max_len, 3, 4, True)
        var closed = 0
        var closed_keys = Dict[String, Int]()
        for k in range(len(cat)):
            if cat[k].open == 0:
                closed += 1
                closed_keys[cat[k].key] = 1
        print("shape cells:", len(cat), " closed:", closed)
        var pc2 = phi_census(max_len)
        var res_total = 0
        var res_closed = 0
        for e in pc2.shapes.items():
            var parts = e.key.split(" | ")
            var head = parts[0].split(" ")
            var cell = delta_cell(Int(String(head[1])), Int(String(head[0])), 3)
            var key = String(head[0]) + " " + String(cell[0]) + ("+" if cell[1] == 1 else "") + " | " + String(parts[1]) + " | " + String(parts[2])
            res_total += e.value
            if key in closed_keys:
                res_closed += e.value
        print("residue members:", res_total, " in closed shape cells:", res_closed, " left:", res_total - res_closed)
        return
    if len(args) > 2 and String(args[2]) == "cell":
        # one delta cell by the guided run tree: cell s delta budget max_runs
        var s = Int(String(args[3]))
        var d = Int(String(args[4]))
        var budget = Int(String(args[5]))
        var max_runs = Int(String(args[6])) if len(args) > 6 else 8
        print("cell s =", s, " Delta =", d, ": guided run tree, region budget", budget, "per pattern, at most", max_runs, "revealed runs", flush=True)
        var leaves = run_tree_guided(s, d, max_runs, budget, True)
        var closed = 0
        for k in range(len(leaves)):
            if leaves[k].closed:
                closed += 1
        print("cell s =", s, " Delta =", d, ": leaves", len(leaves), " closed", closed, " -> ", "CLOSED" if closed == len(leaves) else "OPEN", flush=True)
        return
    if len(args) > 2 and String(args[2]) == "reveal":
        # exhaustive: lengths 1..max_len of the longer word
        print("least revealed runs of a Lemma X certificate (level <=", REVEAL_MAX_LEVEL, ", r capped at", REVEAL_CAP, "; 0 = capped):")
        var first = Int(String(args[3])) if len(args) > 3 else 2
        for L in range(first, max_len + 1):
            var h = reveal_census(L, REVEAL_MAX_LEVEL, REVEAL_CAP)
            var line = "  longer word of length " + String(L) + ":"
            for r in range(len(h)):
                if h[r] != 0:
                    line += "  r=" + String(r) + ": " + String(h[r])
            print(line, flush=True)
        return
    if len(args) > 2 and String(args[2]) == "reveal-sample":
        var seed = Int(String(args[3]))
        var lo = Int(String(args[4]))
        var hi = Int(String(args[5]))
        var want = Int(String(args[6]))
        var budget = 400 * want
        var h = reveal_sample(seed, lo, hi, want, budget, REVEAL_MAX_LEVEL, REVEAL_CAP)
        var line = "seed " + String(seed) + ", lengths " + String(lo) + ".." + String(hi) + ", budget " + String(budget) + " draws: " + String(h[REVEAL_CAP + 1]) + " members" + (" (budget exhausted)" if h[REVEAL_CAP + 1] < want else "") + ";"
        for r in range(REVEAL_CAP + 1):
            if h[r] != 0:
                line += "  r=" + String(r) + ": " + String(h[r])
        print(line)
        return
    if len(args) > 2 and String(args[2]) == "excursions":
        var residue = residue_members(max_len)
        var hist = Dict[Int, Int]()
        for k in range(len(residue)):
            var n = common_points(residue[k].w1, residue[k].w2)
            hist[n] = hist.get(n, 0) + 1
        print("residue members:", len(residue), "; by number of common points:")
        for e in hist.items():
            print("   ", e.key, ":", e.value)
        return
    if len(args) > 2 and String(args[2]) == "runs":
        var residue = residue_members(max_len)
        print("run tree (max runs", RUN_TREE_MAX_RUNS, " splits", RUN_TREE_SPLITS, " peel", RUN_TREE_PEEL, " budget", RUN_TREE_BUDGET, "per pattern); residue members:", len(residue))
        var cell_s = List[Int]([1, 1, 1, -1, -1, -1])
        var cell_d = List[Int]([1, 2, 3, 0, -1, -2])
        for k in range(len(cell_s)):
            var s = cell_s[k]
            var d = cell_d[k]
            print("  cell s", s, " Delta", d, flush=True)
            var leaves = run_tree(s, d, False, RUN_TREE_MAX_RUNS, RUN_TREE_SPLITS, RUN_TREE_PEEL, RUN_TREE_BUDGET, True)
            var t = run_tree_tally(leaves, residue, s, d)
            print("  cell s", s, " Delta", d, ": leaves", t.leaves, " closed", t.closed_leaves, "; residue members", t.members, " in closed leaves", t.in_closed, flush=True)
        return
    if len(args) > 2 and String(args[2]) == "phi":
        var pc = phi_census(max_len, len(args) > 3)
        print("Lemmas Phi6-Phi8: non-crossing", pc.non_crossing, " covered", pc.by_lemma, " failed", pc.lemma_failed, " delta = e_z residue", pc.cell_ez_residue)
        for e in pc.residue.items():
            print("    residue (s dy)", e.key, ":", e.value)
        for k in range(16):
            if pc.residue_levels[k] != 0:
                print("    residue level", k, ":", pc.residue_levels[k])
        for e in pc.signatures.items():
            print("  SIG", e.key)
        for e in pc.shapes.items():
            print("  SHAPE", e.value, " ", e.key)
        return
    if len(args) > 2 and String(args[2]) == "delta":
        var dc = delta_census(max_len, True)
        print("delta split: members", dc.members, " sign violations", dc.sign_violations, " non-crossing", dc.non_crossing, " shape violations", dc.shape_violations)
        print("cells (s dy level): count")
        for e in dc.cells.items():
            print("   ", e.key, ":", e.value)
        print("signatures (s dy | gamma:a,b ...): count")
        for e in dc.signatures.items():
            print("   ", e.value, "  ", e.key)
        return
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


# ---------------------------------------------------------------------------
# The delta split (docs/p1a-a1-prime-2026-10-05.md §3g). delta = pi(w_1) -
# pi(w_2) = (Y_1 - Y_2, Z_1 - Z_2) = (dy, s). Lemma Φ4 (Pisot signs) and
# Lemma Φ5 (the s = +1 non-crossing shape) are checked on every member; the
# non-crossing members are then sorted by (s, dy) and by the offset sequence
# of their shortest witness -- exploratory, to find the next lemma.
# ---------------------------------------------------------------------------


def _signature(sigma: List[List[Int]]) raises -> String:
    """The offsets and letter pairs along the shortest `{o, y}` witness that
    `coincidence_witness` returns, as `gamma:a,b|...`."""
    var w = coincidence_witness(sigma, O, Y)
    if w.empty:
        raise Error("SC REFUTED in Theorem K's family")
    var radix = 0
    for a in range(3):
        radix = max(radix, len(sigma[a]))
    var paths = pair_paths(radix, w.word)
    var m = Mat3(substitution_incidence(sigma))
    var g = List[Int]([0, 0, 0])
    var a = O
    var b = Y
    var names = List[String](["o", "y", "z"])
    var out = String("")
    for l in range(len(w.word)):
        var i = paths[0][l]
        var k = paths[1][l]
        var g2 = List[Int]()
        for r in range(3):
            var v = 0
            for c in range(3):
                v += m.e[3 * r + c] * g[c]
            for j in range(i):
                if sigma[a][j] == r:
                    v += 1
            for j in range(k):
                if sigma[b][j] == r:
                    v -= 1
            g2.append(v)
        g = g2^
        a = sigma[a][i]
        b = sigma[b][k]
        if l > 0:
            out += "|"
        out += "(" + String(g[0]) + "," + String(g[1]) + "," + String(g[2]) + ")" + names[a] + names[b]
    return out


struct DeltaCensus(Copyable, Movable):
    var members: Int
    var sign_violations: Int  # Lemma Φ4: s = +1 needs dy >= 0; s = -1 needs dy <= 0 and Z_2 >= 2
    var shape_violations: Int  # Lemma Φ5: s = +1 non-crossing has w_1 = u y^dy, pi(u) = pi(w_2) + e_z
    var non_crossing: Int
    var cells: Dict[String, Int]  # "s dy level" -> count
    var signatures: Dict[String, Int]  # "s dy | signature" -> count

    def __init__(out self):
        self.members = 0
        self.sign_violations = 0
        self.shape_violations = 0
        self.non_crossing = 0
        self.cells = Dict[String, Int]()
        self.signatures = Dict[String, Int]()


def _bump(mut d: Dict[String, Int], key: String) raises:
    if key in d:
        d[key] = d[key] + 1
    else:
        d[key] = 1


def delta_census(max_len: Int, with_signatures: Bool) raises -> DeltaCensus:
    var out = DeltaCensus()
    var screen = CubicScreen()
    var words = _words(max_len)
    for ia in range(len(words)):
        ref w1 = words[ia]
        for ib in range(len(words)):
            ref w2 = words[ib]
            var y1 = 0
            var z1 = 0
            var y2 = 0
            var z2 = 0
            for k in range(len(w1)):
                if w1[k] == Y:
                    y1 += 1
                else:
                    z1 += 1
            for k in range(len(w2)):
                if w2[k] == Y:
                    y2 += 1
                else:
                    z2 += 1
            var s = z1 - z2
            if abs(s) != 1:
                continue
            var sigma = member_sigma(w1, w2)
            var mat = Mat3(substitution_incidence(sigma))
            if not screen.is_pip(mat):
                continue
            out.members += 1
            var dy = y1 - y2
            if (s == 1 and dy < 0) or (s == -1 and (dy > 0 or z2 < 2)):
                out.sign_violations += 1
            if len(w1) == 0 or w1[0] != Z or crossing(w1, w2)[0] >= 0:
                continue
            out.non_crossing += 1
            if s == 1:
                # w_1 = u y^dy with pi(u) = pi(w_2) + e_z
                var lu = len(w1) - dy
                var ok = lu >= 0
                if ok:
                    for k in range(lu, len(w1)):
                        if w1[k] != Y:
                            ok = False
                    var uy = 0
                    for k in range(lu):
                        if w1[k] == Y:
                            uy += 1
                    if uy != y2 or (lu - uy) != z2 + 1:
                        ok = False
                if not ok:
                    out.shape_violations += 1
            var lev = coincidence_level(sigma, O, Y)
            if lev < 0:
                raise Error("SC REFUTED in Theorem K's family: {o, y} is not eventually coincident")
            _bump(out.cells, String(s) + " " + String(dy) + " " + String(lev))
            if with_signatures:
                _bump(out.signatures, String(s) + " " + String(dy) + " | " + _signature(sigma))
    return out^


# ---------------------------------------------------------------------------
# Lemmas Φ6-Φ8 (§3g): named paths for the non-crossing members. Each lemma
# supplies the core positions; `_finish` closes a state that is already good
# (equal letters at offset 0; two letters of {y, z} at offset 0, which meet
# again at their images' initial o; or offset e_b - e_a, which meet at the
# final o). `verify_witness` then checks everything.
# ---------------------------------------------------------------------------


def _walk(w: List[Int]) -> List[List[Int]]:
    """Prefix Parikh vectors `(y, z)` of `w`, lengths 0 to |w|."""
    var out = List[List[Int]]()
    out.append(List[Int]([0, 0]))
    for k in range(len(w)):
        var p = out[k].copy()
        if w[k] == Y:
            p[0] += 1
        else:
            p[1] += 1
        out.append(p^)
    return out^


def _finish(fam: ConeFamily, var steps: List[WitnessStep]) -> List[WitnessStep]:
    """Append the closing step, if the state the steps reach is good; return
    an empty list otherwise."""
    var a = O
    var b = Y
    var g = List[Int]([0, 0, 0])
    for l in range(len(steps)):
        var r = apply_step(fam, a, b, g, steps[l])
        if not r.ok:
            return List[WitnessStep]()
        a = r.a
        b = r.b
        g = r.gamma.copy()
    if a == b and g == List[Int]([0, 0, 0]):
        return steps^
    if a == O or b == O:
        return List[WitnessStep]()
    if g == List[Int]([0, 0, 0]):
        steps.append(_step(0, 0))
        return steps^
    var want = List[Int]([0, 0, 0])
    want[b] += 1
    want[a] -= 1
    if g == want:
        steps.append(_step(len(fam.images[a]) - 1, len(fam.images[b]) - 1))
        return steps^
    return List[WitnessStep]()


def _factor_closures(fam: ConeFamily, var head: List[WitnessStep], w: List[Int], dy: Int, dz: Int) -> List[WitnessStep]:
    """From a state `(a, a, g)` whose next offset needs a factor of `w = w_a`
    with Parikh `(dy, dz)` -- a-side position after it, b-side at its start --
    or with Parikh `-(dy, dz)` the other way round: try every occurrence, in
    both the start form and the end form shifted by one."""
    var pw = _walk(w)
    for f0 in range(len(w) + 1):
        for f1 in range(f0 + 1, len(w) + 1):
            var fy = pw[f1][0] - pw[f0][0]
            var fz = pw[f1][1] - pw[f0][1]
            var forms = List[List[Int]]()
            if fy == dy and fz == dz:
                forms.append(List[Int]([f1 + 1, f0 + 1]))
                forms.append(List[Int]([f1, f0]))
            if fy == -dy and fz == -dz:
                forms.append(List[Int]([f0 + 1, f1 + 1]))
                forms.append(List[Int]([f0, f1]))
            for k in range(len(forms)):
                var s = head.copy()
                s.append(_step(forms[k][0], forms[k][1]))
                var done = _finish(fam, s^)
                if len(done) > 0:
                    return done^
    return List[WitnessStep]()


def phi_path(w1: List[Int], w2: List[Int]) raises -> List[WitnessStep]:
    """The first of Lemmas Φ6, Φ7, Φ8 that applies, as a path; empty if none."""
    var sigma = member_sigma(w1, w2)
    var fam = concrete_family(sigma)
    var dy = 0
    var dz = 0
    for k in range(len(w1)):
        dy += 1 if w1[k] == Y else 0
        dz += 1 if w1[k] == Z else 0
    for k in range(len(w2)):
        dy -= 1 if w2[k] == Y else 0
        dz -= 1 if w2[k] == Z else 0
    var p1 = _walk(w1)
    var p2 = _walk(w2)
    # Common points: pi(w1[:t]) = pi(w2[:t-1]) + e_z, with both next letters.
    for t in range(1, len(w1)):
        if t - 1 >= len(w2):
            break
        if p1[t][0] != p2[t - 1][0] or p1[t][1] != p2[t - 1][1] + 1:
            continue
        var head = List[WitnessStep]()
        head.append(_step(0, 1))
        head.append(_step(t + 1, t))
        var a = w1[t]
        var b = w2[t - 1]
        if a == b:  # Lemma Φ6
            var done = _factor_closures(fam, head^, w1 if a == Y else w2, dy, dz)
            if len(done) > 0:
                return done^
        elif a == Z and b == Y:  # Lemma Φ8: W_2 meets W_1 + delta
            for m in range(len(w2) + 1):
                for n in range(len(w1) + 1):
                    if p2[m][0] != p1[n][0] + dy or p2[m][1] != p1[n][1] + dz:
                        continue
                    for shift in range(2):
                        var s = head.copy()
                        s.append(_step(m + 1 - shift, n + 1 - shift))
                        var done = _finish(fam, s^)
                        if len(done) > 0:
                            return done^
    # Lemma Φ7: delta = e_z, w1 = zz..., w2 = y...
    if dy == 0 and dz == 1 and len(w1) >= 2 and w1[0] == Z and w1[1] == Z and len(w2) >= 1 and w2[0] == Y:
        var head = List[WitnessStep]()
        head.append(_step(0, 1))
        head.append(_step(2, 0))
        head.append(_step(1, 0))
        var done = _factor_closures(fam, head^, w1, -1, -1)  # the a-side sits at the factor's start
        if len(done) > 0:
            return done^
    return List[WitnessStep]()


struct PhiCensus(Copyable, Movable):
    var non_crossing: Int
    var by_lemma: Int
    var lemma_failed: Int
    var residue: Dict[String, Int]  # "s dy" -> residual count
    var residue_levels: List[Int]
    var cell_ez_residue: Int  # delta = e_z members no lemma covers
    var signatures: Dict[String, Int]  # residue only, when asked for: "s dy | w1 w2 | signature"
    var shapes: Dict[String, Int]  # residue only: "s dy | run shape of w1 | of w2"

    def __init__(out self):
        self.non_crossing = 0
        self.by_lemma = 0
        self.lemma_failed = 0
        self.residue = Dict[String, Int]()
        self.residue_levels = List[Int](length=16, fill=0)
        self.cell_ez_residue = 0
        self.signatures = Dict[String, Int]()
        self.shapes = Dict[String, Int]()


def run_shape(w: List[Int]) -> String:
    """The letters of `w`'s maximal runs, in order: `zzyyz` has shape `zyz`."""
    var names = List[String](["o", "y", "z"])
    var out = String("")
    for k in range(len(w)):
        if k == 0 or w[k] != w[k - 1]:
            out += names[w[k]]
    return out if len(w) > 0 else String("ε")


def _word_name(w: List[Int]) -> String:
    var names = List[String](["o", "y", "z"])
    var out = String("")
    for k in range(len(w)):
        out += names[w[k]]
    return out if len(w) > 0 else String("ε")


def phi_census(max_len: Int, with_signatures: Bool = False) raises -> PhiCensus:
    """Every non-crossing PIP member with `|det M| = 2`, `|w_i| <= max_len`:
    a Lemma Φ6-Φ8 path that verifies and names a shared tile of the words, or
    a residual member decided exactly."""
    var out = PhiCensus()
    var screen = CubicScreen()
    var words = _words(max_len)
    for ia in range(len(words)):
        ref w1 = words[ia]
        if len(w1) == 0 or w1[0] != Z:
            continue
        for ib in range(len(words)):
            ref w2 = words[ib]
            var p1 = _walk(w1)
            var p2 = _walk(w2)
            var s = p1[len(w1)][1] - p2[len(w2)][1]
            if abs(s) != 1 or crossing(w1, w2)[0] >= 0:
                continue
            var sigma = member_sigma(w1, w2)
            var mat = Mat3(substitution_incidence(sigma))
            if not screen.is_pip(mat):
                continue
            out.non_crossing += 1
            var steps = phi_path(w1, w2)
            if len(steps) > 0:
                var fam = concrete_family(sigma)
                var ok = verify_witness(fam, O, Y, steps)
                if ok:
                    ok = shared_tile_between(sigma, O, Y, len(steps), witness_position(fam, O, Y, steps, List[Int]()))
                if ok:
                    out.by_lemma += 1
                else:
                    out.lemma_failed += 1
                continue
            var dy = p1[len(w1)][0] - p2[len(w2)][0]
            _bump(out.residue, String(s) + " " + String(dy))
            if s == 1 and dy == 0:
                out.cell_ez_residue += 1
            var lev = coincidence_level(sigma, O, Y)
            if lev < 0:
                raise Error("SC REFUTED in Theorem K's family: {o, y} is not eventually coincident")
            out.residue_levels[min(lev, 15)] += 1
            _bump(out.shapes, String(s) + " " + String(dy) + " | " + run_shape(w1) + " | " + run_shape(w2))
            if with_signatures:
                _bump(out.signatures, String(s) + " " + String(dy) + " | " + _signature(sigma) + " | " + _word_name(w1) + " " + _word_name(w2))
    return out^


# ---------------------------------------------------------------------------
# Run-shape cover (§3h): the delta split with run-length splits. A run shape
# fixes the letters of the maximal runs of w_1 and of w_2; each run has length
# 1 + (its cone form). The determinant constraint Z_1 - Z_2 = s, and when
# asked a fixed Delta = Y_1 - Y_2, are imposed by exact substitutions that
# partition the solutions; each region is then covered by a witness path, a
# Lemma Φ4 cut, relational splits n_i > n_j | n_i = n_j | n_i < n_j, or an
# exact decision once no variable is left. Open regions are reported.
# ---------------------------------------------------------------------------


def _substitute_ge(subst: List[List[Int]], p: Int, q: Int) -> List[List[Int]]:
    """`n_p <- n_q + n_p`: the region `n_p >= n_q`."""
    var out = List[List[Int]]()
    for k in range(len(subst)):
        var f = subst[k].copy()
        f[q + 1] += f[p + 1]
        out.append(f^)
    return out^


def _substitute_gt(subst: List[List[Int]], p: Int, q: Int) -> List[List[Int]]:
    """`n_q <- n_p + 1 + n_q`: the region `n_q > n_p`."""
    var out = List[List[Int]]()
    for k in range(len(subst)):
        var f = subst[k].copy()
        f[0] += f[q + 1]
        f[p + 1] += f[q + 1]
        out.append(f^)
    return out^


def _set_value(subst: List[List[Int]], p: Int, v: Int) -> List[List[Int]]:
    var out = List[List[Int]]()
    for k in range(len(subst)):
        var f = subst[k].copy()
        f[0] += v * f[p + 1]
        f[p + 1] = 0
        out.append(f^)
    return out^


def solve_constraint(subst: List[List[Int]], pos: List[Int], neg: List[Int], target: Int) -> List[List[List[Int]]]:
    """All regions of `sum_pos n - sum_neg n = target` over `n >= 0`, as
    substitutions; the regions partition the solutions. Each variable is
    assumed to occur in the constraint once (identity forms on these slots)."""
    var out = List[List[List[Int]]]()
    if len(pos) == 0 and len(neg) == 0:
        if target == 0:
            out.append(subst.copy())
        return out^
    if len(neg) == 0 or len(pos) == 0:
        var side = pos.copy() if len(neg) == 0 else neg.copy()
        var t = target if len(neg) == 0 else -target
        if t < 0:
            return out^
        var rest = List[Int]()
        for k in range(1, len(side)):
            rest.append(side[k])
        if len(rest) == 0:
            out.append(_set_value(subst, side[0], t))
            return out^
        for v in range(t + 1):
            var reduced = _set_value(subst, side[0], v)
            var sub = solve_constraint(reduced, rest, List[Int](), t - v) if len(neg) == 0 else solve_constraint(reduced, List[Int](), rest, v - t)
            for k in range(len(sub)):
                out.append(sub[k].copy())
        return out^
    var p = pos[0]
    var q = neg[0]
    var neg_rest = List[Int]()
    for k in range(1, len(neg)):
        neg_rest.append(neg[k])
    var pos_rest = List[Int]()
    for k in range(1, len(pos)):
        pos_rest.append(pos[k])
    # n_p >= n_q: n_p = n_q + r, r in slot p; the constraint loses n_q
    var a = solve_constraint(_substitute_ge(subst, p, q), pos, neg_rest, target)
    for k in range(len(a)):
        out.append(a[k].copy())
    # n_q > n_p: n_q = n_p + 1 + r, r in slot q; the constraint loses n_p
    var b = solve_constraint(_substitute_gt(subst, p, q), pos_rest, neg, target + 1)
    for k in range(len(b)):
        out.append(b[k].copy())
    return out^


struct ShapeRegion(Copyable, Movable):
    var subst: List[List[Int]]
    var compared: List[Int]
    var depth: Int

    def __init__(out self, var subst: List[List[Int]], var compared: List[Int], depth: Int):
        self.subst = subst^
        self.compared = compared^
        self.depth = depth


struct ShapeCover(Copyable, Movable):
    var regions: Int
    var certified: Int
    var line_certified: Int
    var crossing_certified: Int
    var cut: Int
    var decided: Int
    var not_member: Int
    var open: Int
    var max_level: Int
    var budget_exhausted: Bool
    var open_forms: List[List[List[Int]]]

    def __init__(out self):
        self.budget_exhausted = False
        self.regions = 0
        self.certified = 0
        self.line_certified = 0
        self.crossing_certified = 0
        self.cut = 0
        self.decided = 0
        self.not_member = 0
        self.open = 0
        self.max_level = 0
        self.open_forms = List[List[List[Int]]]()


struct RunPattern(Copyable, Movable, Writable):
    """The runs of `w_1` and `w_2` (their letters, in order) and whether each
    word continues with an opaque tail standing for any further runs."""

    var l1: List[Int]
    var open1: Bool
    var l2: List[Int]
    var open2: Bool
    var suffix1: List[Int]  # letters closing w_1 (Lemma Phi5: y^Delta)
    var suffix2: List[Int]  # letters closing w_2 (Lemma Phi5': 2 - Delta letters)

    def __init__(out self, var l1: List[Int], open1: Bool, var l2: List[Int], open2: Bool, var suffix1: List[Int] = List[Int](), var suffix2: List[Int] = List[Int]()):
        self.l1 = l1^
        self.open1 = open1
        self.l2 = l2^
        self.open2 = open2
        self.suffix1 = suffix1^
        self.suffix2 = suffix2^

    def runs(self) -> Int:
        return len(self.l1) + len(self.l2)

    def slots(self) -> Int:
        """Run slots of w_1, its tail's (y, z) slots, then the same for w_2."""
        return self.runs() + (2 if self.open1 else 0) + (2 if self.open2 else 0)

    def write_to[W: Writer](self, mut w: W):
        var names = List[String](["o", "y", "z"])
        for wi in range(2):
            ref letters = self.l1 if wi == 0 else self.l2
            var opn = self.open1 if wi == 0 else self.open2
            if wi == 1:
                w.write(" | ")
            if len(letters) == 0 and not opn:
                w.write("ε")
            for k in range(len(letters)):
                w.write(names[letters[k]])
            if opn:
                w.write("*")
            ref suf = self.suffix1 if wi == 0 else self.suffix2
            if len(suf) > 0:
                w.write(" +")
                for k in range(len(suf)):
                    w.write(names[suf[k]])


def pattern_family(pat: RunPattern, subst: List[List[Int]]) raises -> ConeFamily:
    """`sigma(o) = y`, `sigma(y) = o w_1 o`, `sigma(z) = o w_2 o`: each run has
    length `1 + form`, each tail is an opaque word with Parikh `(0, ty, tz)`."""
    var m = len(subst[0]) - 1
    var images = List[List[Segment]]()
    var img_o = List[Segment]()
    img_o.append(letter_segment(m, Y))
    images.append(img_o^)
    var slot = 0
    for wi in range(2):
        ref letters = pat.l1 if wi == 0 else pat.l2
        var opn = pat.open1 if wi == 0 else pat.open2
        var img = List[Segment]()
        img.append(letter_segment(m, O))
        for k in range(len(letters)):
            var f = subst[slot].copy()
            f[0] += 1
            slot += 1
            img.append(run_of(letters[k], f^))
        if opn:
            var par = List[List[Int]]()
            par.append(aff_const(m, 0))
            par.append(subst[slot].copy())
            par.append(subst[slot + 1].copy())
            slot += 2
            img.append(opaque_segment(par^))
        ref suf = pat.suffix1 if wi == 0 else pat.suffix2
        for k in range(len(suf)):
            img.append(letter_segment(m, suf[k]))
        img.append(letter_segment(m, O))
        images.append(img^)
    return ConeFamily(m, images^)


def shape_family(l1: List[Int], l2: List[Int], subst: List[List[Int]]) raises -> ConeFamily:
    """A run shape with no tails; see `pattern_family`."""
    return pattern_family(RunPattern(l1.copy(), False, l2.copy(), False), subst)


def pattern_counts(pat: RunPattern, subst: List[List[Int]]) -> List[List[Int]]:
    """Affine forms of `Y_1, Z_1, Y_2, Z_2`."""
    var m = len(subst[0]) - 1
    var out = List[List[Int]]()
    for _ in range(4):
        out.append(aff_const(m, 0))
    var slot = 0
    for wi in range(2):
        ref letters = pat.l1 if wi == 0 else pat.l2
        var opn = pat.open1 if wi == 0 else pat.open2
        for k in range(len(letters)):
            var f = subst[slot].copy()
            f[0] += 1
            var idx = 2 * wi + (0 if letters[k] == Y else 1)
            out[idx] = aff_add(out[idx], f)
            slot += 1
        if opn:
            out[2 * wi] = aff_add(out[2 * wi], subst[slot])
            out[2 * wi + 1] = aff_add(out[2 * wi + 1], subst[slot + 1])
            slot += 2
    for wi in range(2):
        ref suf = pat.suffix1 if wi == 0 else pat.suffix2
        for k in range(len(suf)):
            out[2 * wi + (0 if suf[k] == Y else 1)][0] += 1
    return out^


def _quadratic_nonneg(a: List[Int], b: List[Int], c: List[Int]) -> Bool:
    """Is `a * b + c` (affine forms over `n >= 0`) provably nonnegative: all
    coefficients of the expanded quadratic polynomial nonnegative?"""
    var m = len(a) - 1
    if a[0] * b[0] + c[0] < 0:
        return False
    for i in range(1, m + 1):
        if a[0] * b[i] + a[i] * b[0] + c[i] < 0:
            return False
        for j in range(i, m + 1):
            var q = a[i] * b[j] + (a[j] * b[i] if j != i else 0)
            if q < 0:
                return False
    return True


def pisot_cut(counts: List[List[Int]], s: Int) -> Bool:
    """No PIP member in the region. Lemma Φ4: for s = +1 if `Y_2 - Y_1 - 1 >= 0`;
    for s = -1 if `Y_1 - Y_2 - 1 >= 0` or `1 - Z_2 >= 0`. Lemma P1 in the exact
    forms of §3h: for s = +1 if `Z_2 (Delta - 1) - 2 Y_2 - Delta - 3 >= 0`,
    for s = -1 if `Z_2 (|Delta| - 1) - 2 Y_1 - |Delta| + 3 >= 0`, with
    `Delta = Y_1 - Y_2`. Each condition is checked by coefficient signs."""
    var dy = aff_sub(counts[0], counts[2])
    if s == 1:
        var g = aff_scale(dy, -1)
        g[0] -= 1
        if aff_nonneg(g):
            return True
    else:
        var g = dy.copy()
        g[0] -= 1
        if aff_nonneg(g):
            return True
        var h = aff_scale(counts[3], -1)
        h[0] += 1
        if aff_nonneg(h):
            return True
    var ad = dy.copy() if s == 1 else aff_scale(dy, -1)
    var factor = ad.copy()
    factor[0] -= 1
    var rest = aff_scale(ad, -1)
    if s == 1:
        rest = aff_sub(rest, aff_scale(counts[2], 2))
        rest[0] -= 3
    else:
        rest = aff_sub(rest, aff_scale(counts[0], 2))
        rest[0] += 3
    return _quadratic_nonneg(counts[3], factor, rest)


def _pattern_starts(pat: RunPattern, s: Int, delta: Int, tail: Bool) -> List[List[List[Int]]]:
    """The regions of the pattern's variables solving `Z_1 - Z_2 = s` and
    `Y_1 - Y_2 = delta` (or the tail `|Delta| >= |delta|`), as substitutions."""
    var slots = pat.slots()
    var m = slots + (1 if tail else 0)
    var zpos = List[Int]()
    var zneg = List[Int]()
    var ypos = List[Int]()
    var yneg = List[Int]()
    var zconst = 0
    var yconst = 0
    var slot = 0
    for wi in range(2):
        ref letters = pat.l1 if wi == 0 else pat.l2
        var opn = pat.open1 if wi == 0 else pat.open2
        var sg = 1 if wi == 0 else -1
        for k in range(len(letters)):
            if letters[k] == Z:
                if wi == 0:
                    zpos.append(slot)
                else:
                    zneg.append(slot)
                zconst += sg
            else:
                if wi == 0:
                    ypos.append(slot)
                else:
                    yneg.append(slot)
                yconst += sg
            slot += 1
        if opn:
            if wi == 0:
                ypos.append(slot)
                zpos.append(slot + 1)
            else:
                yneg.append(slot)
                zneg.append(slot + 1)
            slot += 2
    for wi in range(2):
        ref suf = pat.suffix1 if wi == 0 else pat.suffix2
        for k in range(len(suf)):
            if suf[k] == Y:
                yconst += 1 if wi == 0 else -1
            else:
                zconst += 1 if wi == 0 else -1
    var starts = solve_constraint(identity_subst(m), zpos, zneg, s - zconst)
    if delta != NO_DELTA:
        if tail:
            if delta >= 0:
                yneg.append(slots)  # Y_1 - Y_2 - e = delta
            else:
                ypos.append(slots)  # Y_1 - Y_2 + e = delta
        var both = List[List[List[Int]]]()
        for k in range(len(starts)):
            var more = solve_constraint(starts[k], ypos, yneg, delta - yconst)
            for j in range(len(more)):
                both.append(more[j].copy())
        starts = both^
    return starts^


def cover_pattern(pat: RunPattern, s: Int, delta: Int, split_limit: Int, tail: Bool = False, peel_limit: Int = PEEL_LIMIT, region_budget: Int = REGION_BUDGET) raises -> ShapeCover:
    """Cover every member of the pattern with `Z_1 - Z_2 = s`, and with
    `Y_1 - Y_2 = delta` unless `delta` is `NO_DELTA` -- or, with `tail`, with
    `|Y_1 - Y_2| >= |delta|` on `delta`'s side, carried by one extra variable."""
    var out = ShapeCover()
    var screen = CubicScreen()
    var m = pat.slots() + (1 if tail else 0)
    var starts = _pattern_starts(pat, s, delta, tail)
    var stack = List[ShapeRegion]()
    for k in range(len(starts)):
        stack.append(ShapeRegion(starts[k].copy(), List[Int](), 0))
    while len(stack) > 0:
        var reg = stack.pop()
        out.regions += 1
        if out.regions > region_budget:
            # budget exhausted: everything still unexamined is reported open
            out.open += 1 + len(stack)
            out.budget_exhausted = True
            break
        if pisot_cut(pattern_counts(pat, reg.subst), s):
            out.cut += 1
            continue
        var fam = pattern_family(pat, reg.subst)
        var w = search_witness(fam, O, Y, OFFSET_BOUND, MAX_LEVEL, True)
        if w.found:
            if not verify_witness(fam, O, Y, w.steps):
                raise Error("a witness path the search found does not verify")
            out.certified += 1
            out.max_level = max(out.max_level, len(w.steps))
            continue
        var wl = search_witness_line(fam, O, Y, OFFSET_BOUND, MAX_LEVEL, Y, Z)
        if wl.found:
            if not verify_witness_line(fam, O, Y, wl.steps):
                raise Error("a line-mode witness path the search found does not verify")
            out.certified += 1
            out.line_certified += 1
            out.max_level = max(out.max_level, len(wl.steps))
            continue
        var wc = search_crossing(fam, O, Y, OFFSET_BOUND, MAX_LEVEL - 2, Y, Z, Y, Z)
        if wc.found:
            if not verify_crossing(fam, O, Y, wc.steps, wc.close[0], Y, Z):
                raise Error("a crossing closure the search found does not verify")
            out.certified += 1
            out.crossing_certified += 1
            out.max_level = max(out.max_level, len(wc.steps) + 2)
            continue
        var any_live = False
        for k in range(m):
            if _live(reg.subst, k):
                any_live = True
        if not any_live:
            var sigma = fam.instantiate(List[Int](length=m, fill=0))
            var mat = Mat3(substitution_incidence(sigma))
            if abs(mat.det()) != 2 or not screen.is_pip(mat):
                out.not_member += 1
                continue
            var lev = coincidence_level(sigma, O, Y)
            if lev < 0:
                raise Error("SC REFUTED in Theorem K's family: {o, y} is not eventually coincident")
            out.decided += 1
            out.max_level = max(out.max_level, lev)
            continue
        var node = Node(any_word(), any_word(), reg.subst.copy(), reg.compared.copy(), 0)
        var pair = _next_pair(node)
        if pair[0] < 0 or len(reg.compared) >= split_limit:
            # value split of the first live variable: n = 0 | n = 1 + n'
            var first = -1
            for k in range(m):
                if _live(reg.subst, k) and first < 0:
                    first = k
            if first < 0 or reg.depth >= split_limit + peel_limit:
                out.open += 1
                out.open_forms.append(reg.subst.copy())
                continue
            stack.append(ShapeRegion(_set_value(reg.subst, first, 0), reg.compared.copy(), reg.depth + 1))
            var shifted = List[List[Int]]()
            for k in range(len(reg.subst)):
                var f = reg.subst[k].copy()
                f[0] += f[first + 1]
                shifted.append(f^)
            stack.append(ShapeRegion(shifted^, reg.compared.copy(), reg.depth + 1))
            continue
        for which in range(3):
            var comp = reg.compared.copy()
            comp.append(pair[0] * 1000 + pair[1])
            stack.append(ShapeRegion(_split(reg.subst, pair[0], pair[1], which), comp^, reg.depth + 1))
    return out^


def cover_shape(l1: List[Int], l2: List[Int], s: Int, delta: Int, split_limit: Int, tail: Bool = False, peel_limit: Int = PEEL_LIMIT, region_budget: Int = REGION_BUDGET) raises -> ShapeCover:
    """A run shape with no tails; see `cover_pattern`."""
    return cover_pattern(RunPattern(l1.copy(), False, l2.copy(), False), s, delta, split_limit, tail, peel_limit, region_budget)


def _letters(shape: String) -> List[Int]:
    var out = List[Int]()
    var b = shape.as_bytes()
    for k in range(len(b)):
        if Int(b[k]) == ord("y"):
            out.append(Y)
        elif Int(b[k]) == ord("z"):
            out.append(Z)
    return out^


def delta_cell(dy: Int, s: Int, exact_cap: Int) -> List[Int]:
    """The cover cell of `Delta`: `[delta, tail]`, exact for `|Delta| <=
    exact_cap`, else the tail `|Delta| >= exact_cap + 1` on its side."""
    if abs(dy) <= exact_cap:
        return List[Int]([dy, 0])
    return List[Int]([(exact_cap + 1) if dy > 0 else -(exact_cap + 1), 1])


struct CatalogEntry(Copyable, Movable):
    var key: String
    var open: Int
    var certified: Int
    var cut: Int

    def __init__(out self, key: String, open: Int, certified: Int, cut: Int):
        self.key = key
        self.open = open
        self.certified = certified
        self.cut = cut


def shape_catalog(max_len: Int, exact_cap: Int, split_limit: Int, verbose: Bool = False) raises -> List[CatalogEntry]:
    """Cover every (run shape, s, Delta cell) that a residual member of
    `phi_census(max_len)` falls in; one entry per cell, with its open count."""
    var pc = phi_census(max_len)
    var done = Dict[String, Int]()
    var out = List[CatalogEntry]()
    for e in pc.shapes.items():
        var parts = e.key.split(" | ")
        var head = parts[0].split(" ")
        var s = Int(String(head[0]))
        var dy = Int(String(head[1]))
        var cell = delta_cell(dy, s, exact_cap)
        var key = String(s) + " " + String(cell[0]) + ("+" if cell[1] == 1 else "") + " | " + String(parts[1]) + " | " + String(parts[2])
        if key in done:
            continue
        var l2 = _letters(String(parts[2])) if String(parts[2]) != "ε" else List[Int]()
        var c = cover_shape(_letters(String(parts[1])), l2, s, cell[0], split_limit, cell[1] == 1, split_limit)
        done[key] = len(out)
        out.append(CatalogEntry(key, c.open, c.certified, c.cut))
        if verbose:
            print("   ", "closed" if c.open == 0 else ("BUDGET" if c.budget_exhausted else "OPEN  "), key, "  regions", c.regions, " certified", c.certified, " (line", c.line_certified, ") cut", c.cut, " decided", c.decided, " open", c.open, flush=True)
    return out^


# ---------------------------------------------------------------------------
# Run tree (§3i): induction on the number of runs. A pattern's tail stands for
# any further runs; runs alternate, so a tail is either empty or one more run
# of the other letter followed by a new tail -- a partition. Each pattern is
# covered by `cover_pattern` in the given delta cell; an uncovered pattern is
# refined by one run, up to `max_runs`. If every branch closes, the cell is
# proved for words with any number of runs.
# ---------------------------------------------------------------------------


struct RunTreeLeaf(Copyable, Movable):
    var pattern: RunPattern
    var closed: Bool
    var open_regions: Int
    var certified: Int
    var cut: Int

    def __init__(out self, var pattern: RunPattern, closed: Bool, open_regions: Int, certified: Int, cut: Int):
        self.pattern = pattern^
        self.closed = closed
        self.open_regions = open_regions
        self.certified = certified
        self.cut = cut


def refine_pattern(pat: RunPattern) -> List[RunPattern]:
    """Partition an open pattern by one run of the open word with fewer runs
    (`w_1` on ties): its tail ends, or continues with a run of the letter
    other than its last run's (either letter if it has no run yet)."""
    var out = List[RunPattern]()
    var pick = 0
    if pat.open1 and pat.open2:
        pick = 0 if len(pat.l1) <= len(pat.l2) else 1
    elif pat.open2:
        pick = 1
    elif not pat.open1:
        return out^
    ref letters = pat.l1 if pick == 0 else pat.l2
    var nexts = List[Int]()
    if len(letters) == 0:
        nexts.append(Y)
        nexts.append(Z)
    else:
        nexts.append(Z if letters[len(letters) - 1] == Y else Y)
    if pick == 0:
        out.append(RunPattern(pat.l1.copy(), False, pat.l2.copy(), pat.open2, pat.suffix1.copy(), pat.suffix2.copy()))
        for k in range(len(nexts)):
            var l = pat.l1.copy()
            l.append(nexts[k])
            out.append(RunPattern(l^, True, pat.l2.copy(), pat.open2, pat.suffix1.copy(), pat.suffix2.copy()))
    else:
        out.append(RunPattern(pat.l1.copy(), pat.open1, pat.l2.copy(), False, pat.suffix1.copy(), pat.suffix2.copy()))
        for k in range(len(nexts)):
            var l = pat.l2.copy()
            l.append(nexts[k])
            out.append(RunPattern(pat.l1.copy(), pat.open1, l^, True, pat.suffix1.copy(), pat.suffix2.copy()))
    return out^


def run_tree(s: Int, delta: Int, tail: Bool, max_runs: Int, split_limit: Int, peel_limit: Int, budget: Int, verbose: Bool = False) raises -> List[RunTreeLeaf]:
    """The run tree of one delta cell, from the root `w_1 = z^+ *`, `w_2 = *`
    (`w_1` beginning with `y` is Lemma Φ1; `w_1` without `z` is not
    primitive)."""
    var out = List[RunTreeLeaf]()
    var stack = List[RunPattern]()
    stack.append(RunPattern(List[Int]([Z]), True, List[Int](), True))
    while len(stack) > 0:
        var pat = stack.pop()
        var c = cover_pattern(pat, s, delta, split_limit, tail, peel_limit, budget)
        if c.open == 0:
            if verbose:
                print("    closed ", pat, "  regions", c.regions, " certified", c.certified, " (line", c.line_certified, ") cut", c.cut, " decided", c.decided, flush=True)
            out.append(RunTreeLeaf(pat.copy(), True, 0, c.certified, c.cut))
            continue
        var kids = refine_pattern(pat)
        if pat.runs() >= max_runs or len(kids) == 0:
            if verbose:
                print("    OPEN   ", pat, "  regions", c.regions, " open", c.open, " budget" if c.budget_exhausted else "", flush=True)
            out.append(RunTreeLeaf(pat.copy(), False, c.open, c.certified, c.cut))
            continue
        if verbose:
            print("    refine ", pat, "  (open", c.open, ")", flush=True)
        for k in range(len(kids)):
            stack.append(kids[k].copy())
    return out^


def _run_letters(w: List[Int]) -> List[Int]:
    var out = List[Int]()
    for k in range(len(w)):
        if k == 0 or w[k] != w[k - 1]:
            out.append(w[k])
    return out^


def pattern_matches(pat: RunPattern, w1: List[Int], w2: List[Int]) -> Bool:
    """Does the word pair lie in the pattern: each word's run letters equal the
    revealed ones, or begin with them when the word has a tail; with a
    suffix, a word ends in its suffix and the runs are those of the rest."""
    var cores = List[List[Int]]()
    for wi in range(2):
        ref w = w1 if wi == 0 else w2
        ref suf = pat.suffix1 if wi == 0 else pat.suffix2
        var n = len(w) - len(suf)
        if n < 0:
            return False
        for k in range(len(suf)):
            if w[n + k] != suf[k]:
                return False
        var core = List[Int]()
        for k in range(n):
            core.append(w[k])
        cores.append(core^)
    for wi in range(2):
        var runs = _run_letters(cores[wi])
        ref letters = pat.l1 if wi == 0 else pat.l2
        var opn = pat.open1 if wi == 0 else pat.open2
        if len(runs) < len(letters) or (not opn and len(runs) != len(letters)):
            return False
        for k in range(len(letters)):
            if runs[k] != letters[k]:
                return False
    return True


struct ResidueMember(Copyable, Movable):
    var w1: List[Int]
    var w2: List[Int]
    var s: Int
    var dy: Int

    def __init__(out self, var w1: List[Int], var w2: List[Int], s: Int, dy: Int):
        self.w1 = w1^
        self.w2 = w2^
        self.s = s
        self.dy = dy


def residue_members(max_len: Int) raises -> List[ResidueMember]:
    """The members `phi_census` leaves: non-crossing, `w_1` beginning with `z`,
    no Lemma Φ6-Φ8 path."""
    var out = List[ResidueMember]()
    var screen = CubicScreen()
    var words = _words(max_len)
    for ia in range(len(words)):
        ref w1 = words[ia]
        if len(w1) == 0 or w1[0] != Z:
            continue
        for ib in range(len(words)):
            ref w2 = words[ib]
            var p1 = _walk(w1)
            var p2 = _walk(w2)
            var s = p1[len(w1)][1] - p2[len(w2)][1]
            if abs(s) != 1 or crossing(w1, w2)[0] >= 0:
                continue
            var mat = Mat3(substitution_incidence(member_sigma(w1, w2)))
            if not screen.is_pip(mat):
                continue
            if len(phi_path(w1, w2)) > 0:
                continue
            out.append(ResidueMember(w1.copy(), w2.copy(), s, p1[len(w1)][0] - p2[len(w2)][0]))
    return out^


def run_leaf_index(leaves: List[RunTreeLeaf], w1: List[Int], w2: List[Int]) raises -> Int:
    """The run-tree leaf holding a word pair. The leaves partition the pairs
    whose `w_1` begins with `z`, so anything but exactly one match raises."""
    var hit = -1
    for k in range(len(leaves)):
        if pattern_matches(leaves[k].pattern, w1, w2):
            if hit >= 0:
                raise Error("run-tree leaves overlap")
            hit = k
    if hit < 0:
        raise Error("run-tree leaves miss a word pair")
    return hit


struct RunTreeTally(Copyable, Movable):
    var leaves: Int
    var closed_leaves: Int
    var members: Int
    var in_closed: Int

    def __init__(out self):
        self.leaves = 0
        self.closed_leaves = 0
        self.members = 0
        self.in_closed = 0


def run_tree_tally(leaves: List[RunTreeLeaf], residue: List[ResidueMember], s: Int, delta: Int) raises -> RunTreeTally:
    """How many residue members of the cell `(s, Delta)` lie in closed leaves."""
    var t = RunTreeTally()
    t.leaves = len(leaves)
    for k in range(len(leaves)):
        if leaves[k].closed:
            t.closed_leaves += 1
    for k in range(len(residue)):
        if residue[k].s != s or residue[k].dy != delta:
            continue
        t.members += 1
        if leaves[run_leaf_index(leaves, residue[k].w1, residue[k].w2)].closed:
            t.in_closed += 1
    return t^


def common_points(w1: List[Int], w2: List[Int]) -> Int:
    """The number of common points (§3g): `t >= 1` with `w_1[t]`, `w_2[t - 1]`
    defined and `pi(w_1[:t]) = pi(w_2[:t - 1]) + e_z`. The prefix lengths
    differ by one, so equal `y`-counts suffice."""
    var n = 0
    var y1 = 0
    var y2 = 0
    for t in range(1, len(w1)):
        if w1[t - 1] == Y:
            y1 += 1
        if t - 1 > len(w2) - 1:
            break
        if t >= 2 and w2[t - 2] == Y:
            y2 += 1
        if y1 == y2:
            n += 1
    return n



# ---------------------------------------------------------------------------
# How much a Lemma X certificate must reveal (§3j). A member's words are read
# only at *revealed* points: positions inside the first r runs of each word,
# the suffix that Lemma Phi5 (s = +1: w_1 = u y^Delta) or Lemma Phi5' (s = -1:
# the last 2 - Delta letters of w_2) makes explicit, the synchronized cuts
# (w_1 near |w_2| + 1, w_2 near |w_1|), and, for a closure step, the lagged
# images of the other word's revealed points. A certificate is an exact path
# through revealed positions to a state that Lemma X closes on revealed
# endpoints: it would close every member that agrees on those points.
# ---------------------------------------------------------------------------


def _run_starts(w: List[Int], r: Int) -> Int:
    """Length of the first `r` runs of `w`."""
    var runs = 0
    for k in range(1, len(w)):
        if w[k] != w[k - 1]:
            runs += 1
            if runs == r:
                return k
    return len(w)


def _sorted_unique(var xs: List[Int]) -> List[Int]:
    sort(xs)
    var out = List[Int]()
    for k in range(len(xs)):
        if k == 0 or xs[k] != xs[k - 1]:
            out.append(xs[k])
    return out^


struct Revealed(Copyable, Movable):
    """Revealed positions (letters readable) and points (walk values readable)
    of both words, for one member and one `r`."""

    var words: List[List[Int]]
    var walks: List[List[List[Int]]]
    var known: List[List[Bool]]  # known[i][p]: letter p of word i is revealed
    var points: List[List[Int]]  # revealed prefix lengths of word i
    var sigma: List[List[Int]]
    var mat: List[List[Int]]

    def __init__(out self, w1: List[Int], w2: List[Int], r: Int):
        self.words = List[List[Int]]()
        self.words.append(w1.copy())
        self.words.append(w2.copy())
        self.walks = List[List[List[Int]]]()
        self.walks.append(_walk(w1))
        self.walks.append(_walk(w2))
        var s = self.walks[0][len(w1)][1] - self.walks[1][len(w2)][1]
        self.known = List[List[Bool]]()
        self.points = List[List[Int]]()
        for i in range(2):
            ref w = self.words[i]
            var lim = _run_starts(w, r)
            var kn = List[Bool]()
            for p in range(len(w)):
                kn.append(p < lim)
            var pts = List[Int]([0, len(w)])
            var runs = 0
            for k in range(1, len(w)):
                if w[k] != w[k - 1]:
                    runs += 1
                    if runs <= r:
                        pts.append(k)
            self.known.append(kn^)
            self.points.append(pts^)
        var l1 = len(w1)
        var l2 = len(w2)
        if s == 1:
            # Lemma Phi5: w_1 = u y^Delta with |u| = |w_2| + 1.
            for p in range(min(l2 + 1, l1), l1):
                self.known[0][p] = True
            for p in range(l2, min(l2 + 3, l1)):
                self.points[0].append(p)
        elif s == -1:
            # Lemma Phi5': the last 2 - Delta letters of w_2 start at |w_1| - 1.
            for p in range(max(l1 - 1, 0), l2):
                self.known[1][p] = True
                self.points[1].append(p)
            for p in range(max(l1 - 1, 0), min(l1 + 2, l2)):
                self.points[1].append(p)
        for i in range(2):
            self.points[i] = _sorted_unique(self.points[i].copy())
        self.sigma = member_sigma(w1, w2)
        self.mat = List[List[Int]]()
        for i in range(3):
            var row = List[Int]()
            for j in range(3):
                var n = 0
                for k in range(len(self.sigma[j])):
                    n += 1 if self.sigma[j][k] == i else 0
                row.append(n)
            self.mat.append(row^)

    def m_times(self, g: List[Int]) -> List[Int]:
        var out = List[Int](length=3, fill=0)
        for i in range(3):
            for j in range(3):
                out[i] += self.mat[i][j] * g[j]
        return out^

    def positions(self, a: Int) -> List[Int]:
        """Revealed positions of `sigma(a)`: its ends and revealed letters."""
        var out = List[Int]()
        var n = len(self.sigma[a])
        if a == O:
            out.append(0)
            return out^
        ref kn = self.known[0 if a == Y else 1]
        for p in range(n):
            if p == 0 or p == n - 1 or kn[p - 1]:
                out.append(p)
        return out^


def _lemma_x_closes(rv: Revealed, a: Int, b: Int, mg: List[Int]) -> Bool:
    """Lemma X from the state with letters `a, b` in {y, z} and `M gamma = mg`
    (o-part 0): `W_a` meets `W_b - mg` between revealed points."""
    var wa = 0 if a == Y else 1
    var wb = 0 if b == Y else 1
    ref pa = rv.walks[wa]
    ref pb = rv.walks[wb]
    var la = len(rv.words[wa])
    var lb = len(rv.words[wb])
    var lag = -mg[1] - mg[2]
    var ia = rv.points[wa].copy()
    var kb = rv.points[wb].copy()
    for k in range(len(rv.points[wb])):
        var i = rv.points[wb][k] + lag
        if i >= 0 and i <= la:
            ia.append(i)
    for i in range(len(rv.points[wa])):
        var k = rv.points[wa][i] - lag
        if k >= 0 and k <= lb:
            kb.append(k)
    var pts_a = _sorted_unique(ia^)
    var pts_b = _sorted_unique(kb^)
    for i0 in range(len(pts_a)):
        for i1 in range(i0 + 1, len(pts_a)):
            for k0 in range(len(pts_b)):
                for k1 in range(k0 + 1, len(pts_b)):
                    var q0 = List[Int]([pb[pts_b[k0]][0] - mg[1], pb[pts_b[k0]][1] - mg[2]])
                    var q1 = List[Int]([pb[pts_b[k1]][0] - mg[1], pb[pts_b[k1]][1] - mg[2]])
                    if monotone_paths_meet(pa[pts_a[i0]], pa[pts_a[i1]], q0, q1, pts_a[i1] < la and pts_b[k1] < lb):
                        return True
    return False


def reveal_certificate(w1: List[Int], w2: List[Int], r: Int, max_level: Int) raises -> Int:
    """The level of the first certificate that reads only revealed data (an
    exact shared tile, or Lemma X plus its two levels), or -1."""
    var rv = Revealed(w1, w2, r)
    var seen = Dict[String, Int]()
    var fa = List[Int]([O])
    var fb = List[Int]([Y])
    var fg = List[List[Int]]()
    fg.append(List[Int]([0, 0, 0]))
    var bound = len(w1) + len(w2) + 4
    for level in range(1, max_level + 1):
        var na = List[Int]()
        var nb = List[Int]()
        var ng = List[List[Int]]()
        for f in range(len(fa)):
            var a = fa[f]
            var b = fb[f]
            var mg = rv.m_times(fg[f])
            var pa = rv.positions(a)
            var pb = rv.positions(b)
            for x in range(len(pa)):
                for y in range(len(pb)):
                    var g2 = mg.copy()
                    for k in range(pa[x]):
                        g2[rv.sigma[a][k]] += 1
                    for k in range(pb[y]):
                        g2[rv.sigma[b][k]] -= 1
                    var a2 = rv.sigma[a][pa[x]]
                    var b2 = rv.sigma[b][pb[y]]
                    if g2[0] == 0 and g2[1] == 0 and g2[2] == 0:
                        if a2 == b2:
                            return level
                        if a2 != O and b2 != O:
                            return level + 1
                    if abs(g2[0]) > bound or abs(g2[1]) > bound or abs(g2[2]) > bound:
                        continue
                    var key = String(a2) + String(b2) + " " + String(g2[0]) + " " + String(g2[1]) + " " + String(g2[2])
                    if key in seen:
                        continue
                    seen[key] = 1
                    if a2 != O and b2 != O:
                        var m2 = rv.m_times(g2)
                        if m2[0] == 0 and _lemma_x_closes(rv, a2, b2, m2):
                            return level + 2
                    na.append(a2)
                    nb.append(b2)
                    ng.append(g2^)
        fa = na^
        fb = nb^
        fg = ng^
    return -1


def least_reveal(w1: List[Int], w2: List[Int], max_level: Int, cap: Int) raises -> Int:
    """Least `r <= cap` with a revealed certificate, or -1 (capped)."""
    for r in range(1, cap + 1):
        if reveal_certificate(w1, w2, r, max_level) >= 0:
            return r
    return -1


def _noncrossing_member(mut screen: CubicScreen, w1: List[Int], w2: List[Int]) raises -> Bool:
    var p1 = _walk(w1)
    var p2 = _walk(w2)
    if abs(p1[len(w1)][1] - p2[len(w2)][1]) != 1 or crossing(w1, w2)[0] >= 0:
        return False
    return screen.is_pip(Mat3(substitution_incidence(member_sigma(w1, w2))))


def reveal_census(length: Int, max_level: Int, cap: Int) raises -> List[Int]:
    """Histogram of `least_reveal` (index 0: capped) over the non-crossing PIP
    members with `w_1` beginning with `z` and longer word of exactly `length`."""
    var hist = List[Int](length=cap + 1, fill=0)
    var screen = CubicScreen()
    var words = _words(length)
    for ia in range(len(words)):
        ref w1 = words[ia]
        if len(w1) == 0 or w1[0] != Z:
            continue
        for ib in range(len(words)):
            ref w2 = words[ib]
            if max(len(w1), len(w2)) != length or not _noncrossing_member(screen, w1, w2):
                continue
            var r = least_reveal(w1, w2, max_level, cap)
            hist[max(r, 0)] += 1
    return hist^


def reveal_sample(seed: Int, lo: Int, hi: Int, want: Int, budget: Int, max_level: Int, cap: Int) raises -> List[Int]:
    """The same histogram over a seeded sample: lengths uniform in
    `[lo, hi]`, letters fair; draws stop at `budget`. Entry `cap + 1` holds
    the members sampled, so a short count shows an exhausted budget."""
    var hist = List[Int](length=cap + 2, fill=0)
    var rng = SplitMix64(seed)
    var screen = CubicScreen()
    var draws = 0
    while hist[cap + 1] < want and draws < budget:
        draws += 1
        var l1 = rng.between(lo, hi)
        var l2 = rng.between(lo, hi)
        var w1 = List[Int]([Z])
        for _ in range(l1 - 1):
            w1.append(Y if rng.below(2) == 0 else Z)
        var w2 = List[Int]()
        for _ in range(l2):
            w2.append(Y if rng.below(2) == 0 else Z)
        if not _noncrossing_member(screen, w1, w2):
            continue
        hist[cap + 1] += 1
        hist[max(least_reveal(w1, w2, max_level, cap), 0)] += 1
    return hist^



# ---------------------------------------------------------------------------
# Certificate-guided partition (§3k). A region is the image of an orthant
# under an affine substitution of the cone variables. `impose_nonneg` splits a
# region into finitely many regions that exactly cover the points where an
# affine form F is nonnegative, for any integer coefficients, and on each of
# them F is nonnegative coefficientwise -- so the ordinary verifiers accept it.
# For a variable n_p with coefficient a > 0 write F = a n_p - R. Either
# R <= 0, and F >= 0 holds throughout; or R >= 1, and then n_p >= ceil(R / a):
# split the other variables by their residues mod a until R / a is affine,
# and substitute n_p <- ceil(R / a) + n_p. Both cases recurse on R, which
# omits n_p, so the recursion ends. With no positive coefficient the
# variables of F are bounded and are enumerated.
# ---------------------------------------------------------------------------


def _subst_var(forms: List[List[Int]], p: Int, repl: List[Int]) -> List[List[Int]]:
    """Every form with the variable `n_p` replaced by the affine form `repl`
    (which may itself contain `n_p`)."""
    var out = List[List[Int]]()
    for k in range(len(forms)):
        var g = forms[k].copy()
        var c = g[p + 1]
        g[p + 1] = 0
        if c != 0:
            for j in range(len(g)):
                g[j] += c * repl[j]
        out.append(g^)
    return out^


def _drop_tail(forms: List[List[Int]], keep: Int) -> List[List[Int]]:
    var out = List[List[Int]]()
    for k in range(keep):
        out.append(forms[k].copy())
    return out^


def _residues(forms: List[List[Int]], idx: Int, a: Int, p: Int) -> List[List[List[Int]]]:
    """Split every variable other than `n_p` whose coefficient in `forms[idx]`
    is not divisible by `a` as `n_k <- a n_k + rho`, rho in [0, a)."""
    var out = List[List[List[Int]]]()
    out.append(forms.copy())
    var m = len(forms[0]) - 1
    for k in range(m):
        if k == p:
            continue
        var next = List[List[List[Int]]]()
        for r in range(len(out)):
            var c = out[r][idx][k + 1]
            if c % a == 0:
                next.append(out[r].copy())
                continue
            for rho in range(a):
                var repl = aff_const(m, rho)
                repl[k + 1] = a
                next.append(_subst_var(out[r], k, repl))
        out = next^
    return out^


def impose_nonneg(forms: List[List[Int]], idx: Int) raises -> List[List[List[Int]]]:
    """Regions partitioning the points of `forms` (a region with constraint
    forms appended) where `forms[idx] >= 0`; on each, that form is
    nonnegative coefficientwise."""
    var out = List[List[List[Int]]]()
    ref F = forms[idx]
    var m = len(F) - 1
    if aff_nonneg(F):
        out.append(forms.copy())
        return out^
    var p = -1
    for k in range(m):
        if F[k + 1] > 0 and (p < 0 or F[k + 1] < F[p + 1]):
            p = k
    if p < 0:
        if F[0] < 0:
            return out^
        var k = -1
        for j in range(m):
            if F[j + 1] < 0 and k < 0:
                k = j
        for v in range(F[0] // (-F[k + 1]) + 1):
            var sub = impose_nonneg(_subst_var(forms, k, aff_const(m, v)), idx)
            for r in range(len(sub)):
                out.append(sub[r].copy())
        return out^
    var a = F[p + 1]
    var R = aff_scale(F, -1)
    R[p + 1] = 0  # F = a n_p - R
    var n = len(forms)
    # R <= 0: F >= 0 throughout
    var with_a = forms.copy()
    with_a.append(aff_scale(R, -1))
    var regs_a = impose_nonneg(with_a, n)
    for r in range(len(regs_a)):
        out.append(_drop_tail(regs_a[r], n))
    # R >= 1: n_p >= ceil(R / a)
    var with_b = forms.copy()
    with_b.append(aff_sub(R, aff_const(m, 1)))
    with_b.append(R.copy())
    var regs_b = impose_nonneg(with_b, n)
    for r in range(len(regs_b)):
        var pieces = _residues(regs_b[r], n + 1, a, p)
        for q in range(len(pieces)):
            ref rc = pieces[q][n + 1]
            var repl = aff_const(m, 0)
            for k in range(1, m + 1):
                repl[k] = rc[k] // a
            repl[0] = -((-rc[0]) // a)  # ceil(rc0 / a)
            repl[p + 1] = 1
            var done = _subst_var(pieces[q], p, repl)
            if not aff_nonneg(done[idx]):
                raise Error("impose_nonneg: the imposed form is not coefficientwise nonnegative")
            out.append(_drop_tail(done, n))
    return out^


struct Carved(Copyable, Movable):
    var inside: List[List[List[Int]]]
    var outside: List[List[List[Int]]]

    def __init__(out self):
        self.inside = List[List[List[Int]]]()
        self.outside = List[List[List[Int]]]()


def carve(forms: List[List[Int]], first: Int, count: Int, keep: Int) raises -> Carved:
    """Partition by the forms `first .. first + count - 1`: the regions where
    all are nonnegative (with every form kept), and the rest, region `j`
    being where the first `j` hold and form `j` is negative (slots only)."""
    var out = Carved()
    out.inside.append(forms.copy())
    for j in range(count):
        var idx = first + j
        var next = List[List[List[Int]]]()
        for r in range(len(out.inside)):
            ref f = out.inside[r]
            var neg = f.copy()
            var g = aff_scale(f[idx], -1)
            g[0] -= 1
            neg.append(g^)
            var outs = impose_nonneg(neg, len(neg) - 1)
            for q in range(len(outs)):
                out.outside.append(_drop_tail(outs[q], keep))
            var ins = impose_nonneg(f, idx)
            for q in range(len(ins)):
                next.append(ins[q].copy())
        out.inside = next^
    return out^


def point_subst(forms: List[List[Int]], ns: List[Int]) -> List[List[Int]]:
    """The slot values of a region at the point `ns`, as forms without variables."""
    var out = List[List[Int]]()
    for k in range(len(forms)):
        out.append(aff_const(0, aff_eval(forms[k], ns)))
    return out^


def _member_at(pat: RunPattern, subst: List[List[Int]], ns: List[Int], mut screen: CubicScreen) raises -> Bool:
    var sigma = pattern_family(pat, point_subst(subst, ns)).instantiate(List[Int]())
    var mat = Mat3(substitution_incidence(sigma))
    return abs(mat.det()) == 2 and screen.is_pip(mat)


def _base_point(pat: RunPattern, subst: List[List[Int]], mut screen: CubicScreen) raises -> List[Int]:
    """A member point of the region, generic first: every live variable 2,
    then 1, then 3, then the origin and the unit points; empty if none of
    them is a member. A generic point keeps the certificate from exploiting a
    boundary value, so the carved region is a full cone, not a slice."""
    var m = len(subst[0]) - 1
    var tries = List[List[Int]]()
    for g in [2, 1, 3]:
        tries.append(List[Int](length=m, fill=g))
    tries.append(List[Int](length=m, fill=0))
    for k in range(m):
        var e = List[Int](length=m, fill=0)
        e[k] = 1
        tries.append(e^)
    for t in range(len(tries)):
        if _member_at(pat, subst, tries[t], screen):
            return tries[t].copy()
    return List[Int]()



def _guided_bag(slots: List[List[Int]], ineqs: List[List[Int]], steps: List[WitnessStep]) -> List[List[Int]]:
    """Slots, then the forms to carve by, then each step's two offsets."""
    var bag = slots.copy()
    for k in range(len(ineqs)):
        bag.append(ineqs[k].copy())
    for k in range(len(steps)):
        bag.append(steps[k].off_a.copy())
        bag.append(steps[k].off_b.copy())
    return bag^


def _steps_from_bag(bag: List[List[Int]], first: Int, steps: List[WitnessStep]) -> List[WitnessStep]:
    var out = List[WitnessStep]()
    for k in range(len(steps)):
        out.append(WitnessStep(steps[k].seg_a, bag[first + 2 * k].copy(), steps[k].seg_b, bag[first + 2 * k + 1].copy()))
    return out^


def cover_pattern_guided(pat: RunPattern, s: Int, delta: Int, region_budget: Int, tail: Bool = False, verbose: Bool = False) raises -> ShapeCover:
    """Cover the pattern's members in one delta cell by certificate-guided
    partition: at a member point of each region find a certificate (an exact
    line-mode path, else a Lemma X closure), lift it, carve out the regions
    where it holds -- each re-verified by the ordinary verifier -- and go on
    with the rest. Regions left at the budget are reported open."""
    var out = ShapeCover()
    var screen = CubicScreen()
    var m = pat.slots() + (1 if tail else 0)
    var stack = _pattern_starts(pat, s, delta, tail)
    while len(stack) > 0:
        var reg = stack.pop()
        out.regions += 1
        if out.regions > region_budget:
            out.open += 1 + len(stack)
            out.budget_exhausted = True
            break
        if pisot_cut(pattern_counts(pat, reg), s):
            out.cut += 1
            continue
        var any_live = False
        var first_live = -1
        for k in range(m):
            if _live(reg, k):
                any_live = True
                if first_live < 0:
                    first_live = k
        var ns = _base_point(pat, reg, screen)
        if len(ns) == 0:
            if not any_live:
                out.not_member += 1
                continue
            stack.append(_set_value(reg, first_live, 0))
            var shifted = List[List[Int]]()
            for k in range(len(reg)):
                var f = reg[k].copy()
                f[0] += f[first_live + 1]
                shifted.append(f^)
            stack.append(shifted^)
            continue
        var fam = pattern_family(pat, reg)
        var point = pattern_family(pat, point_subst(reg, ns))
        var done = False
        # an exact line-mode path at the point
        var wp = search_witness_line(point, O, Y, OFFSET_BOUND, MAX_LEVEL, Y, Z)
        if wp.found:
            var lr = lift_path(fam, point, ns, O, Y, wp.steps, OFFSET_BOUND, Y, Z)
            if lr.ok and lr.a == lr.b:
                var ineqs = lr.ineqs.copy()
                for i in range(3):
                    if not _is_zero_form(lr.gamma[i]):
                        ineqs.append(lr.gamma[i].copy())
                        ineqs.append(aff_scale(lr.gamma[i], -1))
                var bag = _guided_bag(reg, ineqs, lr.steps)
                var cv = carve(bag, len(reg), len(ineqs), len(reg))
                if verbose:
                    _trace(out.regions, "path", ns, reg, ineqs, len(cv.inside), len(cv.outside))
                for q in range(len(cv.inside)):
                    var slots_in = _drop_tail(cv.inside[q], len(reg))
                    var steps_in = _steps_from_bag(cv.inside[q], len(reg) + len(ineqs), lr.steps)
                    if not verify_witness_line(pattern_family(pat, slots_in), O, Y, steps_in):
                        raise Error("a carved region does not verify its lifted path")
                    out.certified += 1
                    out.line_certified += 1
                    out.max_level = max(out.max_level, len(steps_in))
                for q in range(len(cv.outside)):
                    stack.append(cv.outside[q].copy())
                done = True
        if not done:
            var cp = search_crossing(point, O, Y, OFFSET_BOUND, MAX_LEVEL - 2, Y, Z, Y, Z)
            if cp.found:
                var lr = lift_path(fam, point, ns, O, Y, cp.steps, OFFSET_BOUND, Y, Z)
                var ineqs = lr.ineqs.copy()
                if lr.ok and crossing_conditions(fam, lr.a, lr.b, lr.gamma, Y, Z, cp.close[0], ns, ineqs):
                    var bag = _guided_bag(reg, ineqs, lr.steps)
                    var cv = carve(bag, len(reg), len(ineqs), len(reg))
                    if verbose:
                        _trace(out.regions, "crossing", ns, reg, ineqs, len(cv.inside), len(cv.outside))
                    for q in range(len(cv.inside)):
                        var slots_in = _drop_tail(cv.inside[q], len(reg))
                        var steps_in = _steps_from_bag(cv.inside[q], len(reg) + len(ineqs), lr.steps)
                        if not verify_crossing(pattern_family(pat, slots_in), O, Y, steps_in, cp.close[0], Y, Z):
                            raise Error("a carved region does not verify its lifted crossing")
                        out.certified += 1
                        out.crossing_certified += 1
                        out.max_level = max(out.max_level, len(steps_in) + 2)
                    for q in range(len(cv.outside)):
                        stack.append(cv.outside[q].copy())
                    done = True
        if not done:
            out.open += 1
            out.open_forms.append(reg.copy())
    return out^


def _form_str(f: List[Int]) -> String:
    var out = String(f[0])
    for k in range(1, len(f)):
        if f[k] != 0:
            out += (" +" if f[k] > 0 else " ") + String(f[k]) + "n" + String(k - 1)
    return out


def _trace(index: Int, kind: String, ns: List[Int], reg: List[List[Int]], ineqs: List[List[Int]], inside: Int, outside: Int):
    var line = "  #" + String(index) + " " + kind + " at"
    for k in range(len(ns)):
        line += " " + String(ns[k])
    line += " | slots"
    for k in range(len(reg)):
        line += " [" + _form_str(reg[k]) + "]"
    line += " | carve by"
    for k in range(len(ineqs)):
        if not aff_nonneg(ineqs[k]):
            line += " {" + _form_str(ineqs[k]) + " >= 0}"
    line += " -> in " + String(inside) + ", out " + String(outside)
    print(line, flush=True)


def _is_zero_form(f: List[Int]) -> Bool:
    for k in range(len(f)):
        if f[k] != 0:
            return False
    return True


def suffix_roots(s: Int, delta: Int) -> List[RunPattern]:
    """The run-tree roots of a delta cell with the longer word's suffix made
    explicit. s = +1: w_1 = u y^Delta (Lemma Phi5). s = -1: w_2 = v x with
    |x| = 2 - Delta and at least two z in x (Lemma Phi5'). A non-crossing
    member lies under exactly one root; a crossing one is Lemma Phi2's."""
    var out = List[RunPattern]()
    if s == 1:
        var suf = List[Int]()
        for _ in range(delta):
            suf.append(Y)
        out.append(RunPattern(List[Int]([Z]), True, List[Int](), True, suf^, List[Int]()))
        return out^
    var words = _words(2 - delta)
    for k in range(len(words)):
        if len(words[k]) != 2 - delta:
            continue
        var zs = 0
        for j in range(len(words[k])):
            zs += 1 if words[k][j] == Z else 0
        if zs >= 2:
            out.append(RunPattern(List[Int]([Z]), True, List[Int](), True, List[Int](), words[k].copy()))
    return out^


def run_tree_guided(s: Int, delta: Int, max_runs: Int, budget: Int, verbose: Bool = False) raises -> List[RunTreeLeaf]:
    """The run tree of one delta cell under its suffix roots, each pattern
    covered by certificate-guided partition."""
    var out = List[RunTreeLeaf]()
    var stack = suffix_roots(s, delta)
    while len(stack) > 0:
        var pat = stack.pop()
        var c = cover_pattern_guided(pat, s, delta, budget)
        if c.open == 0:
            if verbose:
                print("    closed ", pat, "  regions", c.regions, " certified", c.certified, " (line", c.line_certified, ", crossing", c.crossing_certified, ") cut", c.cut, " not member", c.not_member, flush=True)
            out.append(RunTreeLeaf(pat.copy(), True, 0, c.certified, c.cut))
            continue
        var kids = refine_pattern(pat)
        if pat.runs() >= max_runs or len(kids) == 0:
            if verbose:
                print("    OPEN   ", pat, "  regions", c.regions, " open", c.open, " budget" if c.budget_exhausted else "", flush=True)
            out.append(RunTreeLeaf(pat.copy(), False, c.open, c.certified, c.cut))
            continue
        if verbose:
            print("    refine ", pat, "  (open", c.open, ")", flush=True)
        for k in range(len(kids)):
            stack.append(kids[k].copy())
    return out^
