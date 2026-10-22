"""The class-A d=2 plus line (n+2,n,n+1): boundary hitting for every n>=1, assembled and shown.

    sigma_n(x) = x y^(n+2) x,   sigma_n(c) = c y^n x,   sigma_n(y) = x y^(n+1) c.

`theorem()` assembles the proof from its parts and prints one receipt per part:

  * finite base: exact complete swap-seed graphs for 1 <= n <= 12, every
    vertex with a finite first offset-zero depth (cap-refusing);
  * the two residue rays n = 2l + r of the registry `psc.class_a_ray_tables`,
    each forward closed and strictly descending from its floor (14, 13);
  * minimality of both floors: the certificate refuses two below each floor;
  * the ray carriers are, as exact affine tables, the #312 parity templates
    `psc.class_a_d2_parity_carrier.inferred_template` (8,12) and (9,13).

`witness(n)` shows the certificate at one n (floor <= n <= 24): for every
carrier label its piece, potential X, chosen ordered occurrence (i, j) and
child, re-derived by hand from the integral incidence identity

    w' = (k+s, s-k, n s + 2k + y) + prefix(sigma(bottom), j) - prefix(sigma(top), i),

with the child letters sigma(top)[i], sigma(bottom)[j]; that the label set is
exactly the vertex set of the exact complete graph; and the chosen path of
every canonical swap seed down to offset zero. Source note:
docs/class-a-d2-plus-rays-2026-10-22.md.
"""
from std.collections import Dict
from psc.class_a_line import ALine
from psc.class_a_line_graph import survey
from psc.class_a_ray_tables import tabulated_rays, ray_tables, certify_ray
from psc.class_a_carrier_descent import descent_witnesses_line
from psc.class_a_d2_parity_carrier import inferred_template
from psc.class_a_run_index import labelled
from psc.overlap_seed_patch import (
    OverlapState, build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables,
    seed_overlap_states,
)
from psc.vertex_coincidence import length_matrix, offset_vector


comptime FINITE_BASE_LAST = 12


def d2p(r: Int) raises -> ALine:
    if r != 0 and r != 1:
        raise Error("the d=2 plus line has residues r = 0, 1 only")
    return ALine(2, 1, r)


def ray_spec(r: Int) raises -> List[Int]:
    """`[d, eps, r, floor, cardinality slope, cardinality constant]` from the registry."""
    for spec in tabulated_rays():
        if spec[0] == 2 and spec[1] == 1 and spec[2] == r:
            return spec.copy()
    raise Error("d=2 plus ray is not tabulated")


def finite_base() raises -> Int:
    """Exact complete graphs for 1 <= n <= FINITE_BASE_LAST; returns the largest first-hit depth."""
    var deepest = 0
    for n in range(1, FINITE_BASE_LAST + 1):
        deepest = max(deepest, survey(d2p(n % 2), n)[1])
    print("D2P_FINITE_BASE n=1.." + String(FINITE_BASE_LAST), "all_vertices_hit=true max_first_hit", deepest)
    return deepest


def carrier_is_parity_template(r: Int) raises:
    """The ray rows equal the #312 template, row for row and coefficient for coefficient."""
    var rows = ray_tables(d2p(r))[0].copy()
    var template = inferred_template(8, 12) if r == 0 else inferred_template(9, 13)
    if len(rows) != len(template):
        raise Error("ray carrier and parity template differ in row count")
    for i in range(len(rows)):
        if rows[i] != template[i]:
            raise Error("ray carrier row " + String(i) + " differs from the parity template")
    print("D2P_CARRIER_IS_PARITY_TEMPLATE r=" + String(r), "rows", len(rows), "identical=true")


comptime UNDECIDED = "UNDECIDED sign"


def expected_floor_refusal(reason: String) raises -> String:
    """Only an undecided Perron sign counts as the below-floor refusal."""
    if reason.find(UNDECIDED) != 0:
        raise Error("unexpected refusal below the floor: " + reason)
    return reason


def floor_is_least(r: Int) raises:
    """Below the floor the certificate must refuse with an undecided Perron sign;
    a pass there would move the floor, and any other error is propagated rather
    than read as that refusal."""
    var spec = ray_spec(r)
    var below = spec[3] - 2
    var reason = String()
    try:
        _ = certify_ray(d2p(r), below)
    except e:
        reason = expected_floor_refusal(String(e))
    if not reason:
        raise Error("certificate accepted below the recorded floor: the floor is not least")
    print("D2P_FLOOR_LEAST r=" + String(r), "floor", spec[3], "refused_at", below, "reason=\"" + reason + "\"")


def theorem() raises:
    _ = finite_base()
    for r in range(2):
        _ = certify_ray(d2p(r), ray_spec(r)[3])
        floor_is_least(r)
        carrier_is_parity_template(r)
    print("CLASS_A_D2_PLUS_LINE_BOUNDARY_HITTING n>=1 line=(n+2,n,n+1) finite_base=1.." + String(FINITE_BASE_LAST),
          "rays=2l:" + String(ray_spec(0)[3]) + ",2l+1:" + String(ray_spec(1)[3]), "universal_139=false")


def _prefix(word: List[Int], i: Int) -> List[Int]:
    """Abelianization `(x, c, y)` of `word[0:i]`."""
    var v: List[Int] = [0, 0, 0]
    for t in range(i):
        v[word[t]] += 1
    return v^


def hand_step(sigma: List[List[Int]], n: Int, w: List[Int]) raises:
    """Re-derive a witness record's child from the incidence identity alone."""
    var top = w[0]
    var bottom = w[1]
    var k = w[2]
    var s = w[2] + w[3] + w[4]
    var i = w[7]
    var j = w[8]
    var pt = _prefix(sigma[top], i)
    var pb = _prefix(sigma[bottom], j)
    var child: List[Int] = [
        sigma[top][i], sigma[bottom][j],
        k + s + pb[0] - pt[0],
        s - k + pb[1] - pt[1],
        n * s + 2 * k + w[4] + pb[2] - pt[2],
    ]
    for t in range(5):
        if child[t] != w[9 + t]:
            raise Error("witness child disagrees with the incidence identity")


def _show(w: List[Int], at: Int) -> String:
    return ("(" + String(w[at]) + "," + String(w[at + 1]) + "," + String(w[at + 2]) + "," + String(w[at + 3])
            + "," + String(w[at + 4]) + ")")


def witness(n: Int, emit: Bool = True) raises -> List[Int]:
    """Returns `[labels, targets, seeds, longest seed path, longest chain]`."""
    var r = n % 2
    var line = d2p(r)
    if n < ray_spec(r)[3]:
        raise Error("below the ray floor the evidence is the exact graph (finite_base), not the certificate")
    var t = ray_tables(line)
    var records = descent_witnesses_line(line, n, t[0], t[1], t[2])
    var tables = build_seed_overlap_tables_screened(line.member(n))
    var index = Dict[OverlapState, Int]()
    var targets = 0
    for ri in range(len(records)):
        var w = records[ri].copy()
        index[labelled(tables, w[0], w[1], w[2], w[3], w[4])] = ri
        if w[7] < 0:
            targets += 1
            if emit:
                print("W", n, _show(w, 0), "X", w[6], "piece", w[5], "TARGET")
            continue
        hand_step(tables.sigma, n, w)
        if w[14] > w[6] - 1:
            raise Error("witness does not drop the potential")
        if emit:
            print("W", n, _show(w, 0), "X", w[6], "piece", w[5], "--(" + String(w[7]) + "," + String(w[8]) + ")->",
                  _show(w, 9), "X", w[14])
    # The label set is the vertex set of the exact complete graph.
    var g = build_seed_overlap_graph_from_tables(tables, 20000)
    if g.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no witness verdict")
    if g.size() != len(records):
        raise Error("carrier labels and complete graph vertices differ in number")
    for v in g.states:
        if v not in index:
            raise Error("complete graph vertex outside the carrier")
    # Chosen chains: every label reaches a target within its potential.
    var longest = 0
    for ri in range(len(records)):
        var at = ri
        var steps = 0
        while records[at][7] >= 0:
            var w = records[at].copy()
            at = index[labelled(tables, w[9], w[10], w[11], w[12], w[13])]
            steps += 1
        if steps > records[ri][6]:
            raise Error("chosen chain longer than the potential")
        longest = max(longest, steps)
    var seeds = 0
    var seed_longest = 0
    var lm = length_matrix(tables)
    for seed in seed_overlap_states(tables):
        var u = offset_vector(lm, seed.shift)
        var at = index[labelled(tables, seed.top, seed.bottom, u[0], u[1], u[2])]
        var path = "SEED " + String(n) + " " + _show(records[at], 0)
        var steps = 0
        while records[at][7] >= 0:
            var w = records[at].copy()
            path += " --(" + String(w[7]) + "," + String(w[8]) + ")-> " + _show(w, 9)
            at = index[labelled(tables, w[9], w[10], w[11], w[12], w[13])]
            steps += 1
        seeds += 1
        seed_longest = max(seed_longest, steps)
        if emit:
            print(path, "steps", steps)
    print("D2P_WITNESS", n, "labels", len(records), "targets", targets, "graph_vertices", g.size(), "seeds", seeds,
          "longest_seed_path", seed_longest, "longest_chain", longest, "hand_checked_steps", len(records) - targets)
    return [len(records), targets, seeds, seed_longest, longest]
