"""Class-A gaps d >= 5, both signs: assembly of the d-uniform regime certificates (#139).

For a sign `eps`, the fitted residue regimes (`psc.class_a_gap_regime_tables`)
cover every residue `r` of every gap `d >= D(eps)`, where `D(eps)` is the
largest fitted floor; `eventual_cover` proves the covering pattern once for all
`d >= D(eps)` and `residue_cover` lists it exactly for every smaller gap.
`certify_gap_theorem` then proves boundary hitting on every line
`(n+d, n, n+eps)` of gap `d >= 5` for every `n = d l + r` with `l >= l0`:

  * each regime from its registered uniform floor `d0` by the regime closure and
    descent (`psc.class_a_gap_uniform`), one certificate for all `l >= l0`, `d >= d0`;
  * each `(d, r)` of a regime with `fitted floor <= d < d0` by the ray closure
    and descent on the same tables from the least `l' >= l0` that certifies,
    and exact complete graphs for `l0 <= l < l'`;
  * each `(d, r)` below every fitted floor by its own ray tables
    (`psc.class_a_ray_tables`), again with exact graphs below the ray's floor.

Members with `l < l0` (`n < l0 d + r`) are outside this theorem for every gap
and are its recorded remaining gap. Source note:
docs/class-a-gap-uniform-certificate-design-2026-10-23.md.
"""
from psc.class_a_carrier_closure import certify_closure_line, ray_floor
from psc.class_a_carrier_descent import certify_descent_line
from psc.class_a_gap_regime_tables import (
    fitted_regimes, regime_of, regime_rows, regime_pieces, regime_descents, regime_floors,
)
from psc.class_a_gap_uniform import certify_regime
from psc.class_a_line import ALine
from psc.class_a_line_graph import survey
from psc.class_a_ray_tables import tabulated_rays, certify_ray
from psc.gap_form import Regime, KIND_LOW, KIND_HIGH, KIND_MIDDLE


comptime L_SEARCH = 8
comptime FIRST_GAP = 5


def regimes_of_sign(eps: Int) -> List[List[Int]]:
    var out = List[List[Int]]()
    for spec in fitted_regimes():
        if spec[0] == eps:
            out.append(spec.copy())
    return out^


def eventual_cover(eps: Int) raises -> Int:
    """The least `D` such that the fitted regimes of the sign cover every residue of every
    gap `d >= D`: the low regimes are `r = 0..J_low`, the high ones `r = d-1..d-J_high`,
    and the middle one `j0 <= r <= d - j1` with `j0 <= J_low + 1`, `j1 <= J_high + 1`;
    for `d >= D >= max(fitted floors, j0 + j1)` the three then tile `[0, d)`. Raises when
    the fitted regimes have no such pattern."""
    var low = List[Bool]()
    var high = List[Bool]()
    for _ in range(64):
        low.append(False)
        high.append(False)
    var j0 = -1
    var j1 = -1
    var floor_max = FIRST_GAP
    for spec in regimes_of_sign(eps):
        floor_max = max(floor_max, spec[4])
        if spec[1] == KIND_LOW:
            low[spec[2]] = True
        elif spec[1] == KIND_HIGH:
            high[spec[2]] = True
        elif spec[1] == KIND_MIDDLE:
            if j0 >= 0:
                raise Error("more than one middle regime for eps " + String(eps))
            j0 = spec[2]
            j1 = spec[3]
        else:
            raise Error("unknown regime kind")
    if j0 < 0:
        raise Error("no middle regime for eps " + String(eps))
    var j_low = -1
    while j_low + 1 < 64 and low[j_low + 1]:
        j_low += 1
    var j_high = 0
    while j_high + 1 < 64 and high[j_high + 1]:
        j_high += 1
    if j_low < 0 or j_high < 1:
        raise Error("no low or no high regime for eps " + String(eps))
    if j0 > j_low + 1 or j1 > j_high + 1:
        raise Error("the middle regime leaves residues uncovered for large gaps (eps " + String(eps) + ")")
    return max(floor_max, j0 + j1)


def residue_cover(eps: Int, d: Int) raises -> List[Int]:
    """For every residue `r` of gap `d`: the index into `fitted_regimes()` of the first
    regime fitted at `d` that contains `r`, else `-2 - i` for the `i`-th tabulated ray
    `(d, eps, r)`; raises when neither exists."""
    var specs = fitted_regimes()
    var rays = tabulated_rays()
    var out = List[Int]()
    for r in range(d):
        var found = -1
        for i in range(len(specs)):
            if specs[i][0] == eps and specs[i][4] <= d and regime_of(specs[i], 1).contains(1, d, r):
                found = i
                break
        if found < 0:
            for i in range(len(rays)):
                if rays[i][0] == d and rays[i][1] == eps and rays[i][2] == r:
                    found = -2 - i
                    break
        if found == -1:
            raise Error("residue " + String(r) + " of gap " + String(d) + " (eps " + String(eps) + ") is covered by no regime and no ray table")
        out.append(found)
    return out^


def _exact_graphs(line: ALine, l_from: Int, l_to: Int) raises -> Int:
    """Exact complete graphs (cap-refusing, every vertex hitting) for `l_from <= l < l_to`."""
    for l in range(l_from, l_to):
        _ = survey(line, line.n_of(l))
    return max(0, l_to - l_from)


def _finite_ray(line: ALine, l0: Int, rows: List[List[Int]], pieces: List[List[Int]],
                descents: List[List[Int]]) raises -> Int:
    """The ray closure and descent on regime tables from the least `l' >= l0` accepting
    both, then exact graphs for `l0 <= l < l'`; returns the number of exact graphs."""
    var lp = l0
    while lp <= l0 + L_SEARCH:
        var n0 = line.n_of(lp)
        try:
            _ = certify_closure_line(line, n0, rows)
            _ = certify_descent_line(line, n0, rows, pieces, descents)
            return _exact_graphs(line, l0, lp)
        except e:
            print("RAY_FLOOR_PROBE line=" + line.name(), "l0=" + String(lp), "refused:", e)
            lp += 1
    raise Error("finite ray " + line.name() + " did not certify for any l0 <= " + String(l0 + L_SEARCH))


def certify_gap_theorem(eps: Int, l0: Int) raises -> List[Int]:
    """Boundary hitting on every class-A line of gap `d >= 5` and sign `eps`, for every
    `n = d l + r` with `l >= l0`, for `1 <= l0 <= 64`. This is the supported floor interface range;
    exact Bernstein denominator powers use unbounded rationals. A certificate
    from `l0` covers every larger mathematical floor. Returns `[regimes, finite rays,
    exceptional rays, exact graphs, largest finite gap]`."""
    if eps != 1 and eps != -1:
        raise Error("class-A line requires eps = +-1")
    if l0 < 1 or l0 > 64:
        raise Error("the theorem floor l0 must satisfy 1 <= l0 <= 64 (supported certificate floor range)")
    var cover_from = eventual_cover(eps)
    var specs = fitted_regimes()
    var floors = regime_floors()
    var rays = tabulated_rays()
    var regimes = 0
    var finite = 0
    var exceptional = 0
    var graphs = 0
    var d_finite = cover_from
    # Uniform floors: every regime of the sign has a registered floor, certified here.
    var uniform_floor = List[Int]()
    for i in range(len(specs)):
        uniform_floor.append(-1)
    for f in floors:
        for i in range(len(specs)):
            if specs[i][0] == f[0] and specs[i][1] == f[1] and specs[i][2] == f[2]:
                uniform_floor[i] = f[3]
    for i in range(len(specs)):
        if specs[i][0] != eps:
            continue
        if uniform_floor[i] < specs[i][4]:
            raise Error("regime without a registered uniform floor at or above its fitted floor")
        var reg = regime_of(specs[i], l0)
        reg.d0 = uniform_floor[i]
        _ = certify_regime(reg, regime_rows(reg), regime_pieces(reg), regime_descents(reg))
        regimes += 1
        d_finite = max(d_finite, uniform_floor[i])
    # Every gap below the largest uniform floor, residue by residue.
    for d in range(FIRST_GAP, d_finite):
        var cover = residue_cover(eps, d)
        for r in range(d):
            var line = ALine(d, eps, r)
            var c = cover[r]
            if c >= 0:
                if uniform_floor[c] <= d:
                    continue   # inside the regime's uniform certificate
                var reg = regime_of(specs[c], l0)
                graphs += _finite_ray(line, l0, regime_rows(reg), regime_pieces(reg), regime_descents(reg))
                finite += 1
            else:
                var ray = rays[-2 - c].copy()
                var n0 = ray[3]
                _ = certify_ray(line, n0)
                var lp = ray_floor(line, n0)
                if lp < l0:
                    lp = l0
                graphs += _exact_graphs(line, l0, lp)
                exceptional += 1
    print("CLASS_A_GAP_THEOREM eps=" + String(eps), "l>=" + String(l0), "d>=" + String(FIRST_GAP),
          "regimes", regimes, "regimes_cover_from_d", cover_from, "finite_rays", finite,
          "exceptional_rays", exceptional, "exact_graphs", graphs, "universal_139=false")
    return [regimes, finite, exceptional, graphs, d_finite]
