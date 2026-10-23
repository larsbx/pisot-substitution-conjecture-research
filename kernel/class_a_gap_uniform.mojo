"""Class-A gaps d>=5: the d-uniform regime certificate on the fitted regime tables.

  mojo run -I . class_a_gap_uniform.mojo closure EPS KIND J L0 [D0]  # closure of one fitted regime, l>=L0, d>=D0 (default: the fitted floor)
  mojo run -I . class_a_gap_uniform.mojo closure-all L0            # every fitted regime of both signs
  mojo run -I . class_a_gap_uniform.mojo floor EPS KIND J L0 DMAX  # least d0 <= DMAX from which the regime closure certifies,
                                                                   # then the ray closure on the same rows for every (d, r) of the
                                                                   # regime with fitted floor <= d < d0
  mojo run -I . class_a_gap_uniform.mojo floor-all L0 DMAX
  mojo run -I . class_a_gap_uniform.mojo descent EPS KIND J L0 [D0]  # descent of one regime on its generated pieces/descents
  mojo run -I . class_a_gap_uniform.mojo descent-floor EPS KIND J L0 DMAX  # least d0 <= DMAX from which the regime descent certifies
  mojo run -I . class_a_gap_uniform.mojo certify EPS KIND J L0 [D0]  # closure and descent of one regime

Floors satisfy 1 <= L0, D0 <= 64 (`Regime.check`): the exact box denominators
`l0^p d0^q` of the Perron signs are Int64; a certificate from a floor covers
every larger one.
"""
from std.sys import argv
from psc.class_a_gap_uniform import certify_regime, certify_regime_closure, certify_regime_descent
from psc.class_a_gap_regime_tables import fitted_regimes, regime_of, regime_rows, regime_pieces, regime_descents
from psc.class_a_carrier_closure import certify_closure_line
from psc.class_a_line import ALine
from psc.class_a_line_graph import survey
from psc.gap_form import Regime, KIND_LOW, KIND_HIGH, KIND_MIDDLE


comptime L_SEARCH = 8


def residues_at(reg: Regime, d: Int) -> List[Int]:
    """The residues of gap `d` in the regime."""
    var out = List[Int]()
    for r in range(d):
        if reg.contains(reg.l0, d, r):
            out.append(r)
    return out^


def closure_floor(spec: List[Int], l0: Int, d_max: Int) raises -> Int:
    """Least `d0` in `[fitted floor, d_max]` from which the regime closure certifies;
    every `(d, r)` of the regime with `fitted floor <= d < d0` is then certified by the
    ray closure on the same rows. Returns `d0`; raises if none certifies by `d_max`."""
    var rows = regime_rows(regime_of(spec, l0))
    var fitted = spec[4]
    var d0 = fitted
    var found = False
    while d0 <= d_max:
        var reg = regime_of(spec, l0)
        reg.d0 = d0
        try:
            _ = certify_regime_closure(reg, rows)
            found = True
            break
        except e:
            print("REGIME_FLOOR_PROBE eps=" + String(spec[0]), "regime=" + reg.name(), "d0=" + String(d0), "refused:", e)
            d0 += 1
    if not found:
        raise Error("regime closure did not certify for any d0 <= " + String(d_max))
    var probe = regime_of(spec, l0)
    probe.d0 = fitted
    var finite = 0
    var graphs = 0
    for d in range(fitted, d0):
        for r in residues_at(probe, d):
            # The ray closure on the same rows from the least l' >= l0 that certifies;
            # members l0 <= l < l' are exact complete graphs (cap-refusing, every vertex hitting).
            var line = ALine(d, spec[0], r)
            var lp = l0
            var ok = False
            while lp <= l0 + L_SEARCH:
                try:
                    _ = certify_closure_line(line, d * lp + r, rows)
                    ok = True
                    break
                except e:
                    print("RAY_FLOOR_PROBE line=" + line.name(), "l0=" + String(lp), "refused:", e)
                    lp += 1
            if not ok:
                raise Error("finite ray " + line.name() + " did not certify for any l0 <= " + String(l0 + L_SEARCH))
            for l in range(l0, lp):
                _ = survey(line, d * l + r)
                graphs += 1
            finite += 1
    print("CLASS_A_REGIME_CLOSURE_FLOOR eps=" + String(spec[0]), "regime=" + probe.name(), "fitted_d>=" + String(fitted),
          "uniform_d>=" + String(d0), "finite_rays", finite, "exact_graphs", graphs, "l>=" + String(l0))
    return d0


def spec_for(eps: Int, kind: Int, j: Int) raises -> List[Int]:
    for spec in fitted_regimes():
        if spec[0] == eps and spec[1] == kind and spec[2] == j:
            return spec.copy()
    raise Error("no fitted regime for the given eps, kind, j")


def descent_floor(spec: List[Int], l0: Int, d_max: Int) raises -> Int:
    """Least `d0` in `[fitted floor, d_max]` from which the regime descent certifies."""
    var d0 = spec[4]
    while d0 <= d_max:
        var reg = regime_of(spec, l0)
        reg.d0 = d0
        try:
            _ = certify_regime_descent(reg, regime_rows(reg), regime_pieces(reg), regime_descents(reg))
            print("CLASS_A_REGIME_DESCENT_FLOOR eps=" + String(spec[0]), "regime=" + reg.name(), "fitted_d>=" + String(spec[4]),
                  "uniform_d>=" + String(d0), "l>=" + String(l0))
            return d0
        except e:
            print("REGIME_DESCENT_FLOOR_PROBE eps=" + String(spec[0]), "regime=" + reg.name(), "d0=" + String(d0), "refused:", e)
            d0 += 1
    raise Error("regime descent did not certify for any d0 <= " + String(d_max))


def main() raises:
    var args = argv()
    if (len(args) == 6 or len(args) == 7) and (args[1] == "descent" or args[1] == "certify"):
        var reg = regime_of(spec_for(Int(args[2]), Int(args[3]), Int(args[4])), Int(args[5]))
        if len(args) == 7:
            reg.d0 = Int(args[6])
        var rows = regime_rows(reg)
        if args[1] == "descent":
            _ = certify_regime_descent(reg, rows, regime_pieces(reg), regime_descents(reg))
        else:
            _ = certify_regime(reg, rows, regime_pieces(reg), regime_descents(reg))
        return
    if len(args) == 7 and args[1] == "descent-floor":
        _ = descent_floor(spec_for(Int(args[2]), Int(args[3]), Int(args[4])), Int(args[5]), Int(args[6]))
        return
    if (len(args) == 6 or len(args) == 7) and args[1] == "closure":
        var eps = Int(args[2])
        var kind = Int(args[3])
        var j = Int(args[4])
        for spec in fitted_regimes():
            if spec[0] == eps and spec[1] == kind and spec[2] == j:
                var reg = regime_of(spec, Int(args[5]))
                if len(args) == 7:
                    reg.d0 = Int(args[6])
                _ = certify_regime_closure(reg, regime_rows(reg))
                return
        raise Error("no fitted regime for the given eps, kind, j")
    if len(args) == 3 and args[1] == "closure-all":
        for spec in fitted_regimes():
            var reg = regime_of(spec, Int(args[2]))
            _ = certify_regime_closure(reg, regime_rows(reg))
        return
    if len(args) == 7 and args[1] == "floor":
        var eps = Int(args[2])
        var kind = Int(args[3])
        var j = Int(args[4])
        for spec in fitted_regimes():
            if spec[0] == eps and spec[1] == kind and spec[2] == j:
                _ = closure_floor(spec, Int(args[5]), Int(args[6]))
                return
        raise Error("no fitted regime for the given eps, kind, j")
    if len(args) == 4 and args[1] == "floor-all":
        for spec in fitted_regimes():
            _ = closure_floor(spec, Int(args[2]), Int(args[3]))
        return
    raise Error("usage: closure EPS KIND J L0 [D0] | closure-all L0 | floor EPS KIND J L0 DMAX | floor-all L0 DMAX"
                " | descent EPS KIND J L0 [D0] | descent-floor EPS KIND J L0 DMAX | certify EPS KIND J L0 [D0]")
