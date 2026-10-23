"""The d-uniform regime descent: generated pieces and descents certify from the floor, and refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_carrier_descent import certify_descent_line
from psc.class_a_gap_regime_tables import fitted_regimes, regime_of, regime_rows, regime_pieces, regime_descents
from psc.class_a_gap_uniform import certify_regime_descent
from psc.class_a_line import ALine
from psc.gap_form import Regime, KIND_LOW, KIND_HIGH, KIND_MIDDLE


def spec_of(eps: Int, kind: Int, j: Int) raises -> List[Int]:
    for spec in fitted_regimes():
        if spec[0] == eps and spec[1] == kind and spec[2] == j:
            return spec.copy()
    raise Error("regime not fitted")


def refuses(reg: Regime, rows: List[List[Int]], pieces: List[List[Int]], descents: List[List[Int]]) -> Bool:
    try:
        _ = certify_regime_descent(reg, rows, pieces, descents)
    except:
        return True
    return False


def main() raises:
    # The minus low r=0 regime: the descent generated from the sample ray d=5 certifies for
    # every l >= 5 and every gap d >= 5, with the statistics of the ray descent on the same
    # tables at the sample gap.
    var low0 = regime_of(spec_of(-1, KIND_LOW, 0), 5)
    var rows = regime_rows(low0)
    var pieces = regime_pieces(low0)
    var descents = regime_descents(low0)
    var uniform = certify_regime_descent(low0, rows, pieces, descents)
    var ray = certify_descent_line(ALine(5, -1, 0), 25, rows, pieces, descents)
    assert_equal(len(uniform), len(ray))
    for i in range(len(uniform)):
        assert_equal(uniform[i], ray[i])
    assert_true(uniform[0] > 100 and uniform[2] > uniform[0])
    # Negative controls: a removed descent row, a shifted piece end, a swapped child piece,
    # a descent row on the target piece, and a regime without generated tables.
    var fewer = List[List[Int]]()
    for i in range(1, len(descents)):
        fewer.append(descents[i].copy())
    assert_true(refuses(low0, rows, pieces, fewer))
    var shifted = pieces.copy()
    shifted[3][4] += 1
    assert_true(refuses(low0, rows, shifted, descents))
    var swapped = descents.copy()
    swapped[0][8] = (swapped[0][8] + 1) % len(pieces)
    assert_true(refuses(low0, rows, pieces, swapped))
    var onto_target = descents.copy()
    for pi in range(len(pieces)):
        var p = pieces[pi].copy()
        var row = rows[p[0]].copy()
        if row[2] == 0 and row[3] == 0 and p[1] == p[3] and p[2] == p[4] and row[4] + p[1] == 0 and row[5] + p[2] == 0:
            onto_target[0][0] = pi
            break
    assert_true(refuses(low0, rows, pieces, onto_target))
    # Every fitted regime of both signs has generated tables; an unfitted one refuses.
    for spec in fitted_regimes():
        var reg = regime_of(spec, 5)
        assert_true(len(regime_pieces(reg)) > 100 and len(regime_descents(reg)) > len(regime_pieces(reg)))
    var bad = False
    try:
        _ = regime_pieces(Regime(1, KIND_LOW, 7, 0, 5, 11))
    except:
        bad = True
    assert_true(bad)
    require_contract("class-A d-uniform regime descent: on the minus low r=0 regime the pieces and descent occurrences generated from the sample ray d=5 certify a strict affine potential descent for every l>=5 and every gap d>=5 with the ray descent's statistics; a removed descent row, a shifted piece end, a swapped child piece, a descent on the target piece and an unfitted regime refuse; every fitted regime of both signs has generated tables")
