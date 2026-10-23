"""The d-uniform regime closure: agreement with the ray closure, and refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_carrier_closure import certify_closure_line
from psc.class_a_gap_regime_tables import fitted_regimes, regime_of, regime_rows
from psc.class_a_gap_uniform import (
    certify_regime_closure, check_perron_bound, check_regime_identity, child_base, displacement_hu, regime_sign,
)
from psc.class_a_line import ALine
from psc.gap_form import GapForm, Regime, KIND_LOW, KIND_HIGH, KIND_MIDDLE
from psc.poly_hu import PolyHU


def spec_of(eps: Int, kind: Int, j: Int) raises -> List[Int]:
    for spec in fitted_regimes():
        if spec[0] == eps and spec[1] == kind and spec[2] == j:
            return spec.copy()
    raise Error("regime not fitted")


def refuses_closure(reg: Regime, rows: List[List[Int]]) -> Bool:
    try:
        _ = certify_regime_closure(reg, rows)
    except:
        return True
    return False


def main() raises:
    # Symbolic identities for both signs; a third sign refuses.
    for eps in [1, -1]:
        check_regime_identity(eps)
        check_perron_bound(eps)
    var bad = False
    try:
        check_regime_identity(0)
    except:
        bad = True
    assert_true(bad)
    # The child-index base splits n s = (d l + r) s into the l d and r coefficients.
    var low0 = regime_of(spec_of(-1, KIND_LOW, 0), 5)
    low0.d0 = 10
    var rows = regime_rows(low0)
    assert_equal(rows[0], List[Int]([0, 0, -1, -2, 0, 1, 0, 1]))
    assert_equal(child_base(low0, rows[0]), GapForm(2, 0, 1, -1, -1))
    # A displacement margin at a carrier member is positive; its negation negative.
    var t = displacement_hu(-1, rows[0][2], [rows[0][4], rows[0][5]], rows[0][3])
    var margin = displacement_hu(-1, 0, [0, 0], 0).sub(t)   # -T; T = -L_c + u(1+h) + 2h at k = 1, s = -1, y = -2
    assert_true(regime_sign(low0, margin) * regime_sign(low0, t) == -1)
    # The regime closure certifies for every l >= 5 and d >= 10, with the statistics of
    # the ray closure on the same rows at any single gap.
    var uniform = certify_regime_closure(low0, rows)
    var ray = certify_closure_line(ALine(12, -1, 0), 60, rows)
    for i in range(2, len(uniform)):
        assert_equal(uniform[i], ray[i])
    # Below the uniform floor a rounding varies with d: refused, not decided.
    var early = low0
    early.d0 = 9
    assert_true(refuses_closure(early, rows))
    # Negative controls on the table: a removed row, a shifted endpoint, another regime's rows.
    var fewer = List[List[Int]]()
    for i in range(1, len(rows)):
        fewer.append(rows[i].copy())
    assert_true(refuses_closure(low0, fewer))
    var shifted = rows.copy()
    shifted[7][7] += 1
    assert_true(refuses_closure(low0, shifted))
    var low1 = regime_of(spec_of(-1, KIND_LOW, 1), 5)
    low1.d0 = 10
    assert_true(refuses_closure(low0, regime_rows(low1)))
    # A middle regime with an empty floor refuses at check().
    var empty = Regime(-1, KIND_MIDDLE, 3, 4, 5, 6)
    assert_true(refuses_closure(empty, rows))
    require_contract("class-A d-uniform regime closure: on the fitted minus low r=0 rows the regime certificate proves forward closure for every l>=5 and every gap d>=10 with the ray closure's statistics; symbolic Perron identities for both signs; the child-index base is d k_lo + n s + eps y; a floor where a rounding varies, a removed row, a shifted endpoint, another regime's rows and an empty middle regime refuse")
