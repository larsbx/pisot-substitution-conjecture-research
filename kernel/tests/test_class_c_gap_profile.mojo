"""Class-C finite profile: frozen tail label sets across gaps, controls, domain pins, refusals."""
from std.testing import assert_true, assert_equal
from mojo_smoke.claims import require_contract
from psc.class_c_gap_profile import c_block, c_member, frozen_onset, rows_of, vertices_of


def refuses(d: Int, eps: Int, n: Int) -> Bool:
    try:
        _ = c_member(d, eps, n)
    except:
        return True
    return False


def main() raises:
    for eps in [1, -1]:
        var size = 196 if eps == 1 else 214
        var common = rows_of(c_block(6, eps, frozen_onset(6, eps)))
        for d in [6, 9, 12]:
            for extra in [0, 3]:
                var block = c_block(d, eps, frozen_onset(d, eps) + extra)
                assert_equal(vertices_of(block), size)
                assert_true(rows_of(block) == common)
            # Negative control: the member just below the onset has another label set.
            var below = c_block(d, eps, frozen_onset(d, eps) - 1)
            assert_true(rows_of(below) != common)
    # Domain starts: plus 2d-5, minus 2d+1 (screened refusals just below).
    assert_true(c_block(6, 1, 6).startswith("S 6 the characteristic polynomial"))
    assert_true(c_block(6, 1, 7).startswith("M 7 2432 "))
    assert_true(c_block(6, -1, 12).startswith("S 12 the characteristic polynomial"))
    assert_true(c_block(6, -1, 13).startswith("M 13 1283 "))
    # Refusals: sign, budget, normal form.
    assert_true(refuses(6, 0, 20))
    assert_true(refuses(6, 1, 401))
    assert_true(refuses(6, -1, 6))
    require_contract("class C (n+d,n,n-d+eps) finite profile: label sets equal on the observed frozen tail (4d plus, 4d+4 minus) across gaps 6/9/12 with 196/214 vertices, below-onset negative controls, PIP domain starts 2d-5/2d+1, screening-only skips, refusals; no uniform claim")
