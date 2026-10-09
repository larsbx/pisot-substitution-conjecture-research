"""Exact regressions for the progression certificate (psc.progression_line).

docs/p1b-edge-progressions-2026-10-09.md. The index sets, their maps under
translation and reflection, and the far part the ranking must cover are
checked on constant intervals; Lemma EP's identity `M u = s u + k e_y` is
checked on the class A slope-1 line and refused for a vector that is not a
Lemma EP vector; the pinned progression rows are well formed. The full
certificate of each pinned row runs in the evidence workflow
(.github/workflows/class-b-lines-evidence.yml), against its pin.
"""

from std.testing import assert_equal, assert_false, assert_true
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract
from psc.progression_line import (
    Interval,
    ProgressionLine,
    normalize_set,
    set_far,
    set_has,
    set_key,
    set_map,
    set_subset,
    small_int,
)
from psc.symbolic_line import Eventual, qx_const
from symbolic_line_certificate import (
    CLASS_A,
    PROGRESSION_PIN_FIELDS,
    ClassLine,
    certified_progressions,
    part,
    progression_of,
)


def iv(lo: Int, hi: Int) -> Interval:
    return Interval(qx_const(lo), qx_const(hi))


def test_index_sets_merge_map_and_split() raises:
    var ev = Eventual()
    # adjacent integer intervals merge; order does not matter
    var merged = normalize_set(ev, [iv(3, 5), iv(0, 2), iv(9, 9)])
    assert_equal(set_key(merged), set_key([iv(0, 5), iv(9, 9)]))
    # translation j -> 2 + j and reflection j -> 3 - j
    assert_equal(set_key(set_map([iv(2, 5)], 2, 1)), set_key([iv(4, 7)]))
    assert_equal(set_key(normalize_set(ev, set_map([iv(2, 5)], 3, -1))), set_key([iv(-2, 1)]))
    # the far part |j| > j0 the ranking must cover
    assert_equal(set_key(set_far(ev, [iv(-4, 4)], 1)), set_key([iv(-4, -2), iv(2, 4)]))
    assert_equal(len(set_far(ev, [iv(-2, 2)], 2)), 0)
    assert_true(set_subset(ev, [iv(1, 2)], [iv(0, 5)]))
    assert_false(set_subset(ev, [iv(1, 7)], [iv(0, 5)]))
    assert_true(set_has(ev, merged, 4))
    assert_false(set_has(ev, merged, 7))


def test_small_int_is_exact() raises:
    assert_equal(small_int(q_int(-7)), -7)
    var refused = False
    try:
        _ = small_int(q_int(1).div(q_int(2)))
    except:
        refused = True
    assert_true(refused)


def test_lemma_ep_on_the_class_a_slope_one_line() raises:
    """(n + 1, n, n + 1): u = (1, -1, 0) with M u = u + e_y."""
    var spec = ClassLine(CLASS_A, [1, 1, 1, 0, 1, 1], True)
    var pl = ProgressionLine(spec.line(), [1, -1, 0], 1)
    assert_equal(pl.k, 1)
    assert_equal(pl.phi_index, 0)
    var refused = False
    try:
        _ = ProgressionLine(spec.line(), [1, 0, 0], 1)
    except:
        refused = True
    assert_true(refused)


def test_every_pinned_progression_is_well_formed() raises:
    var rows = certified_progressions()
    assert_true(len(rows) >= 1)
    for i in range(len(rows)):
        assert_equal(len(rows[i]), PROGRESSION_PIN_FIELDS)
        assert_true(rows[i][10] == 1 or rows[i][10] == -1)
        _ = progression_of(rows[i]).line()
        for j in range(i):
            assert_false(part(rows[i], 0, 11) == part(rows[j], 0, 11))


def main() raises:
    test_index_sets_merge_map_and_split()
    print("[PASS] test_index_sets_merge_map_and_split")
    test_small_int_is_exact()
    print("[PASS] test_small_int_is_exact")
    test_lemma_ep_on_the_class_a_slope_one_line()
    print("[PASS] test_lemma_ep_on_the_class_a_slope_one_line")
    test_every_pinned_progression_is_well_formed()
    print("[PASS] test_every_pinned_progression_is_well_formed")
    require_contract("progression certificate (Lemma EP): integer index sets with ends affine in q merge, translate, reflect and split exactly; M u = s u + k e_y is verified on the line (k = 1 for class A (n + 1, n, n + 1), u = (1, -1, 0)) and a vector that is not a Lemma EP vector is refused; every pinned progression row is well formed and distinct")
