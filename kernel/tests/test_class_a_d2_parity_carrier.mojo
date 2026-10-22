"""Exact d=2 finite parity profile discovery, source pairs, and refusals."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_d2_parity_carrier import (
    specimen, exact_profile, inferred_template, certify_finite_parity,
)


def main() raises:
    var even=inferred_template(8,12)
    var odd=inferred_template(9,13)
    assert_equal(len(even),93)
    assert_equal(len(odd),87)
    assert_equal(len(exact_profile(4)),87)
    assert_equal(len(exact_profile(5)),85)
    assert_equal(len(exact_profile(6)),91)
    assert_equal(len(exact_profile(7)),87)
    assert_equal(certify_finite_parity(8,even),List[Int]([93,265]))
    assert_equal(certify_finite_parity(10,even),List[Int]([93,305]))
    assert_equal(certify_finite_parity(14,even),List[Int]([93,385]))
    assert_equal(certify_finite_parity(9,odd),List[Int]([87,271]))
    assert_equal(certify_finite_parity(11,odd),List[Int]([87,311]))
    assert_equal(certify_finite_parity(15,odd),List[Int]([87,391]))
    # An odd template must not be misapplied to an even specimen.
    var refused=False
    try:
        _=certify_finite_parity(8,odd)
    except:
        refused=True
    assert_true(refused)
    # Neither n=4 nor n=5 agrees with its later stable-parity profile.
    for n in [4,5]:
        refused=False
        try:
            if n%2==0:
                _=certify_finite_parity(n,even)
            else:
                _=certify_finite_parity(n,odd)
        except:
            refused=True
        assert_true(refused)
    for n in [3,33]:
        refused=False
        try:
            _=specimen(n)
        except:
            refused=True
        assert_true(refused)
    refused=False
    try:
        _=inferred_template(8,13)
    except:
        refused=True
    assert_true(refused)
    var damaged=even.copy()
    var first=damaged[0].copy()
    first[5]+=1
    damaged[0]=first.copy()
    refused=False
    try:
        _=certify_finite_parity(14,damaged)
    except:
        refused=True
    assert_true(refused)
    require_contract("class-A d=2 finite-only even/odd typed interval candidates: 93 even n>=8 and 87 odd n>=7 rows inferred from exact paired source graphs, checked against fresh finite complete graphs; strict cap, parity, transient prefix and changed-row refusals; no universal carrier, closure, descent or hitting theorem")
