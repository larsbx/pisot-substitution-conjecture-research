"""Exact two-parameter rank-spine transport; no cover-closure claim."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_d_positive_b_spine import verify_minus_positive_b_spine


def main() raises:
    var out = verify_minus_positive_b_spine()
    assert_equal(out[0], 145)
    assert_equal(out[1], 6)
    assert_equal(out[2], 129)
    assert_equal(out[3], 4)
    assert_equal(out[4], 6)
    assert_equal(out[5], 4)
    assert_equal(out[1]+out[2]+out[3]+out[4], 145)
    require_contract(
        "minus class-D positive-b rank spine: all 139 non-target sealed labels "
        "have an occurrence-labelled strict rank descent for every a>=2,b>=1; "
        "129 direct transports, four alternate edges, six explicit y/y cases; "
        "cover closure is a separate obligation"
    )


if __name__ == "__main__":
    main()
