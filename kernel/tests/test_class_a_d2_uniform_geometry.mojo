"""All-parameter candidate geometry and nine-seed checks; NOT all-child closure."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_d2_parity_carrier import inferred_template
from psc.class_a_d2_uniform_geometry import (
    certify_uniform_d2_geometry, certify_rows, canonical_seeds,
    _strict_on_root_interval, _contains_uniform_seed,
)


def main() raises:
    certify_uniform_d2_geometry()
    var even=inferred_template(8,12)
    var odd=inferred_template(9,13)
    assert_equal(certify_rows(even,0),List[Int]([93,186,82,9,40,105]))
    assert_equal(certify_rows(odd,1),List[Int]([87,174,80,9,40,111]))
    var seeds=canonical_seeds()
    for seed in seeds:
        assert_true(_contains_uniform_seed(even,4,seed))
        assert_true(_contains_uniform_seed(odd,3,seed))
    # Neither touching nor negative margin can certify strict geometry.
    for q in [8,9]:
        for poly in [List[Int]([0,0,0,0]),List[Int]([-1,0,0,0])]:
            var refused=False
            try:
                _strict_on_root_interval(poly,q)
            except:
                refused=True
            assert_true(refused)
        _strict_on_root_interval(List[Int]([0,1,0,0]),q)
    # A source row perturbation cannot silently change the formal cardinality.
    var mutated=even.copy()
    var first=mutated[0].copy()
    first[7]+=20
    mutated[0]=first
    var rejected=False
    try:
        _=certify_rows(mutated,0)
    except:
        rejected=True
    assert_true(rejected)
    # Explicit parity swapping violates the arithmetic-root/row contract.
    rejected=False
    try:
        _=certify_rows(even,1)
    except:
        rejected=True
    assert_true(rejected)
    require_contract("class-A d2 uniform-in-n parity candidate strict Perron geometry: even n>=8 93 rows/186 margins/82 slices, odd n>=7 87 rows/174 margins/80 slices, all nine canonical strict swap seeds, cardinalities 40m+105 and 40m+111, zero/negative margin and damaged/cross-parity refusals; no all-child closure or hitting claim")
