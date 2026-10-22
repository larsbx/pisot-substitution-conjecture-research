"""True all-parameter carrier components: exact Bernstein and seed controls."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_typed_carrier import template_rows
from psc.class_a_uniform_geometry import (
    certify_uniform_components, certify_uniform_components_rows,
    canonical_seeds, _strict_positive_fifth, _uniform_seed_in_rows,
)


def main() raises:
    assert_equal(certify_uniform_components(),List[Int]([89,178,9,40,115]))
    var rows=template_rows()
    var seeds=canonical_seeds()
    for seed in seeds:
        assert_true(_uniform_seed_in_rows(rows,seed))
    # The actual endpoint margins are all strictly positive; zero and
    # negative functions must not be silently accepted.
    for poly in [List[Int]([0,0,0,0]),List[Int]([0,-1,0,0]),
                 List[Int]([-1,0,0,0])]:
        var rejected=False
        try:
            _strict_positive_fifth(poly)
        except:
            rejected=True
        assert_true(rejected)
    _strict_positive_fifth(List[Int]([0,1,0,0]))  # h>0
    _strict_positive_fifth(List[Int]([1,-5,0,0]))  # 1-5h>0
    # A duplicated row cannot masquerade as a candidate.
    var corrupted=template_rows()
    corrupted[0]=corrupted[1].copy()
    var rejected=False
    try:
        _=certify_uniform_components_rows(corrupted)
    except:
        rejected=True
    assert_true(rejected)
    # Uniform seed coverage fails on a missing singleton slice.
    var missing=List[List[Int]]()
    for i in range(len(rows)):
        if not (rows[i][0]==2 and rows[i][1]==2 and rows[i][2]==-1 and rows[i][3]==0):
            missing.append(rows[i].copy())
    assert_true(not _uniform_seed_in_rows(missing,List[Int]([2,2,0,-1,0])))
    require_contract("class-A n>=4 uniform typed carrier components: 178 exact Bernstein-certified strict margins, all nine swap seeds, pairwise disjoint nonempty 89 affine intervals of size 40n+115, zero/negative margin and corrupted-row/seed refusals; no all-child closure or hitting promoted")
