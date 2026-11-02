"""Actual multi-level prefix carry versus independent full-prefix computation."""

from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_madic_digits import apply_incidence, in_image_power
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_prefix_carry import (
    actual_prefix_corrections, exact_prefix_pair_carry,
    unique_actual_zero_parent, replay_actual_zero_overlap_path,
)
from psc.class_a_boundary_children import _prefix


def level_two_prefix(k: Int, t: Int, sigma: List[List[Int]],
                     parent: Int, i: Int, j: Int) raises -> List[Int]:
    var n=k+t+3
    var d=k+2*t+5
    var outer=_prefix(-1,n,d,parent,i)
    var inner=_prefix(-1,n,d,sigma[parent][i],j)
    var inflated=apply_incidence(k,t,outer)
    return [inflated[0]+inner[0],inflated[1]+inner[1],
            inflated[2]+inner[2]]


def main() raises:
    var accepted=0
    var failed_low=0
    var failed_high=0
    var examined=0
    for k in range(2):
        var t=0
        var n=k+t+3
        var d=k+2*t+5
        var sigma=class_member(CLASS_A,n+d,n,n-1)
        for a in range(3):
            for b in range(3):
                for i in range(len(sigma[a])):
                    for j in range(len(sigma[sigma[a][i]])):
                        var first=level_two_prefix(k,t,sigma,a,i,j)
                        var top_path: List[Int] = [i,j]
                        for r in range(len(sigma[b])):
                            for s in range(len(sigma[sigma[b][r]])):
                                var bottom_path: List[Int] = [r,s]
                                var second=level_two_prefix(k,t,sigma,b,r,s)
                                var diff: List[Int] = [
                                    first[0]-second[0],
                                    first[1]-second[1],
                                    first[2]-second[2],
                                ]
                                var actual=in_image_power(k,t,diff,2)
                                var got=exact_prefix_pair_carry(
                                    k,t,a,b,top_path,bottom_path
                                )
                                assert_true(actual==got.valid)
                                assert_equal(got.depth,2)
                                if got.valid:
                                    var unique=unique_actual_zero_parent(
                                        k,t,a,b,top_path,bottom_path
                                    )
                                    var replay=apply_incidence(
                                        k,t,apply_incidence(k,t,unique)
                                    )
                                    for z in range(3):
                                        assert_equal(replay[z],diff[z])
                                        assert_equal(got.parent[z],unique[z])
                                    accepted+=1
                                elif got.first_failure==0:
                                    failed_low+=1
                                else:
                                    assert_equal(got.first_failure,1)
                                    failed_high+=1
                                examined+=1
    assert_true(accepted>0 and failed_low>0 and failed_high>0)
    # Independently reconstructed literal sigma^2/Cramer counts.
    assert_equal(examined,31429)
    assert_equal(accepted,11645)
    assert_equal(failed_low,8766)
    assert_equal(failed_high,11018)

    var first: List[Int] = [0,0]
    var other: List[Int] = [1,0]
    var local=actual_prefix_corrections(0,0,0,0,first,other)
    # Both deepest occurrence digits are FIRST (zero); the higher
    # actual prefix difference is -e_x and violates parity.
    assert_equal(local[0][0],0)
    assert_equal(local[0][1],0)
    assert_equal(local[0][2],0)
    var false_shortcut=exact_prefix_pair_carry(0,0,0,0,first,other)
    assert_true(not false_shortcut.valid)
    assert_equal(false_shortcut.first_failure,1)

    var refused=False
    var invalid: List[Int] = [999,0]
    try:
        _=exact_prefix_pair_carry(0,0,0,0,invalid,other)
    except:
        refused=True
    assert_true(refused)
    refused=False
    var malformed: List[Int] = [0]
    try:
        _=exact_prefix_pair_carry(0,0,0,0,first,malformed)
    except:
        refused=True
    assert_true(refused)
    # A uniform 2-level REAL typed coincidence path exists for this
    # specific oriented x/c occurrence pair exactly at even k.
    # This is a constructed formal source, NOT X/seed reachability.
    var outer_top: List[Int] = [0,1]
    var outer_bottom: List[Int] = [0,2]
    for k in range(5):
        for t in range(3):
            var n=k+t+3
            var d=k+2*t+5
            var result=exact_prefix_pair_carry(
                k,t,0,1,outer_top,outer_bottom
            )
            assert_true(result.valid==(k%2==0))
            if k%2!=0:
                assert_equal(result.first_failure,1)
                continue
            var pp=(d+3)//2
            var qq=n*d+2*n-1-(n+d)*pp
            var rr=(n+d)*pp-n*d-2*n-d-1
            assert_equal(result.parent[0],pp)
            assert_equal(result.parent[1],qq)
            assert_equal(result.parent[2],rr)
            var tables=build_seed_overlap_tables_screened(
                class_member(CLASS_A,n+d,n,n-1)
            )
            var path=replay_actual_zero_overlap_path(
                tables,k,t,0,1,outer_top,outer_bottom
            )
            assert_equal(len(path),3)
            assert_equal(path[0].top,0)
            assert_equal(path[0].bottom,1)
            assert_equal(path[1].top,0)
            assert_equal(path[1].bottom,1)
            assert_equal(path[1].x,1)
            assert_equal(path[1].c,-d-2)
            assert_equal(path[1].y,d+1)
            assert_equal(path[2].top,2)
            assert_equal(path[2].bottom,2)
            assert_equal(path[2].x,0)
            assert_equal(path[2].c,0)
            assert_equal(path[2].y,0)

    print("CLASS_A_ACTUAL_PREFIX_CARRY_PASS",examined,accepted,
          failed_low,failed_high)
    require_contract("Actual ordered level-two prefix-pair parity-carry soundness on complete finite member oracles; full index and depth checks; no param-uniform seed entry/BH")
