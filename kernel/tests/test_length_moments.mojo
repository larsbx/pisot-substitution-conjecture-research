"""Occurrence-sensitive length windows, with sharp and singular controls."""
from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int, q_is_zero
from finite_linear_algebra.qlinalg import matvec, rank, is_zero_vec
from substitution_dynamics.substitution import Substitution
from psc.length_moments import LengthMomentTables, observation_rows, replay_moment_address
from psc.coincidence_formula import coincidence_witness, pair_paths
from psc.dumont_thomas import max_image_length
from psc.overlap_seed_patch import build_seed_overlap_tables
from psc.occurrence_path import SwapOccurrence, search_overlap_path, CERTIFIED_LIFTABLE_TARGET_PATH


def main() raises:
    var sigma: List[List[Int]] = [[0,2,2,2,2,1], [1,2,2,2,0], [1,2,1]]
    # This validates the actual PIP specimen through the canonical exact screen.
    _ = build_seed_overlap_tables(sigma)
    var tables = LengthMomentTables(sigma)
    var substitution = Substitution.checked(sigma)
    assert_equal(sigma[0][0],0)
    assert_equal(sigma[1][0],1)
    for k in range(1,4):
        assert_equal(sigma[0][k],2)
        assert_equal(sigma[1][k],2)
    # Fixed rays start with the same yyy block at position 1. Its descendants
    # start at 6 and 5, then 23 and 20: equality of words is not same-position
    # inflation. No bad/nonproductive hub hypothesis is asserted here.
    var drift = tables.moments([-1,1,0])
    for j in range(3):
        assert_true(drift[j].eq(q_int([0,-1,-3][j])))
        assert_equal(len(substitution.apply_n([1],j))-len(substitution.apply_n([0],j)),[0,-1,-3][j])
    print("FIXED_RAY_BLOCK_DRIFT verified=(0,-1,-3)")
    # A nonzero integer defect with zero first TWO observations: sharp window.
    var near = tables.moments([2,-3,1])
    assert_true(q_is_zero(near[0]) and q_is_zero(near[1]))
    assert_true(near[2].eq(q_int(-1)))
    print("TWO_LEVEL_FALSE_POSITIVE verified=(0,0,-1)")
    # An independent accepted Dumont-Thomas witness, replayed with the new
    # exact address semantics; all three pairs, not a universal census.
    for a in range(3):
        for b in range(a+1,3):
            var witness = coincidence_witness(sigma,a,b)
            assert_false(witness.empty)
            var paths = pair_paths(max_image_length(sigma),witness.word)
            var replay = replay_moment_address(tables,a,b,[0,0,0],paths[0],paths[1])
            assert_true(replay.coincidence())
            assert_true(is_zero_vec(replay.defect))
            print("ALIGNED_ADDRESS_REPLAY",a,b,len(paths[0]))
    # Offset zero with unequal letters is a BH target, not coincidence.
    var boundary = replay_moment_address(tables,0,1,[0,0,0],[],[])
    assert_true(boundary.boundary_hit())
    assert_false(boundary.coincidence())
    # A genuine nonzero-offset swap occurrence and its geometrically checked
    # path. The bottom second tile starts at e_1; both root tile types are 0.
    var found = search_overlap_path(sigma,SwapOccurrence(0,1,0,1),20,10000,1000000)
    assert_equal(found.status,CERTIFIED_LIFTABLE_TARGET_PATH)
    var top_path = List[Int]()
    var bottom_path = List[Int]()
    for i in range(len(found.edges)):
        top_path.append(found.edges[i].top_index)
        bottom_path.append(found.edges[i].bottom_index)
    var hit = replay_moment_address(tables,0,0,[0,1,0],top_path,bottom_path)
    assert_true(hit.coincidence())
    assert_true(is_zero_vec(hit.defect))
    print("NONZERO_SEED_ADDRESS_REPLAY",len(top_path))
    # Changing just the supplied root offset destroys the receipt.
    var corrupt = replay_moment_address(tables,0,0,[0,2,0],top_path,bottom_path)
    assert_false(corrupt.boundary_hit())
    # Proper occurrences, equal depths and a real budget are mandatory.
    var refused = 0
    for control in range(4):
        try:
            if control == 0:
                _ = replay_moment_address(tables,0,1,[0,0,0],[6],[0])
            elif control == 1:
                _ = replay_moment_address(tables,0,1,[0,0,0],[],[0])
            elif control == 2:
                _ = replay_moment_address(tables,0,1,[0,0,0],[0],[0],0)
            else:
                _ = replay_moment_address(tables,3,1,[0,0,0],[],[])
        except:
            refused += 1
    assert_equal(refused,4)
    # The return-period version works without materializing sigma^r words.
    for period in [1,2,3,7,64]:
        var powered = LengthMomentTables(sigma,period)
        assert_false(is_zero_vec(powered.moments([2,-3,1])))
        assert_true(is_zero_vec(powered.moments([0,0,0])))
    # Primitive, reducible constant-length control: all column sums are 3.
    var reducible: List[List[Int]] = [[1,0,2],[2,1,0],[0,2,1]]
    var obs = observation_rows(Substitution.checked(reducible))
    assert_equal(rank(obs),1)
    assert_true(is_zero_vec(matvec(obs,[q_int(1),q_int(-1),q_int(0)])))
    var singular_refused = False
    try:
        _ = LengthMomentTables(reducible)
    except:
        singular_refused = True
    assert_true(singular_refused)
    print("LENGTH_MOMENT_INTERFACE_CONTROLS_PASSED")
    require_contract("full-rank exact length windows replay supplied prefix occurrences; same-position drift and two-level false positives are retained; singular maps, malformed paths and budgets refuse; boundary hitting remains distinct from coincidence and universal existence")
