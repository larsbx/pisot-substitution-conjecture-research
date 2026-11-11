"""Exact local lifting, retained-set criteria and authenticated finite profiles.

These abstract finite-group countermodels do not instantiate Pisot geometry.
All fixture counts preserve actual mark positions and their multiplicity.
"""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.c4_bounded_cover import forward_leak_control
from psc.c4_local_admissibility import (
    CyclicModel, LocalAdmissibility, build_local_admissibility,
    verify_local_admissibility, validate_cyclic_model, local_fixture_model,
    local_fixture, local_summary, singular_fixture_model, singular_lift_control,
    cyclic_image, project_mask,
)


def _reject_inventory(inventory: LocalAdmissibility) raises:
    var refused = False
    try:
        verify_local_admissibility(inventory)
    except:
        refused = True
    assert_true(refused)


def _reject_model(model: CyclicModel) raises:
    var refused = False
    try:
        _ = build_local_admissibility(model)
    except:
        refused = True
    assert_true(refused)


def test_six_finite_model_boundaries() raises:
    var expected: List[List[Int]] = [
        [2,2,2,2,2,0,0,1,1,1,2,0],
        [2,8,8,2,2,6,0,0,0,1,0,0],
        [2,8,8,0,0,8,0,0,0,0,0,0],
        [2,2,2,2,0,0,2,1,0,0,3,0],
        [2,4,4,4,2,0,2,1,0,1,3,0],
        [6,6,4,2,2,2,0,1,1,1,2,2],
    ]
    var sources = 0
    var pairs = 0
    for fixture in range(6):
        var inventory = local_fixture(fixture)
        verify_local_admissibility(inventory)
        assert_equal(local_summary(inventory),expected[fixture])
        sources += len(inventory.rows)
        pairs += len(inventory.pairs)
        for row in inventory.rows:
            assert_equal(row[1],row[2])  # unconditional complete paired union
            assert_equal(row[15],row[16])  # exact all-raw-pair containment
        print("C4_LOCAL_MODEL",fixture,len(inventory.rows),len(inventory.pairs),
            expected[fixture][7],expected[fixture][8],expected[fixture][9])
    assert_equal(sources,16)
    assert_equal(pairs,30)


def test_global_reflection_and_local_lifting_differ() raises:
    var local = local_fixture(0)
    # e0 has ambient preimage zero but no integral inverse for diag(2,1,1).
    assert_equal(local.basis[0],[1,0,0,0,0,0,0,0,0])
    for row in local.rows:
        assert_equal(row[1],7)
        assert_equal(row[13],1)
        assert_equal(row[14],1)
        assert_equal(row[15],1)
    var redundant = local_fixture(1)
    var lost = local_fixture(2)
    for source in range(2):
        assert_equal(redundant.rows[source][5],4)
        assert_equal(redundant.rows[source][11],3)
        assert_equal(redundant.rows[source][13],0)
        assert_equal(redundant.rows[source][14],0)
        assert_equal(redundant.rows[source][15],1)
        assert_equal(redundant.rows[source][18],3)
        assert_equal(lost.rows[source][5],4)
        assert_equal(lost.rows[source][7],0)
        assert_equal(lost.rows[source][3],0)
        assert_equal(lost.rows[source][1],7)
        assert_equal(lost.rows[source][15],0)
    # Equal actual piece sets retain four different pairs of digit IDs.
    for i in range(4):
        assert_equal(redundant.pairs[i][15],7)
        for j in range(i):
            assert_false(redundant.pairs[i][1] == redundant.pairs[j][1] and
                redundant.pairs[i][2] == redundant.pairs[j][2])
    # Two distinct retained actual occurrences can have the same ancestor
    # and the same nonempty affine set; neither is deduplicated in counts.
    var diagonal_model = local_fixture_model(1)
    diagonal_model.sources = [[0,0,0,0,0]]
    diagonal_model.domain = [[0,0,0,0,0]]
    var diagonal = build_local_admissibility(diagonal_model)
    assert_equal(diagonal.rows[0][5],4)
    assert_equal(diagonal.rows[0][7],2)
    assert_equal(diagonal.rows[0][10],2)
    assert_equal(diagonal.rows[0][17],1)
    assert_equal(diagonal.pairs[0][18],7)
    assert_equal(diagonal.pairs[3][18],7)
    assert_equal(diagonal.pairs[0][9],diagonal.pairs[3][9])
    assert_false(diagonal.pairs[0][1] == diagonal.pairs[3][1])
    print("C4_LOCAL_GLOBAL_NONINTEGRAL_CONTROLS",1,3,4)


def test_representation_and_set_cover_differ() raises:
    var empty_internal = local_fixture(3)
    var redundant = local_fixture(4)
    for source in range(2):
        assert_equal(empty_internal.rows[source][13],1)
        assert_equal(empty_internal.rows[source][14],0)
        assert_equal(empty_internal.rows[source][9],0)
        assert_equal(empty_internal.rows[source][1],7)
        assert_equal(empty_internal.rows[source][15],0)
        assert_equal(redundant.rows[source][13],1)
        assert_equal(redundant.rows[source][14],0)
        assert_equal(redundant.rows[source][15],1)
        assert_equal(redundant.rows[source][12],1)
        assert_equal(redundant.rows[source][18],1)
    # The existing mandatory control is preserved verbatim.  Its lengths
    # remain physical diagnostics, never compact-set masks or Haar mass.
    assert_equal(forward_leak_control(),[4,2,2])
    print("C4_LOCAL_REPRESENTATION_AND_FORWARD_LEAK",4,2,2)


def test_authenticated_profiles_and_inconclusive_profiles() raises:
    var inventory = local_fixture(5)
    for source in range(2):
        assert_equal(inventory.rows[source][1],0)
        assert_equal(inventory.pairs[source][6],0)
        assert_equal(inventory.pairs[source][15],0)
        assert_equal(inventory.pairs[source][21],0)
        assert_equal(inventory.rows[source][13],1)
        assert_equal(inventory.rows[source][19],1)
    for source in range(2,4):
        assert_true(inventory.pairs[source][15] != 0)
        assert_equal(inventory.pairs[source][6],1)
        assert_equal(inventory.pairs[source][12],1)
        assert_equal(inventory.rows[source][15],1)
    for source in range(4,6):
        assert_true(inventory.pairs[source][15] != 0)
        assert_true(inventory.pairs[source][21] != 0)
        assert_equal(inventory.pairs[source][6],0)
        assert_equal(inventory.rows[source][13],0)
        assert_equal(inventory.rows[source][15],0)
        assert_equal(inventory.rows[source][0],0)
    assert_equal(project_mask(9,6,3),1)
    assert_equal(project_mask(18,6,3),2)
    assert_equal(project_mask(36,6,3),4)
    # A genuine enclosure may be too broad to prove an empty-piece claim.
    var coarse = local_fixture_model(5)
    coarse.profiles = [7,7,7]
    var inconclusive = build_local_admissibility(coarse)
    assert_equal(inconclusive.rows[0][1],0)
    assert_true(inconclusive.pairs[0][21] != 0)
    assert_equal(inconclusive.rows[0][19],0)
    print("C4_LOCAL_AUTHENTICATED_FINITE_PROFILES",2,2,2)


def test_singular_existential_lift_does_not_represent_all_lifts() raises:
    var model = singular_fixture_model()
    validate_cyclic_model(model)
    _reject_model(model)
    var witnesses = singular_lift_control()
    assert_equal(witnesses,[[0,0,0,0,0,0,0,0,7,1],[0,0,1,-1,0,0,0,0,7,0]])
    print("C4_LOCAL_SINGULAR_TWO_LIFT_CONTROL",1,2,1)


def test_inventory_mutations_fail_closed() raises:
    var original = local_fixture(1)
    var changed = original.copy()
    changed.digits[1][3] = 0
    _reject_inventory(changed)
    changed = original.copy()
    changed.digits[1][0] = 1
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[1][0] = 1
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[1][1] = changed.pairs[0][1]
    changed.pairs[1][2] = changed.pairs[0][2]
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[1][3] += 1
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[1][6] = 1
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[0][9] = 1
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[0][12] = 0
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[0][15] = 0
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs[0][21] = 0
    _reject_inventory(changed)
    changed = original.copy()
    changed.rows[0][13] = 1
    _reject_inventory(changed)
    changed = original.copy()
    changed.basis[0][3] = 0
    _reject_inventory(changed)
    changed = original.copy()
    changed.pairs.append(changed.pairs[0].copy())
    _reject_inventory(changed)
    changed = original.copy()
    var fewer = List[List[Int]]()
    for i in range(len(changed.pairs)-1):
        fewer.append(changed.pairs[i].copy())
    changed.pairs = fewer^
    _reject_inventory(changed)
    changed = original.copy()
    changed.determinant = 1
    _reject_inventory(changed)
    print("C4_LOCAL_ALTERED_OR_INCOMPLETE_INVENTORY_REFUSALS",15)


def test_false_premises_and_bounds_refuse() raises:
    var model = local_fixture_model(0)
    model.modulus = 16
    _reject_model(model)
    model = local_fixture_model(0)
    model.modulus = 1
    _reject_model(model)
    model = local_fixture_model(5)
    model.action = 2  # false ambient injectivity; tile/profile masks valid
    _reject_model(model)
    model = local_fixture_model(0)
    model.star[0] = 1  # star(M e0)=2 != A star(e0)=1
    _reject_model(model)
    model = local_fixture_model(1)
    model.tiles[0] = 1  # true commute/injection, false original tile union
    _reject_model(model)
    model = local_fixture_model(5)
    model.profiles[1] = 1  # undersized and wrong C1 fails actual enclosure
    _reject_model(model)
    model = local_fixture_model(5)
    model.profile_modulus = 4
    _reject_model(model)
    model = local_fixture_model(0)
    model.sources.append(model.sources[0].copy())
    _reject_model(model)
    model = local_fixture_model(0)
    model.domain.append([0,0,0,0,0])
    _reject_model(model)
    model = local_fixture_model(0)
    model.domain.append(model.domain[0].copy())
    _reject_model(model)
    model = local_fixture_model(0)
    model.sources[0][2] = 65
    _reject_model(model)
    model = local_fixture_model(0)
    model.images[0] = List[Int]()
    _reject_model(model)
    model = local_fixture_model(0)
    model.star[0] = -1
    _reject_model(model)
    model = local_fixture_model(0)
    model.tiles[0] = 8
    _reject_model(model)
    model = local_fixture_model(0)
    model.sources = List[List[Int]]()
    _reject_model(model)
    model = local_fixture_model(1)
    var refused = False
    try:
        _ = build_local_admissibility(model,candidate_cap=1)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = project_mask(7,6,4)
    except:
        refused = True
    assert_true(refused)
    refused = False
    try:
        _ = cyclic_image(8,3,1,0)
    except:
        refused = True
    assert_true(refused)
    print("C4_LOCAL_FALSE_PREMISE_AND_BOUND_REFUSALS",18)


def test_bounds_apply_to_every_actual_basis_probe_pair() raises:
    var model = local_fixture_model(0)
    var middle = List[Int]()
    for i in range(6):
        middle.append(0)
    middle.append(1)
    var last = List[Int]()
    for i in range(4):
        last.append(1)
    last.append(0)
    for i in range(4):
        last.append(1)
    last.append(2)
    model.images = [[0],middle,last]
    model.sources = [[0,0,0,0,0]]
    model.domain = [[0,0,0,0,0]]
    model.star = [0,0,0]
    validate_cyclic_model(model)
    # M has rows (1,6,1), (0,1,8), (0,0,1).  Each individual basis lift
    # is within the coordinate cap; in particular M^-1 e2=(47,-8,1).
    # But the actual e2 probe also pairs the last image's position-four 0
    # (prefix 4e1) with the first image's 0 (empty prefix).  Its lift is
    # M^-1(e2-4e1)=(71,-12,1), so the WHOLE construction must refuse.
    _reject_model(model)
    print("C4_LOCAL_COMPLETE_BASIS_PROBE_BOUND_REFUSAL",1)


def main() raises:
    test_six_finite_model_boundaries()
    test_global_reflection_and_local_lifting_differ()
    test_representation_and_set_cover_differ()
    test_authenticated_profiles_and_inconclusive_profiles()
    test_singular_existential_lift_does_not_represent_all_lifts()
    test_inventory_mutations_fail_closed()
    test_false_premises_and_bounds_refuse()
    test_bounds_apply_to_every_actual_basis_probe_pair()
    require_contract("C4 supplied finite cyclic models preserve all literal paired occurrences and distinguish local integral lifting, representation and retained set coverage")
    require_contract("C4 finite profile exclusions require actual tile enclosure and commuting projection; singular two-lift and inverse-closed forward-leak controls remain explicit")
