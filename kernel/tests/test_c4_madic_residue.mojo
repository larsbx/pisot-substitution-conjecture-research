"""Complete quotient/address authentication and failed stronger residue claims."""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from finite_linear_algebra.madic_ball import contains
from finite_linear_algebra.mat3 import Mat3
from psc.c4_bounded_cover import forward_leak_control
from psc.c4_madic_residue import (
    MadicResidue, ResidueLevel, build_madic_residue, verify_madic_residue,
    residue_fixture_images, residue_fixture, residue_class, residue_summary,
    profile_intersection, residue_refusal,
)


def _reject(certificate: MadicResidue) raises:
    var refused = False
    try:
        verify_madic_residue(certificate)
    except:
        refused = True
    assert_true(refused)


def test_complete_quotients_and_all_actual_addresses() raises:
    var levels = 0
    var classes = 0
    var occurrences = 0
    for fixture in range(4):
        var certificate = residue_fixture(fixture)
        verify_madic_residue(certificate)
        for level in certificate.levels:
            assert_equal(len(level.representatives),level.index)
            assert_equal(level.candidates,3*level.index)
            assert_equal(len(level.addition),level.index)
            var marked = 0
            for source in range(3):
                for position in range(len(level.words[source])):
                    var mark = level.occurrences[marked].copy()
                    assert_equal(mark[0],source)
                    assert_equal(mark[1],position)
                    assert_equal(mark[2],level.words[source][position])
                    assert_equal(mark[3]+mark[4]+mark[5],position)
                    assert_equal(mark[6]+mark[7]+mark[8],len(level.words[source])-position-1)
                    marked += 1
            assert_equal(marked,len(level.occurrences))
            for first in range(level.index):
                assert_equal(level.addition[first][0],first)
                assert_equal(level.addition[0][first],first)
                assert_equal(level.addition[first][level.inverse[first]],0)
                for second in range(level.index):
                    for third in range(level.index):
                        assert_equal(level.addition[level.addition[first][second]][third],
                            level.addition[first][level.addition[second][third]])
            levels += 1
            classes += level.index
            occurrences += marked
        print("C4_MADIC_FIXTURE",fixture,certificate.depth,certificate.determinant)
    assert_equal(levels,17)
    assert_equal(classes,139)
    assert_equal(occurrences,333)
    print("C4_MADIC_COMPLETE_INVENTORY",levels,classes,occurrences)


def test_named_group_is_not_the_cyclic_group_of_order_four() raises:
    var named = residue_fixture(0)
    var level = named.levels[2].copy()
    assert_equal(level.matrix.e,[1,3,1,1,3,3,1,1,1])
    assert_equal(level.smith,[1,2,2])
    assert_equal(level.orders,[1,2,2,2])
    assert_equal(level.addition[1],[1,0,3,2])
    assert_equal(level.action,[0,2,0,2])
    assert_equal(level.reduction,[0,1,0,1])
    assert_equal(residue_summary(level),[4,12,15,6,2,2,2])
    assert_equal(level.profiles[0],[0,2,3])
    assert_equal(level.profiles[1],[0,2])
    assert_equal(level.profiles[2],[1])
    # Same group cardinality does not authenticate its operation table.
    var cyclic = named.copy()
    for first in range(4):
        for second in range(4):
            cyclic.levels[2].addition[first][second] = (first+second)%4
    _reject(cyclic)
    # A finite action collision is compatible with an injective limit action.
    assert_false(level.representatives[0] == level.representatives[2])
    assert_equal(level.action[0],level.action[2])
    for identity in range(4):
        assert_equal(level.action[level.action[identity]],0)
    print("C4_MADIC_NONCYCLIC_AND_FINITE_ACTION",4,2,2)


def test_literal_multiplicity_and_profile_scope() raises:
    var named = residue_fixture(0)
    var level = named.levels[2].copy()
    assert_equal(level.counts[6],[1,2,1,2,2])
    assert_equal(level.occurrences[6],[1,3,1,2,1,0,1,1,1,2])
    assert_equal(level.occurrences[9],[1,6,1,3,2,1,0,0,0,2])
    # Two equal-residue occurrences in the SAME source remain different marks.
    assert_equal(level.occurrences[6][9],level.occurrences[9][9])
    assert_false(level.occurrences[6][1] == level.occurrences[9][1])
    assert_equal(len(level.occurrences),15)
    assert_equal(residue_summary(level)[6],2)
    assert_equal(profile_intersection(level,2,2,[0,0,0]),[1])
    assert_equal(profile_intersection(level,2,2,[1,0,0]),List[Int]())
    assert_equal(named.levels[3].orders[residue_class(named.levels[3],[1,0,0])],4)
    assert_equal(profile_intersection(named.levels[3],0,0,[1,0,0]),[3])
    assert_equal(profile_intersection(named.levels[3],0,0,[-1,0,0]),[2])
    # These are projected sets.  Nonempty is not an actual-overlap assertion;
    # empty becomes sound for actual sets only with the Lean enclosure premise.
    var reordered = residue_fixture(1)
    assert_equal(named.matrix.e,reordered.matrix.e)
    assert_equal(named.levels[2].addition[1],reordered.levels[2].addition[1])
    assert_false(named.levels[2].counts[0] == reordered.levels[2].counts[0])
    print("C4_MADIC_LITERAL_MULTIPLICITY",15,13,2)


def test_column_lattice_and_finite_depth_alias() raises:
    var named = residue_fixture(0)
    var column: List[Int] = [5,7,3]
    var transposed: List[Int] = [0,1,0,1,1,1,2,1,0]
    assert_true(contains(named.matrix.e,3,4,column))
    assert_false(contains(transposed,3,4,column))
    assert_equal(residue_class(named.levels[4],column),0)
    var doubled = residue_fixture(3)
    assert_equal(doubled.levels[2].smith,[4,4,4])
    assert_equal(residue_class(doubled.levels[1],[2,0,0]),0)
    assert_equal(residue_class(doubled.levels[2],[2,0,0]),4)
    assert_equal(doubled.levels[2].reduction[4],0)
    # Neither a zero residue nor all residues of a unimodular action force z=0.
    var unit = residue_fixture(2)
    for level in unit.levels:
        assert_equal(level.index,1)
        assert_equal(level.smith,[1,1,1])
        assert_equal(residue_class(level,[1,0,0]),0)
        assert_equal(level.action,[0])
    # A negative determinant is normalized by absolute lattice index.
    var reversed = build_madic_residue([[1],[0],[2]],2)
    assert_equal(reversed.determinant,-1)
    assert_equal(reversed.levels[1].determinant,-1)
    assert_equal(reversed.levels[2].determinant,1)
    assert_equal(reversed.levels[2].index,1)
    var negative_nonunit = build_madic_residue([[1,1],[0,0],[2,2]],2)
    assert_equal(negative_nonunit.determinant,-8)
    assert_equal(negative_nonunit.levels[1].index,8)
    assert_equal(negative_nonunit.levels[2].index,64)
    print("C4_MADIC_COLUMN_LATTICE_AND_ALIAS",1,0,0,4)


def test_every_submitted_field_is_authenticated() raises:
    var canonical = residue_fixture(0)
    for mutation in range(22):
        var altered = canonical.copy()
        if mutation == 0:
            altered.matrix.e[0] += 1
        elif mutation == 1:
            altered.levels[2].index = 3
        elif mutation == 2:
            altered.levels[2].adjugate.e[0] += 1
        elif mutation == 3:
            altered.levels[2].representatives[1][0] += 1
        elif mutation == 4:
            altered.levels[2].representatives[1][3] += 1
        elif mutation == 5:
            altered.levels[2].representatives[1][7] = 2
        elif mutation == 6:
            _ = altered.levels[2].representatives.pop()
        elif mutation == 7:
            altered.levels[2].addition[1][1] = 2
        elif mutation == 8:
            altered.levels[2].inverse[1] = 2
        elif mutation == 9:
            altered.levels[2].orders[1] = 4
        elif mutation == 10:
            altered.levels[2].action[2] = 2
        elif mutation == 11:
            altered.levels[2].reduction[2] = 1
        elif mutation == 12:
            altered.levels[2].words[1][0] = 0
        elif mutation == 13:
            altered.levels[2].occurrences[6][3] += 1
        elif mutation == 14:
            altered.levels[2].occurrences[6][6] += 1
        elif mutation == 15:
            altered.levels[2].occurrences[6][1] = 6
        elif mutation == 16:
            altered.levels[2].occurrences[6][9] = 0
        elif mutation == 17:
            altered.levels[2].occurrences.append(altered.levels[2].occurrences[6].copy())
        elif mutation == 18:
            _ = altered.levels[2].occurrences.pop()
        elif mutation == 19:
            # All source/letter totals still agree, but residue placement is false.
            altered.levels[2].counts[0][2] -= 1
            altered.levels[2].counts[1][2] += 1
        elif mutation == 20:
            _ = altered.levels[2].profiles[0].pop()
        else:
            altered.levels[2].candidates = 11
        _reject(altered)
    print("C4_MADIC_INVENTORY_MUTATIONS",22)


def test_budgets_and_arithmetic_refuse_incomplete_constructions() raises:
    for control in range(8):
        residue_refusal(control)
    # This budget fails only after all four class representatives were found.
    # All basis extensions are required even when no new classes remain.
    var complete = build_madic_residue(residue_fixture_images(0),2,candidate_cap=12)
    assert_equal(complete.levels[2].candidates,12)
    var maximal = build_madic_residue(residue_fixture_images(0),6)
    assert_equal(maximal.levels[6].index,64)
    assert_equal(maximal.levels[6].candidates,192)
    for control in range(17):
        var refused = False
        try:
            if control == 0:
                _ = build_madic_residue([[0],[1]],1)
            elif control == 1:
                _ = build_madic_residue([[0],[],[2]],1)
            elif control == 2:
                _ = build_madic_residue([[0],[1],[3]],1)
            elif control == 3:
                _ = build_madic_residue([[0,0,0,0],[1],[2]],1)
            elif control == 4:
                _ = build_madic_residue(residue_fixture_images(0),-1)
            elif control == 5:
                _ = build_madic_residue(residue_fixture_images(0),1,index_cap=0)
            elif control == 6:
                _ = build_madic_residue(residue_fixture_images(0),1,index_cap=65)
            elif control == 7:
                _ = build_madic_residue(residue_fixture_images(0),1,candidate_cap=0)
            elif control == 8:
                _ = build_madic_residue(residue_fixture_images(0),1,candidate_cap=193)
            elif control == 9:
                _ = build_madic_residue(residue_fixture_images(0),0,candidate_cap=2)
            elif control == 10:
                _ = build_madic_residue(residue_fixture_images(0),1,word_cap=0)
            elif control == 11:
                _ = build_madic_residue(residue_fixture_images(0),1,word_cap=730)
            elif control == 12:
                _ = build_madic_residue(residue_fixture_images(0),1,occurrence_cap=0)
            elif control == 13:
                _ = build_madic_residue(residue_fixture_images(0),1,occurrence_cap=2188)
            elif control == 14:
                _ = build_madic_residue(residue_fixture_images(0),0,occurrence_cap=2)
            elif control == 15:
                _ = residue_class(complete.levels[2],[0,Int.MAX,0])
            else:
                _ = ResidueLevel(1,Mat3([730,0,0,0,1,0,0,0,1]))
        except:
            refused = True
        assert_true(refused)
    assert_equal(forward_leak_control(),[4,2,2])
    print("C4_MADIC_REFUSALS",8,17)
    print("C4_MADIC_FORWARD_LEAK",4,2,2)


def test_action_image_and_one_level_division() raises:
    for fixture in range(2):
        var certificate = residue_fixture(fixture)
        for depth in range(1, len(certificate.levels)):
            var level = certificate.levels[depth].copy()
            var previous = certificate.levels[depth - 1].copy()
            # Record the division class at depth-1 for every depth image class.
            var division = List[Int]()
            for _ in range(level.index):
                division.append(-1)
            for x in range(level.index):
                var image_class = level.action[x]
                var quotient_class = level.reduction[x]
                if division[image_class] == -1:
                    division[image_class] = quotient_class
                else:
                    assert_equal(division[image_class], quotient_class)
            var covered = 0
            for image_class in range(level.index):
                var first = image_class
                for q in range(depth, 1, -1):
                    first = certificate.levels[q].reduction[first]
                assert_equal(division[image_class] != -1, first == 0)
                if division[image_class] != -1:
                    covered += 1
            assert_equal(covered, previous.index)
            assert_equal(2 * covered, level.index)
            # Duplicate one complete occurrence cover. Each class is measured
            # once in the union but twice in the sum over occurrences.
            assert_true(covered > 0)
            assert_true(covered < 2 * covered)
            print("C4_MADIC_IMAGE_HALF", fixture, depth, covered, level.index)


def main() raises:
    test_complete_quotients_and_all_actual_addresses()
    test_action_image_and_one_level_division()
    test_named_group_is_not_the_cyclic_group_of_order_four()
    test_literal_multiplicity_and_profile_scope()
    test_column_lattice_and_finite_depth_alias()
    test_every_submitted_field_is_authenticated()
    test_budgets_and_arithmetic_refuse_incomplete_constructions()
    require_contract("C4 complete bounded matrix quotients preserve column lattices, maps and literal occurrence multiplicity")
    require_contract("C4 finite residue profiles require a supplied geometric enclosure and preserve forward-leak and cap controls")
