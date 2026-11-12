"""Source-bound full marks, correction direction, complete residues and refusals."""

from std.testing import assert_equal, assert_true
from finite_linear_algebra.integer_vector import matvec
from mojo_smoke.claims import require_contract
from psc.c4_cut_prefix_embedding import (
    bounded_inflate, build_cut_prefix_witness, verify_cut_prefix_witness,
    verify_balanced_cut,
)
from psc.c4_finite_cylinder_overlap import fixture_images
from psc.c4_nonunit_residue_occupancy import same_vector


def main() raises:
    var records = 0
    var residues = 0
    var nonzero = 0
    for fixture in range(2):
        for depth in range(0,7,2):
            var source: List[Int] = [2,0,1,0]
            var output = bounded_inflate(fixture_images(fixture),source,depth)
            for position in range(len(output)):
                var packet = build_cut_prefix_witness(fixture,source,depth,position)
                verify_cut_prefix_witness(packet)
                assert_equal(packet.address[6],output[position])
                records += 1
                residues += len(packet.residue_witnesses)
                if not same_vector(packet.correction,[0,0,0]):
                    nonzero += 1
    assert_true(records > 1000)
    assert_true(nonzero > 0)
    var paired = 0
    for fixture in range(2):
        for depth in range(0,7,2):
            var output = bounded_inflate(fixture_images(fixture),[0,1],depth)
            for position in range(len(output)):
                var top = build_cut_prefix_witness(fixture,[0,1],depth,position)
                var bottom = build_cut_prefix_witness(fixture,[1,0],depth,position)
                if same_vector(top.point,bottom.point):
                    verify_balanced_cut(top,bottom)
                    paired += 1
    assert_true(paired > 8)

    # Establish both exact valid baselines outside every refusal boundary.
    # A constructor regression must fail here, never earn mutant rejection credit.
    var good = build_cut_prefix_witness(0,[1,0,2],2,1)
    verify_cut_prefix_witness(good)
    var different = build_cut_prefix_witness(0,[1,0,2],2,0)
    verify_cut_prefix_witness(different)
    assert_true(not same_vector(good.point,different.point))
    assert_true(not same_vector(good.correction,[0,0,0]))
    assert_true(len(good.local_after) > 0)
    var refused = 0
    for control in range(19):
        var bad = good.copy()
        try:
            if control == 0:
                _ = build_cut_prefix_witness(0,[1],1,0)
            elif control == 1:
                _ = build_cut_prefix_witness(0,List[Int](),2,0)
            elif control == 2:
                _ = build_cut_prefix_witness(0,[3],2,0)
            elif control == 3:
                _ = build_cut_prefix_witness(0,[0],2,3)
            elif control == 4:
                _ = build_cut_prefix_witness(0,[1],6,0,2)
            elif control == 5:
                bad.address = [0,2]
                verify_cut_prefix_witness(bad)
            elif control == 6:
                bad.address[0] = 1
                verify_cut_prefix_witness(bad)
            elif control == 7:
                bad.reference = [0,1,2]
                verify_cut_prefix_witness(bad)
            elif control == 8:
                bad.address[3] = 7
                verify_cut_prefix_witness(bad)
            elif control == 9:
                bad.local_before.append(0)
                verify_cut_prefix_witness(bad)
            elif control == 10:
                bad.local_after = List[Int]()
                verify_cut_prefix_witness(bad)
            elif control == 11:
                for i in range(3):
                    bad.correction[i] = -bad.correction[i]
                verify_cut_prefix_witness(bad)
            elif control == 12:
                bad.reference_point[0] += 1
                verify_cut_prefix_witness(bad)
            elif control == 13:
                bad.residue_witnesses = List[List[Int]]()
                verify_cut_prefix_witness(bad)
            elif control == 14:
                bad.correction[0] = Int.MAX
                verify_cut_prefix_witness(bad)
            elif control == 15:
                bad.source = [2,0,1]
                verify_cut_prefix_witness(bad)
            elif control == 16:
                verify_balanced_cut(good,different)
            elif control == 17:
                _ = matvec([[2,0,0],[0,1,0],[0,0,1]],[Int.MAX,0,0])
            else:
                bad.residue_witnesses[1][0] += 1
                verify_cut_prefix_witness(bad)
        except:
            refused += 1
            print("refused",control)
    assert_equal(refused,19)
    # The authentic named reference prefixes differ despite equal incidence.
    var first = build_cut_prefix_witness(0,[1],0,0)
    var second = build_cut_prefix_witness(1,[1],0,0)
    assert_true(not same_vector(first.reference,second.reference))
    assert_true(not same_vector(first.correction,second.correction))
    print("cut-prefix records/residues/balanced-cuts/refusals",records,residues,paired,refused)
    require_contract("C4 actual cut-prefix full marks and exact residue embedding")
