"""Export complete finite cut-prefix witnesses as one deterministic JSON packet."""

from psc.c4_cut_prefix_embedding import (
    bounded_inflate, build_cut_prefix_witness, verify_cut_prefix_witness,
    verify_balanced_cut, witness_json, integer_array,
)
from psc.c4_finite_cylinder_overlap import fixture_images
from psc.c4_nonunit_residue_occupancy import same_vector


def main() raises:
    var sources: List[List[Int]] = [[0,1,2],[2,0,1,0],[1,2,0]]
    print('{"schema":"c4-cut-prefix-embedding-v1","fixtures":[0,1],"powers":[0,2,4,6],"sources":[[0,1,2],[2,0,1,0],[1,2,0]],"caps":{"power":6,"source":8,"word":100000},"scope":"finite literal embedding and residue witnesses; no limiting or measure conclusion","witnesses":[')
    var count = 0
    var residue_count = 0
    for fixture in range(2):
        var images = fixture_images(fixture)
        for depth in range(0,7,2):
            for source in sources:
                var output = bounded_inflate(images,source,depth)
                for position in range(len(output)):
                    var packet = build_cut_prefix_witness(fixture,source,depth,position)
                    verify_cut_prefix_witness(packet)
                    if count > 0:
                        print(",")
                    print(witness_json(packet))
                    count += 1
                    residue_count += len(packet.residue_witnesses)
    print('],"balanced_cuts":[')
    var cuts = 0
    var distinct = 0
    for fixture in range(2):
        var images = fixture_images(fixture)
        for depth in range(0,7,2):
            var output = bounded_inflate(images,[0,1],depth)
            for position in range(len(output)):
                var top = build_cut_prefix_witness(fixture,[0,1],depth,position)
                var bottom = build_cut_prefix_witness(fixture,[1,0],depth,position)
                if same_vector(top.point,bottom.point):
                    verify_balanced_cut(top,bottom)
                    if cuts > 0:
                        print(",")
                    print('{"top":'+witness_json(top)+',"bottom":'+witness_json(bottom)+'}')
                    cuts += 1
                    if top.address[6] != bottom.address[6]:
                        distinct += 1
    print('],"counts":'+integer_array([count,residue_count,cuts,distinct])+'}')
