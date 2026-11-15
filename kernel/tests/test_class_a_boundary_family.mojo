"""The shared boundary-children skeleton: synthesis, packet and star verification.

Real families (H9: kind!=0 orientation and fixed-kind dimensions; B3 and P9:
the two hand-picked duplicate strides it replaces; F: kind%2 orientation) are
checked on actual members; negative controls are a duplicated, a dropped and
a mistyped edge, a disallowed occurrence, an occurrence pair the old p9
stride n+1 conflated, a negative index and a dimension overflow.
"""
from std.testing import assert_true, assert_false
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge
from psc.class_a_boundary_next_run import _parameters
from psc.class_a_boundary_family import BoundaryFamily, boundary_dimensions, append_child, verify_child_packet, verify_child_star, duplicate_occurrence
from psc.class_a_boundary_h9_children import H9Children, h9_child_star, h9_count, verify_h9_star
from psc.class_a_boundary_b3_children import B3Children, b3_child_star, verify_b3_star
from psc.class_a_boundary_p9_children import P9Children, p9_child_star, p9_count, verify_p9_star
from psc.class_a_boundary_f_children import FChildren, f_child_star
from psc.overlap_seed_patch import SeedOverlapTables, build_seed_overlap_tables_screened


def refuses_star[F: BoundaryFamily](family: F, tables: SeedOverlapTables, kind: Int, k: Int, t: Int, edges: List[BoundaryEdge], count: Int) -> Bool:
    try:
        verify_child_star(family,tables,kind,k,t,edges,count)
    except:
        return True
    return False


def check_family[F: BoundaryFamily](family: F, tables: SeedOverlapTables, kind: Int, k: Int, t: Int, star: List[BoundaryEdge]) raises:
    var count=len(star)
    assert_true(count>=2)
    verify_child_star(family,tables,kind,k,t,star,count)
    var rebuilt=List[BoundaryEdge]()
    for edge in star:
        var i=edge.j if family.swapped(kind) else edge.i
        var j=edge.i if family.swapped(kind) else edge.j
        append_child(family,rebuilt,kind,k,t,i,j)
    for z in range(count):assert_true(rebuilt[z].i==star[z].i and rebuilt[z].j==star[z].j and rebuilt[z].target==star[z].target)
    var duplicated=star.copy()
    duplicated[count-1]=star[0]
    assert_true(refuses_star(family,tables,kind,k,t,duplicated,count))
    var dropped=star.copy()
    _=dropped.pop()
    assert_true(refuses_star(family,tables,kind,k,t,dropped,count))
    var mistyped=star.copy()
    mistyped[0]=BoundaryEdge(star[0].i,star[0].j,BoundaryLabel(9,9,9,9,9))
    assert_true(refuses_star(family,tables,kind,k,t,mistyped,count))
    var bad=0 if not family.allowed(kind,k,t,0,0) else -1  # (0,0) when disallowed, else nonexistent
    var refused=False
    try:
        var out=List[BoundaryEdge]()
        append_child(family,out,kind,k,t,bad,bad)
    except:
        refused=True
    assert_true(refused)


def main() raises:
    assert_false(duplicate_occurrence([BoundaryEdge(0,9,BoundaryLabel(0,0,0,0,0)),BoundaryEdge(1,0,BoundaryLabel(0,0,0,0,0))]))
    assert_true(duplicate_occurrence([BoundaryEdge(2,3,BoundaryLabel(0,0,0,0,0)),BoundaryEdge(5,1,BoundaryLabel(0,0,0,0,0)),BoundaryEdge(2,3,BoundaryLabel(1,0,0,0,0))]))
    var negative=False
    try:
        _=duplicate_occurrence([BoundaryEdge(-1,3,BoundaryLabel(0,0,0,0,0))])
    except:
        negative=True
    assert_true(negative)
    var overflow=False
    try:
        _=boundary_dimensions(0,0,Int.MAX)
    except:
        overflow=True
    assert_true(overflow)
    assert_true(H9Children().swapped(1) and not H9Children().swapped(0))
    assert_true(FChildren().swapped(3) and not FChildren().swapped(2))
    var stars=0
    for k in range(3):
        for t in range(3):
            var p=_parameters(-1,k,t)
            var dims=boundary_dimensions(k,t,12)
            assert_true(dims[0]==p[0] and dims[1]==p[1] and dims[2]==p[0]+p[1] and dims[3]==p[0]-1)
            var n=p[0]
            var A=p[0]+p[1]
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            for kind in range(2):
                var h9=h9_child_star(kind,k,t)
                assert_true(len(h9)==h9_count(k,t))
                verify_h9_star(tables,kind,k,t,h9)
                check_family(H9Children(),tables,kind,k,t,h9)
                var b3=b3_child_star(kind,k,t)
                verify_b3_star(tables,kind,k,t,b3)
                check_family(B3Children(),tables,kind,k,t,b3)
                var p9=p9_child_star(kind,k,t)
                assert_true(len(p9)==p9_count(k,t))
                verify_p9_star(tables,kind,k,t,p9)
                check_family(P9Children(),tables,kind,k,t,p9)
                check_family(FChildren(),tables,kind,k,t,f_child_star(kind,k,t))
                stars+=4
    assert_true(stars==72)
    print("CLASS_A_BOUNDARY_FAMILY stars=72 negative_controls=duplicate,dropped,mistyped,disallowed,collision,negative,overflow")
    require_contract("class-A boundary children skeleton: one synthesis/packet/star verifier over BoundaryFamily reproduces the H9, B3, P9 and F stars on k<3,t<3 members and refuses duplicated, dropped and mistyped edges, disallowed occurrences, negative indices and dimension overflow; duplicate keys i*(max j+1)+j are injective")
