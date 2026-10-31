"""Six complete P3-family stars, actual ancestry and two-step typed exit."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_p3_children import certify_p3_children, p3_source, p3_child_allowed, p3_child_star, p3_image, in_p3_image, verify_p3_packet, p3_path, verify_p3_path, _first_identity
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt
from psc.param_poly import qx_const
from psc.class_a_boundary_occurrences import LAST


def main() raises:
    certify_p3_children()
    var envelope=p3_image()
    assert_true(len(envelope)==37)
    var attained=List[Bool]()
    for z in range(len(envelope)):
        attained.append(False)
        assert_true(in_p3_image(envelope[z]))
        for j in range(z):
            assert_true(envelope[z]!=envelope[j])
    var pairs=0
    var accepted=0
    var path_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var N=n-1
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,N))
            var cache=Dict[CubicElt,Int]()
            verify_member_edge(tables,-1,k,n,d,BoundaryLabel(0,0,-1,0,3),A+1,A-k-1,p3_source(0))
            verify_p3_packet(tables,0,k,t,BoundaryEdge(A+1,n-2,BoundaryLabel(0,2,1,-1,1)))
            var disjoint=member_transport(-1,k,n,d,p3_source(0),d+2,0)
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,disjoint)))
            if n==3:
                assert_true(d+4==A+1)
                assert_true(member_transport(-1,k,n,d,p3_source(0),d+4,0)!=p3_source(2))
            for kind in range(6):
                var w=p3_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if w.top==0 else N
                var B=A if w.bottom==0 else N
                var star=p3_child_star(kind,k,t)
                var expected=2*n-3 if kind//2==0 else (n+3 if kind//2==1 else A+3)
                assert_true(len(star)==expected)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_p3_packet(tables,kind,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var found=False
                    for z in range(len(envelope)):
                        if edge.target==envelope[z]:
                            attained[z]=True
                            found=True
                    assert_true(found)
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==p3_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var packet=p3_path(kind,k,t)
                verify_p3_path(tables,kind,k,t,packet)
                verify_p3_packet(tables,kind,k,t,packet[0])
                assert_true(len(packet)==(2 if kind//2==0 else 1))
                path_edges+=len(packet)
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        certify_p3_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=p3_child_allowed(6,0,0,0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=p3_child_allowed(0,0,0,-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _first_identity(qx_const(3),qx_const(5),LAST,qx_const(9),p3_source(2))
    except:
        failed=True
    assert_true(failed) # symbolic endpoint check also binds actual child types
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        verify_p3_packet(tables,0,0,0,BoundaryEdge(9,0,p3_source(2)))
    except:
        failed=True
    assert_true(failed) # same offset but different actual child types, both interior
    var packet=p3_path(0,0,0)
    packet[0]=BoundaryEdge(9,0,p3_source(2))
    failed=False
    try:
        verify_p3_path(tables,0,0,0,packet)
    except:
        failed=True
    assert_true(failed)
    packet=p3_path(1,0,0)
    packet[len(packet)-1]=BoundaryEdge(2,1,BoundaryLabel(2,0,0,0,0))
    failed=False
    try:
        verify_p3_path(tables,1,0,0,packet)
    except:
        failed=True
    assert_true(failed)
    verify_p3_packet(tables,4,0,0,BoundaryEdge(8,9,BoundaryLabel(2,0,0,0,0)))
    assert_true(BoundaryLabel(2,0,0,0,0)!=BoundaryLabel(2,2,0,0,0))
    print("CLASS_A_BOUNDARY_P3_FINITE members=56", "pairs",pairs,"accepted",accepted,
          "path_edges",path_edges,"union_labels=37", "BH=false")
    require_contract("class-A minus P3/T/U and real reversals: six complete nine-kind stars, exact 37-label union, every literal pair checked by Parikh/Perron geometry, actual E3 ancestry and typed exits <=2 with sole n=3 LAST exception; legal disjoint, wrong interior targets, corrupted identities and malformed paths refused; no global closure/BH")
