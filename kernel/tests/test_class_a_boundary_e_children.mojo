"""All six actual stars, real orientation reversal and short coincidence exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge,
)
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_w_children import typed_coincidence
from psc.class_a_boundary_e_children import (
    eh_source, certify_eh_children, eh_child_allowed, eh_child_star,
    verify_eh_packet, eh_image, short_eh_path, verify_short_eh_path, eh_selected_rank,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_eh_children()
    var members=0
    var pairs=0
    var accepted=0
    var path_edges=0
    var envelope=eh_image()
    assert_true(len(envelope)==29)
    for k in range(8):
        for t in range(7):
            members+=1
            var n=k+3+t
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            var attained=List[Bool]()
            for _ in envelope:
                attained.append(False)
            for kind in range(6):
                var parent=eh_source(kind)
                var source=geometric_state(tables,parent)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if parent.top==0 else n-1
                var B=A if parent.bottom==0 else n-1
                var group=kind//2
                var expected=2*d+1 if group==0 else (n+2 if group==1 else 2*n+3)
                var star=eh_child_star(kind,k,t)
                assert_true(len(star)==expected)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_eh_packet(tables,kind,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(parent),edge.j,edge.i,
                                       reverse_label(edge.target))
                    var found=False
                    for z in range(len(envelope)):
                        if edge.target==envelope[z]:
                            attained[z]=True
                            found=True
                    assert_true(found)
                for i in range(R+2):
                    for j in range(B+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,parent,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==eh_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var path=short_eh_path(kind,k,t)
                verify_short_eh_path(tables,kind,k,t,path)
                assert_true(len(path)==(1 if group==1 else 2))
                path_edges+=len(path)
            for reached in attained:
                assert_true(reached)
            # A real zero-offset unequal-type child is retained by the carrier,
            # while the stronger typed-coincidence terminal predicate refuses it.
            var unequal=BoundaryLabel(2,1,0,0,0)
            verify_eh_packet(tables,2,k,t,BoundaryEdge(n-1,n,unequal))
            assert_true(not typed_coincidence(unequal))
            assert_true(not eh_child_allowed(2,k,t,0,2)) # endpoint-only contact
            assert_true(not eh_child_allowed(4,k,t,2*n+3,n)) # invalid extra run
    var failed=False
    try:
        certify_eh_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=eh_child_allowed(6,0,0,0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=eh_child_allowed(2,0,0,-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=eh_selected_rank(BoundaryLabel(0,0,0,0,0))
    except:
        failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var path=short_eh_path(1,0,0)
    path[0]=BoundaryEdge(0,0,path[0].target)
    failed=False
    try:
        verify_short_eh_path(tables,1,0,0,path)
    except:
        failed=True
    assert_true(failed)
    path=short_eh_path(1,0,0)
    path[1]=BoundaryEdge(1,2,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:
        verify_short_eh_path(tables,1,0,0,path)
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_EH_FINITE members",members,"pairs",pairs,
          "accepted",accepted,"selected_path_edges",path_edges,
          "every_member_image_labels=29", "all_six_sources_short_coincidence=true", "BH=false")
    require_contract("class-A minus E/H1/H2 and all orientation reversals: complete six indexed child stars, every finite pair against exact full Parikh and Perron geometry, 29 typed targets per member, actual orientation reversal, at most two-step typed coincidence from each source; endpoint, illegal ordinals, corrupted path, false typed terminal and out-of-packet rank rejected; no universal BH")
