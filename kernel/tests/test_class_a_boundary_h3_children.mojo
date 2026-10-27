"""All oriented H3-chain child pairs, half separator and actual short exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_e_children import verify_eh_packet
from psc.class_a_boundary_h3_children import (
    alpha_high, chain_source, certify_h3_children, chain_child_allowed,
    chain_child_star, verify_chain_packet, chain_image, chain_path,
    verify_chain_path, chain_rank,
)
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt


def main() raises:
    certify_h3_children()
    assert_true(not alpha_high(0,0))
    assert_true(not alpha_high(1,1))
    assert_true(alpha_high(2,2))
    assert_true(alpha_high(0,1))
    assert_true(not alpha_high(1,0))
    var envelope=chain_image()
    assert_true(len(envelope)==76)
    var attained=List[Bool]()
    for _ in envelope:
        attained.append(False)
    var pairs=0
    var accepted=0
    var path_edges=0
    for k in range(8):
        for t in range(7):
            var n=k+t+3
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            # These normalized shifts are 2alpha-2 and 2alpha.
            # Their independent exact geometry distinguishes the strict half split.
            assert_true(interior_overlap_cached(tables,cache,
                geometric_state(tables,BoundaryLabel(2,2,2,2,-8)))==alpha_high(k,t))
            assert_true(interior_overlap_cached(tables,cache,
                geometric_state(tables,BoundaryLabel(2,2,2,2,-6)))==(not alpha_high(k,t)))
            verify_eh_packet(tables,1,k,t,BoundaryEdge(0,n+3,chain_source(0)))
            for kind in range(8):
                var w=chain_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if w.top==0 else n-1
                var B=A if w.bottom==0 else n-1
                var group=kind//2
                var expected=2*t+3
                if group==1:
                    expected=2*k+2
                elif group==2:
                    expected=2*t+6
                elif group==3:
                    expected=2*n+3
                var star=chain_child_star(kind,k,t)
                assert_true(len(star)==expected)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(B+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_chain_packet(tables,kind,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,
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
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==chain_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(B+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var path=chain_path(kind,k,t)
                verify_chain_path(tables,kind,k,t,path)
                assert_true(len(path)==5-group)
                path_edges+=len(path)
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        certify_h3_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=chain_child_allowed(8,0,0,0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=chain_child_allowed(0,0,0,-1,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=chain_rank(BoundaryLabel(0,0,0,0,0))
    except:
        failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var path=chain_path(0,0,0)
    path[1]=BoundaryEdge(0,0,path[1].target)
    failed=False
    try:
        verify_chain_path(tables,0,0,0,path)
    except:
        failed=True
    assert_true(failed)
    # Correct final C cannot excuse a corrupted intermediate, or a wrong terminal.
    path=chain_path(0,0,0)
    path[len(path)-1]=BoundaryEdge(1,2,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:
        verify_chain_path(tables,0,0,0,path)
    except:
        failed=True
    assert_true(failed)
    assert_true(not chain_child_allowed(0,4,3,25,0))
    assert_true(chain_child_allowed(0,2,2,19,0)) # high diagonal last/first
    print("CLASS_A_BOUNDARY_H3_FINITE members=56", "pairs",pairs,"accepted",accepted,
          "path_edges",path_edges,"union_labels=76", "all_sources_exit_in_at_most_five=true", "BH=false")
    require_contract("class-A minus H3/J/K/L and reversals: exact half-chamber polynomial separator with diagonal exceptions, complete eight actual child stars and 76-label union, full Parikh/Perron every-pair replay, actual orientation and selected <=5-step typed coincidence; bad indices, symbolic corruption, out-of-packet rank and broken paths refused; no universal BH")
