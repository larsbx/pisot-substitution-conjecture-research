"""Every literal E2/Dxx child pair, conditional endpoint and selected typed exits."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_p_children import p_source, verify_p_packet
from psc.class_a_boundary_h3_children import chain_source
from psc.class_a_boundary_e2_children import (
    certify_e2_children, e2_source, e2_child_allowed, e2_child_star,
    e2_image, verify_e2_packet, e2_path, e2_rank, verify_e2_path,
)
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.perron_field3 import CubicElt
from psc.class_a_boundary_occurrences import symbolic_child, RUN, FIRST
from psc.class_a_boundary_signs import chamber_parameters
from psc.param_poly import QX, qx_const, qx_add


def main() raises:
    certify_e2_children()
    var envelope=e2_image()
    assert_true(len(envelope)==46)
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
            verify_p_packet(tables,4,k,t,BoundaryEdge(0,0,e2_source(0)))
            if k>=2:
                verify_member_edge(tables,-1,k,n,d,chain_source(6),1,n,p_source(0))
                verify_p_packet(tables,0,k,t,BoundaryEdge(1,t+4,p_source(4)))
            var bad=member_transport(-1,k,n,d,e2_source(2),t+3,1)
            var good=member_transport(-1,k,n,d,e2_source(2),A+1,2*n+1)
            assert_true(bad==BoundaryLabel(2,2,0,-2,4))
            assert_true(not interior_overlap_cached(tables,cache,geometric_state(tables,bad)))
            assert_true(good==BoundaryLabel(0,2,0,-2,4))
            verify_e2_packet(tables,2,k,t,BoundaryEdge(A+1,2*n+1,good))
            for kind in range(4):
                var w=e2_source(kind)
                var source=geometric_state(tables,w)
                assert_true(interior_overlap_cached(tables,cache,source))
                var expected=2*t+1 if kind//2==0 else 4*n+3
                var star=e2_child_star(kind,k,t)
                assert_true(len(star)==expected)
                var seen=Dict[Int,Bool]()
                for edge in star:
                    var key=edge.i*(A+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_e2_packet(tables,kind,k,t,edge)
                    verify_member_edge(tables,-1,k,n,d,reverse_label(w),edge.j,edge.i,reverse_label(edge.target))
                    var found=False
                    for z in range(len(envelope)):
                        if edge.target==envelope[z]:
                            attained[z]=True
                            found=True
                    assert_true(found)
                for i in range(A+2):
                    for j in range(A+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,w,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==e2_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(A+2)+j in seen))
                        if overlaps:
                            accepted+=1
                var path=e2_path(kind,k,t)
                verify_e2_path(tables,kind,k,t,path)
                assert_true(len(path)==(5 if kind//2==0 else 4))
                path_edges+=len(path)
                if t==0 and kind//2==0:
                    assert_true(len(star)==1 and star[0].target==e2_source(2+kind%2))
    for reached in attained:
        assert_true(reached)
    var failed=False
    try:
        certify_e2_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        var p=chamber_parameters(-1)
        var i=qx_add(qx_add(p[0],p[0]),qx_const(3))
        var old: List[QX]=[qx_const(0),qx_const(0),qx_const(2)]
        _=symbolic_child(-1,0,0,old,RUN,i,FIRST,qx_const(0),2,0)
    except:
        failed=True
    assert_true(failed) # t=0 puts this supposed run at LAST x
    failed=False
    try:
        _=e2_child_allowed(4,0,0,0,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=e2_child_allowed(0,0,0,10,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=e2_rank(BoundaryLabel(0,0,0,0,0))
    except:
        failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    failed=False
    try:
        verify_e2_packet(tables,0,0,0,BoundaryEdge(9,0,chain_source(2)))
    except:
        failed=True
    assert_true(failed)
    var path=e2_path(0,0,0)
    path[1]=BoundaryEdge(0,0,path[1].target)
    failed=False
    try:
        verify_e2_path(tables,0,0,0,path)
    except:
        failed=True
    assert_true(failed)
    path=e2_path(0,0,0)
    path[len(path)-1]=BoundaryEdge(1,2,BoundaryLabel(2,1,0,0,0))
    failed=False
    try:
        verify_e2_path(tables,0,0,0,path)
    except:
        failed=True
    assert_true(failed)
    # t=3 LAST/FIRST exists in the high half only; all tested ordinals are real.
    assert_true(e2_child_allowed(0,0,3,18,0))
    assert_true(not e2_child_allowed(0,4,3,26,0))
    assert_true(e2_child_allowed(0,0,4,20,0))
    assert_true(not e2_child_allowed(0,5,4,30,0))
    print("CLASS_A_BOUNDARY_E2_FINITE members=56", "pairs",pairs,"accepted",accepted,
          "path_edges",path_edges,"union_labels=46", "all_four_sources_exit_within_five=true", "BH=false")
    require_contract("class-A minus E2/Dxx and real reversals: complete four first/run/last stars, exact 46-label chamber union, half-chamber guards and t0 unique LAST x, full Parikh/Perron every-pair replay and actual <=5-step typed coincidence; same-shift y/y disjoint versus x/y interior, wrong types/ordinals, universal fictitious run, symbolic corruption and broken paths refused; no forward closure or universal BH")
