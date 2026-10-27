"""Independent every-pair geometry, selected seed path and invalid controls."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, member_transport, geometric_state, verify_member_edge,
)
from psc.class_a_boundary_w_children import (
    W, Z, X, Q, certify_w_children, local_source, local_child_allowed,
    local_child_star, verify_local_packet, local_target_envelope,
    selected_path_label, selected_path_rank, typed_coincidence,
    minus_seed_path, verify_minus_seed_path,
)
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def main() raises:
    certify_w_children()
    var pairs=0
    var accepted=0
    var members=0
    var path_edges=0
    var envelope=local_target_envelope()
    var attained=List[Bool]()
    for _ in envelope:
        attained.append(False)
    for k in range(8):
        for t in range(7):
            members+=1
            var n=k+3+t
            var d=2*n-1-k
            var A=n+d
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,A,n,n-1))
            var cache=Dict[CubicElt,Int]()
            var path=minus_seed_path(k,t)
            verify_minus_seed_path(tables,k,t,path)
            path_edges+=len(path)
            # Every member also has this cycle; its existence does not exclude
            # the distinct W->Q->typed-coincidence exit just verified.
            verify_member_edge(tables,-1,k,n,d,selected_path_label(3),n,0,local_source(W))
            verify_local_packet(tables,W,k,t,BoundaryEdge(0,0,local_source(Z)))
            verify_local_packet(tables,Z,k,t,BoundaryEdge(n+1,0,local_source(X)))
            verify_local_packet(tables,X,k,t,BoundaryEdge(d,0,selected_path_label(3)))
            for kind in range(4):
                var parent=local_source(kind)
                var source=geometric_state(tables,parent)
                assert_true(interior_overlap_cached(tables,cache,source))
                var R=A if kind==X else (n-1 if kind==Q else n)
                var edges=local_child_star(kind,k,t)
                var expected=1 if kind==Z else (n+3 if kind==Q else 2*n+3)
                assert_true(len(edges)==expected)
                var seen=Dict[Int,Bool]()
                for edge in edges:
                    var key=edge.i*(A+2)+edge.j
                    assert_true(key not in seen)
                    seen[key]=True
                    verify_local_packet(tables,kind,k,t,edge)
                    var found=False
                    for z in range(len(envelope)):
                        if edge.target==envelope[z]:
                            attained[z]=True
                            found=True
                    assert_true(found)
                for i in range(R+2):
                    for j in range(A+2):
                        pairs+=1
                        var target=member_transport(-1,k,n,d,parent,i,j)
                        var actual=selected_overlap_child(tables,source,i,j)
                        assert_true(actual==geometric_state(tables,target))
                        var overlaps=interior_overlap_cached(tables,cache,actual)
                        assert_true(overlaps==local_child_allowed(kind,k,t,i,j))
                        assert_true(overlaps==(i*(A+2)+j in seen))
                        if overlaps:
                            accepted+=1
    for reached in attained:
        assert_true(reached)
    assert_true(typed_coincidence(BoundaryLabel(2,2,0,0,0)))
    assert_true(not typed_coincidence(BoundaryLabel(1,2,0,0,0)))
    assert_true(not typed_coincidence(BoundaryLabel(2,2,0,0,1)))
    var failed=False
    try:
        certify_w_children(True)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=local_child_allowed(W,0,0,5,0)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        _=selected_path_rank(local_source(Z))
    except:
        failed=True
    assert_true(failed)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var path=minus_seed_path(0,0)
    # Final coincidence alone cannot validate a broken intermediate packet.
    path[2]=BoundaryEdge(1,1,selected_path_label(3))
    failed=False
    try:
        verify_minus_seed_path(tables,0,0,path)
    except:
        failed=True
    assert_true(failed)
    path=minus_seed_path(0,0)
    path[5]=BoundaryEdge(1,2,BoundaryLabel(1,2,0,0,0))
    failed=False
    try:
        verify_minus_seed_path(tables,0,0,path)
    except:
        failed=True
    assert_true(failed)
    failed=False
    try:
        verify_local_packet(tables,Q,0,0,BoundaryEdge(0,2,
            member_transport(-1,0,3,5,local_source(Q),0,2)))
    except:
        failed=True
    assert_true(failed)
    print("CLASS_A_BOUNDARY_W_FINITE members",members,"pairs",pairs,
          "accepted",accepted,"selected_path_edges",path_edges,
          "union_labels=17", "six_step_seed_coincidence=true", "BH=false")
    require_contract("class-A minus W/Z/X/Q complete actual child stars, indexed affine polynomial certificates, all finite pairs against exact Parikh/Perron geometry, exact 17-label image, six-step physical seed coincidence with stage-rank restricted to selected packet; false typed coincidence and broken intermediate path rejected; no universal BH or closed obstruction")
