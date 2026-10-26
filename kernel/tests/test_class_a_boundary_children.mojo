"""Exhaustive finite occurrence/field checks of the complete symbolic seed star."""
from std.testing import assert_true
from std.collections import Dict
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, certify_seed_star, check_boundary_member,
    boundary_r, member_transport, seed_child_allowed, seed_star,
    geometric_state, verify_member_edge,
)
from psc.overlap_seed_patch import (
    SeedOverlapTables, build_seed_overlap_tables_screened,
    selected_overlap_child, interior_overlap_cached,
)
from psc.perron_field3 import CubicElt


def _literal(tables: SeedOverlapTables, n: Int, d: Int, eps: Int,
             parent: BoundaryLabel, i: Int, j: Int) raises -> BoundaryLabel:
    # Deliberately independent literal-word prefix accumulation.
    var a: List[Int]=[0,0,0]
    var b: List[Int]=[0,0,0]
    for z in range(i):
        a[tables.sigma[parent.top][z]]+=1
    for z in range(j):
        b[tables.sigma[parent.bottom][z]]+=1
    return BoundaryLabel(tables.sigma[parent.top][i],tables.sigma[parent.bottom][j],
        2*parent.x+parent.c+parent.y+b[0]-a[0],
        parent.c+parent.y+b[1]-a[1],
        (n+d)*parent.x+n*parent.c+(n+eps)*parent.y+b[2]-a[2])


def _specimen(eps: Int, k: Int, t: Int, second_step: Bool) raises -> Int:
    var n=k+3+t if eps==-1 else 2*(k+2)+t
    var d=2*n+6*eps+5-k
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n+eps))
    var root=BoundaryLabel(0,1,0,0,0)
    var source=geometric_state(tables,root)
    var cache=Dict[CubicElt,Int]()
    var edges=seed_star(eps,k,n,d)
    var found=0
    var pairs=0
    for i in range(n+d+2):
        for j in range(n+2):
            pairs+=1
            var packet=member_transport(eps,k,n,d,root,i,j)
            assert_true(packet==_literal(tables,n,d,eps,root,i,j))
            var actual=selected_overlap_child(tables,source,i,j)
            assert_true(actual==geometric_state(tables,packet))
            var overlaps=interior_overlap_cached(tables,cache,actual)
            assert_true(overlaps==seed_child_allowed(eps,k,n,d,i,j))
            if overlaps:
                found+=1
    assert_true(found==len(edges))
    var labels=List[BoundaryLabel]()
    for edge in edges:
        assert_true(seed_child_allowed(eps,k,n,d,edge.i,edge.j))
        verify_member_edge(tables,eps,k,n,d,root,edge.i,edge.j,edge.target)
        var seen=False
        for label in labels:
            if label==edge.target:
                seen=True
        if not seen:
            labels.append(edge.target)
    var r=boundary_r(eps,k)
    assert_true(len(labels)==2*r+(7 if eps==-1 else 6))
    # A valid word pair, valid full transport, but disjoint geometry.
    var failed=False
    try:
        verify_member_edge(tables,eps,k,n,d,root,1,1,BoundaryLabel(2,2,-1,1,0))
    except:
        failed=True
    assert_true(failed)
    # Crucial determinant-sign-specific final run/last boundary.
    assert_true(seed_child_allowed(eps,k,n,d,n+2,n+1)==(eps==-1))
    # Wrong coordinate AND wrong child letter are independently refused.
    for bad in [BoundaryLabel(0,2,0,1,1),BoundaryLabel(2,2,0,1,0)]:
        failed=False
        try:
            verify_member_edge(tables,eps,k,n,d,root,0,1,bad)
        except:
            failed=True
        assert_true(failed)
    if second_step:
        var next_edges=0
        var escapes=0
        for label in labels:
            if label.top!=2 or label.bottom!=2:
                continue
            var state=geometric_state(tables,label)
            for i in range(n+eps+2):
                for j in range(n+eps+2):
                    var packet=member_transport(eps,k,n,d,label,i,j)
                    assert_true(packet==_literal(tables,n,d,eps,label,i,j))
                    # Every prefix of sigma(y) has c-coordinate zero.
                    assert_true(packet.c==label.y+1)
                    assert_true(packet.c>label.c)
                    var actual=selected_overlap_child(tables,state,i,j)
                    assert_true(actual==geometric_state(tables,packet))
                    if interior_overlap_cached(tables,cache,actual):
                        verify_member_edge(tables,eps,k,n,d,label,i,j,packet)
                        next_edges+=1
                        var inside=False
                        for known in labels:
                            if known==packet:
                                inside=True
                        if not inside:
                            escapes+=1
        assert_true(next_edges>0 and escapes==next_edges)
        print("CLASS_A_BOUNDARY_SECOND_STEP eps",eps,"k",k,"t",t,
              "T_m_occurrences",next_edges,"outside_seed_star",escapes,
              "closed_carrier=false", "BH=false")
    print("CLASS_A_BOUNDARY_STAR_MEMBER eps",eps,"k",k,"t",t,
          "pairs",pairs,"occurrences",found,"labels",len(labels))
    return pairs


def main() raises:
    certify_seed_star()
    var total=0
    for eps in [-1,1]:
        for k in [0,3,4]:
            for t in [0,2]:
                total+=_specimen(eps,k,t,t==0 and (k==0 or (eps==1 and k==4)))
    for i in [-1,10]:
        var failed=False
        try:
            _=seed_child_allowed(-1,0,3,5,i,0)
        except:
            failed=True
        assert_true(failed)
    var failed=False
    try:
        check_boundary_member(1,0,4,18)
    except:
        failed=True
    assert_true(failed)
    # Exact endpoint contacts are refused by the same strict predicate.
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var cache=Dict[CubicElt,Int]()
    assert_true(not interior_overlap_cached(tables,cache,
        geometric_state(tables,BoundaryLabel(0,0,1,0,0))))
    assert_true(not interior_overlap_cached(tables,cache,
        geometric_state(tables,BoundaryLabel(0,0,-1,0,0))))
    print("CLASS_A_BOUNDARY_STAR_FINITE members=12 pairs",total,
          "universal_evidence=false")
    require_contract("class-A boundary aligned seed complete first/run/last outgoing star; symbolic prefix endpoints; all finite occurrence pairs match exact Perron geometry; typed full-Parikh target packets and invalid geometry refused; T_m successors escape one-step star; no closed carrier or BH")
