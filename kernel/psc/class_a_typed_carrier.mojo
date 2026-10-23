"""Typed semilinear candidate for the unbounded class-A seed carrier (#139).

The 89 affine intervals are synthesized from exact complete n=4 and n=18
graph exports and are *not* a uniform-in-n theorem. In particular, the
finite verifier below must not be mistaken for an all-n closure proof.
Source and rejection notes: docs/class-a-typed-carrier-2026-10-21.md.
"""
from std.collections import Dict
from psc.class_a_run_index import labelled
from psc.class_a_line import ALine, plus_line
from psc.overlap_seed_patch import (
    OverlapState, build_seed_overlap_tables_screened,
    build_seed_overlap_graph_from_tables, first_left_aligned_depths,
    interior_overlap, seed_overlap_states,
)
from psc.overlap_zipper import ordered_child_occurrences_cached
from psc.perron_field3 import CubicElt


def template_rows() -> List[List[Int]]:
    """Rows: top,bottom,sum(w),w_y,k_lower_slope,k_lower_constant,k_upper_slope,k_upper_constant."""
    return List[List[Int]]([
        List[Int]([0,0,-1,-1,0,0,0,1]),
        List[Int]([0,0,-1,0,0,0,0,0]),
        List[Int]([0,0,-1,0,1,-1,1,0]),
        List[Int]([0,0,-1,1,1,-1,1,-1]),
        List[Int]([0,0,0,-1,-1,0,-1,0]),
        List[Int]([0,0,0,-1,0,-1,0,1]),
        List[Int]([0,0,0,0,0,-1,0,1]),
        List[Int]([0,0,0,1,0,-1,0,1]),
        List[Int]([0,0,0,1,1,0,1,0]),
        List[Int]([0,0,1,-1,-1,1,-1,1]),
        List[Int]([0,0,1,0,-1,0,-1,1]),
        List[Int]([0,0,1,0,0,0,0,0]),
        List[Int]([0,0,1,1,0,-1,0,0]),
        List[Int]([0,1,-1,-1,0,1,0,1]),
        List[Int]([0,1,-1,0,0,1,0,1]),
        List[Int]([0,1,-1,0,1,-1,1,-1]),
        List[Int]([0,1,-1,1,1,-1,1,0]),
        List[Int]([0,1,0,-1,-1,1,-1,1]),
        List[Int]([0,1,0,-1,0,-1,0,0]),
        List[Int]([0,1,0,0,0,-1,0,2]),
        List[Int]([0,1,0,1,0,-1,0,1]),
        List[Int]([0,1,1,0,-1,1,-1,2]),
        List[Int]([0,1,1,0,0,0,0,0]),
        List[Int]([0,1,1,1,0,-1,0,0]),
        List[Int]([0,2,-1,-1,0,1,1,0]),
        List[Int]([0,2,-1,-2,0,1,0,1]),
        List[Int]([0,2,-1,0,0,0,1,0]),
        List[Int]([0,2,0,-1,-1,0,0,2]),
        List[Int]([0,2,0,-2,-1,1,0,1]),
        List[Int]([0,2,0,0,0,0,1,1]),
        List[Int]([0,2,0,1,0,0,1,0]),
        List[Int]([0,2,1,-1,-1,1,0,1]),
        List[Int]([0,2,1,0,-1,1,0,0]),
        List[Int]([1,0,-1,-1,0,0,0,1]),
        List[Int]([1,0,-1,0,0,0,0,0]),
        List[Int]([1,0,-1,0,1,-2,1,-1]),
        List[Int]([1,0,0,-1,0,-1,0,1]),
        List[Int]([1,0,0,0,0,-2,0,1]),
        List[Int]([1,0,0,1,0,0,0,1]),
        List[Int]([1,0,0,1,1,-1,1,-1]),
        List[Int]([1,0,1,-1,-1,0,-1,1]),
        List[Int]([1,0,1,0,-1,1,-1,1]),
        List[Int]([1,0,1,0,0,-1,0,-1]),
        List[Int]([1,0,1,1,0,-1,0,-1]),
        List[Int]([1,1,-1,0,0,1,0,1]),
        List[Int]([1,1,-1,0,1,-2,1,-2]),
        List[Int]([1,1,-1,1,1,-1,1,-1]),
        List[Int]([1,1,0,-1,-1,1,-1,1]),
        List[Int]([1,1,0,-1,0,-1,0,0]),
        List[Int]([1,1,0,1,0,0,0,1]),
        List[Int]([1,1,0,1,1,-1,1,-1]),
        List[Int]([1,1,1,-1,-1,1,-1,1]),
        List[Int]([1,1,1,0,-1,2,-1,2]),
        List[Int]([1,1,1,0,0,-1,0,-1]),
        List[Int]([1,2,-1,-1,0,1,1,0]),
        List[Int]([1,2,-1,-2,0,1,0,1]),
        List[Int]([1,2,-1,0,0,0,1,0]),
        List[Int]([1,2,0,-1,-1,1,0,2]),
        List[Int]([1,2,0,-2,-1,0,0,1]),
        List[Int]([1,2,0,0,0,-1,1,0]),
        List[Int]([1,2,0,1,0,1,1,0]),
        List[Int]([1,2,1,-1,-1,0,0,0]),
        List[Int]([1,2,1,0,-1,2,0,-1]),
        List[Int]([2,0,-1,0,0,0,1,-1]),
        List[Int]([2,0,-1,1,0,-1,1,-1]),
        List[Int]([2,0,0,-1,-1,0,0,0]),
        List[Int]([2,0,0,0,-1,-1,0,0]),
        List[Int]([2,0,0,1,0,-2,1,0]),
        List[Int]([2,0,0,2,0,-1,1,-1]),
        List[Int]([2,0,1,0,-1,0,0,0]),
        List[Int]([2,0,1,1,-1,0,0,-1]),
        List[Int]([2,0,1,2,0,-1,0,-1]),
        List[Int]([2,1,-1,0,0,1,1,-2]),
        List[Int]([2,1,-1,1,0,0,1,0]),
        List[Int]([2,1,0,-1,-1,0,0,-1]),
        List[Int]([2,1,0,0,-1,0,0,1]),
        List[Int]([2,1,0,1,0,-2,1,-1]),
        List[Int]([2,1,0,2,0,-1,1,0]),
        List[Int]([2,1,1,0,-1,0,0,0]),
        List[Int]([2,1,1,1,-1,0,0,-1]),
        List[Int]([2,1,1,2,0,-1,0,-1]),
        List[Int]([2,2,-1,-1,0,1,1,-1]),
        List[Int]([2,2,-1,0,0,0,0,0]),
        List[Int]([2,2,-1,1,0,-1,1,0]),
        List[Int]([2,2,0,-2,-1,0,0,0]),
        List[Int]([2,2,0,0,-1,0,1,0]),
        List[Int]([2,2,0,2,0,0,1,0]),
        List[Int]([2,2,1,-1,-1,0,0,1]),
        List[Int]([2,2,1,1,-1,1,0,-1]),
    ])


def contains_rows(
    n: Int, rows: List[List[Int]], top: Int, bottom: Int,
    k: Int, c: Int, y: Int,
) raises -> Bool:
    if n < 4:
        raise Error("typed class-A template requires n>=4")
    for row in rows:
        if len(row) != 8:
            raise Error("malformed typed carrier interval")
        if row[0] == top and row[1] == bottom and row[2] == k+c+y and row[3] == y:
            if k >= row[4]*n+row[5] and k <= row[6]*n+row[7]:
                return True
    return False


def contains(n: Int, top: Int, bottom: Int, k: Int, c: Int, y: Int) raises -> Bool:
    return contains_rows(n,template_rows(),top,bottom,k,c,y)


def certify_finite_rows(n: Int, rows: List[List[Int]]) raises -> List[Int]:
    return certify_finite_line(plus_line(),n,rows,40,115)


def certify_finite_line(line: ALine, n: Int, rows: List[List[Int]], slope: Int, constant: Int) raises -> List[Int]:
    """EXACT finite replay only; n is explicitly bounded. No universal promotion.
    `slope n + constant` is the carrier cardinality from its affine row identity."""
    if n < 4 or n > 160:
        raise Error("finite typed-carrier replay permits 4<=n<=160")
    var tables=build_seed_overlap_tables_screened(line.member(n))
    var sign_cache = Dict[CubicElt, Int]()   # one exact sign cache for every edge enumeration
    var ln=line.l_of(n)   # rows are affine in l = (n - r)/d
    var g=build_seed_overlap_graph_from_tables(tables,20000)
    if g.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no typed-carrier verdict")
    var candidate=Dict[OverlapState,Int]()
    for row in rows:
        if len(row)!=8 or row[0]<0 or row[0]>2 or row[1]<0 or row[1]>2:
            raise Error("invalid typed-carrier row")
        var lo=row[4]*ln+row[5]
        var hi=row[6]*ln+row[7]
        if lo>hi:
            raise Error("empty affine interval")
        for k in range(lo,hi+1):
            var y=row[3]
            var c=row[2]-k-y
            var st=labelled(tables,row[0],row[1],k,c,y)
            if st in candidate:
                raise Error("overlapping carrier intervals")
            if not interior_overlap(tables,st):
                raise Error("typed carrier contains a non-strict overlap")
            candidate[st]=1
    if len(candidate)!=slope*ln+constant:
        raise Error("typed carrier candidate count disagrees with affine identity")
    if g.size()!=len(candidate):
        raise Error("finite seed graph cardinality differs from typed candidate")
    # Equal finite cardinalities plus graph inclusion imply label-set equality.
    for st in g.states:
        if st not in candidate:
            raise Error("seed graph escapes typed carrier")
        if st.is_coincidence():
            continue
        for occurrence in ordered_child_occurrences_cached(tables, sign_cache, st):
            if occurrence.state not in candidate:
                raise Error("finite ordered occurrence escapes typed candidate")
    for seed in seed_overlap_states(tables):
        if seed not in candidate:
            raise Error("swap seed omitted from typed candidate")
    var depths=first_left_aligned_depths(g)
    var deepest=0
    for depth in depths:
        if depth<0:
            raise Error("finite candidate has a non-hitting seed descendant")
        deepest=max(deepest,depth)
    var tag="" if line.eps==1 and line.d==1 else " line="+line.name()
    print("CLASS_A_TYPED_CARRIER_FINITE"+tag,n,"candidate",len(candidate),"graph",g.size(),"max_hit",deepest,"uniform_closure=false")
    return [len(candidate),g.size(),deepest]


def certify_finite(n: Int) raises -> List[Int]:
    return certify_finite_rows(n,template_rows())
