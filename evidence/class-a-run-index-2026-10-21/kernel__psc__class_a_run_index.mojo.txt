"""Class A: an explicit seed-reachable recurrent family with unbounded hit depth.

The uniform proof is in docs/p1b-class-a-run-index-2026-10-21.md. Polynomial
identities are checked coefficient-wise, not inferred from this finite replay.
The replay uses the existing strict bottom-minus-top occurrence geometry.
"""
from std.collections import Dict
from a1_normal_form_census import class_member, CLASS_A
from psc.param_poly import QX, qx_const, qx_affine, qx_affine2, qx_add, qx_sub, qx_mul, qx_neg, qx_is_zero, qx_shift
from psc.exact import q_sign
from finite_linear_algebra.scalar import q_int
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, SeedOverlapAutomaton,
    build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables,
    first_left_aligned_depths, seed_overlap_states, selected_overlap_child,
    interior_overlap,
)
from psc.perron_field3 import CubicElt
from psc.vertex_coincidence import length_matrix, offset_vector
from psc.overlap_zipper import ordered_child_occurrences
from psc.overlap_obstruction import recurrent_sccs


def member(n: Int) raises -> List[List[Int]]:
    if n < 1 or n > 256:
        raise Error("class-A finite replay budget requires 1<=n<=256")
    return class_member(CLASS_A,n+1,n,n+1)


def _same(a: QX, b: QX) raises:
    if not qx_is_zero(qx_sub(a,b)):
        raise Error("class-A polynomial identity failed")


def _vec(x: QX, c: QX, y: QX) -> List[QX]:
    return [x.copy(),c.copy(),y.copy()]


def _prefix(parent: Int, part: Int, index: QX) raises -> List[QX]:
    # FIRST=0, RUN=1, LAST=2. Every nonempty proper prefix is
    # the parent's first letter followed by index-1 copies of y.
    if parent < 0 or parent > 2 or part < 0 or part > 2:
        raise Error("invalid symbolic occurrence type")
    if part == 0:
        _same(index,qx_const(0))
        return [qx_const(0),qx_const(0),qx_const(0)]
    return [qx_const(0 if parent==1 else 1),qx_const(1 if parent==1 else 0),qx_sub(index,qx_const(1))]


def _letter(parent: Int, part: Int) -> Int:
    if part == 0:
        return 1 if parent==1 else 0
    if part == 1:
        return 2
    return 1 if parent==2 else 0


def check_symbolic_edge(
    top: Int, bottom: Int, w: List[QX], ti: QX, bi: QX,
    tp: Int, bp: Int, ct: Int, cb: Int, want: List[QX],
) raises:
    """Typed affine identity in Q[n,k]. Bounds/geometry are separate obligations."""
    if len(w)!=3 or len(want)!=3:
        raise Error("three offset coordinates required")
    if _letter(top,tp)!=ct or _letter(bottom,bp)!=cb:
        raise Error("symbolic child type mismatch")
    var n = qx_affine(0,1)
    var np = qx_add(n,qx_const(1))
    var mw = _vec(qx_add(qx_add(w[0],w[0]),qx_add(w[1],w[2])),
                  qx_add(w[1],w[2]),
                  qx_add(qx_mul(np,qx_add(w[0],w[2])),qx_mul(n,w[1])))
    var a = _prefix(top,tp,ti)
    var b = _prefix(bottom,bp,bi)
    for d in range(3):
        _same(qx_add(mw[d],qx_sub(b[d],a[d])),want[d])


def _cubic(n: QX, t: QX) -> QX:
    var q=qx_add(n,qx_const(4))
    return qx_sub(qx_add(qx_sub(qx_mul(qx_mul(t,t),t),qx_mul(q,qx_mul(t,t))),qx_mul(q,t)),qx_const(2))


def verify_symbolic_identities() raises:
    var z=qx_const(0)
    var one=qx_const(1)
    var n=qx_affine(0,1)
    var k=qx_affine2(0,0,1)
    var kp=qx_add(k,one)
    var km=qx_sub(k,one)
    var np2=qx_add(n,qx_const(2))
    # Bootstrap from the actual (xc,cx) seed, then the two-edge ladder.
    check_symbolic_edge(1,0,_vec(qx_const(-1),one,z),z,one,0,1,1,2,_vec(z,one,qx_const(-1)))
    check_symbolic_edge(1,2,_vec(z,one,qx_const(-1)),z,one,0,1,1,2,_vec(one,z,qx_const(-1)))
    check_symbolic_edge(1,2,_vec(one,z,qx_const(-1)),one,one,1,1,2,2,_vec(qx_const(2),qx_const(-2),z))
    check_symbolic_edge(2,2,_vec(k,qx_neg(k),z),np2,qx_sub(np2,k),2,1,1,2,_vec(k,qx_neg(k),z))
    check_symbolic_edge(1,2,_vec(k,qx_neg(k),z),kp,one,1,1,2,2,_vec(kp,qx_neg(kp),z))
    # A_k -> B_k -> B_(k-1) is a constructive descending rank.
    check_symbolic_edge(1,2,_vec(k,qx_neg(k),z),k,z,1,0,2,0,_vec(k,qx_neg(kp),one))
    check_symbolic_edge(2,0,_vec(k,qx_neg(kp),one),kp,z,1,0,2,0,_vec(km,qx_neg(k),one))
    # B_k -> A_k closes a genuine cycle, while B_0 exits to coincidence.
    check_symbolic_edge(2,0,_vec(k,qx_neg(kp),one),np2,qx_sub(qx_add(n,one),k),2,1,1,2,_vec(k,qx_neg(k),z))
    check_symbolic_edge(2,0,_vec(z,qx_const(-1),one),qx_const(2),one,1,1,2,2,_vec(z,z,z))
    # Left eigenvector and characteristic cubic, now second variable t.
    var t=k.copy()
    var tm1=qx_sub(t,one)
    var tm2=qx_sub(t,qx_const(2))
    var lx=qx_mul(qx_add(n,one),tm1)
    var lc=qx_add(qx_mul(n,tm1),one)
    var ly=qx_mul(tm2,tm1)
    var chi=qx_sub(qx_add(qx_sub(qx_mul(qx_mul(t,t),t),qx_mul(qx_add(n,qx_const(4)),qx_mul(t,t))),qx_mul(qx_add(n,qx_const(4)),t)),qx_const(2))
    _same(qx_add(qx_add(lx,lx),qx_mul(qx_add(n,one),ly)),qx_mul(t,lx))
    _same(qx_add(qx_add(lx,lc),qx_mul(n,ly)),qx_mul(t,lc))
    _same(qx_add(qx_add(qx_add(lx,lc),qx_mul(qx_add(n,one),ly)),chi),qx_mul(t,ly))
    _same(qx_sub(lx,lc),tm2)
    _same(chi,_cubic(n,t))
    _same(_cubic(n,qx_const(0)),qx_const(-2))
    _same(_cubic(n,one),qx_const(-1))
    _same(_cubic(n,qx_const(-1)),qx_affine(-11,-2))
    _same(_cubic(n,qx_const(2)),qx_affine(-2,-2))
    _same(_cubic(n,qx_const(-2)),qx_affine(-34,-6))
    _same(_cubic(n,qx_add(n,qx_const(2))),qx_neg(qx_add(qx_add(qx_mul(n,n),qx_mul(qx_const(2),n)),qx_const(2))))
    _same(_cubic(n,qx_add(n,qx_const(3))),qx_add(n,one))
    # Cleared-denominator evaluation n^3 chi(1-2/n).
    var a=qx_sub(n,qx_const(2))
    var n2=qx_mul(n,n)
    var n3=qx_mul(n2,n)
    var raw=qx_sub(qx_add(qx_sub(qx_mul(qx_mul(a,a),a),qx_mul(qx_mul(qx_add(n,qx_const(4)),qx_mul(a,a)),n)),qx_mul(qx_mul(qx_add(n,qx_const(4)),a),n2)),qx_mul(qx_const(2),n3))
    var positive=qx_sub(qx_sub(qx_sub(n3,qx_mul(qx_const(2),n2)),qx_mul(qx_const(4),n)),qx_const(8))
    _same(raw,positive)
    var shifted=qx_shift(positive,4,0)
    for row in shifted:
        for coefficient in row:
            if q_sign(coefficient)<0:
                raise Error("root bracket positivity failed")
    _same(shifted,[[q_int(8),q_int(28),q_int(10),q_int(1)]])
    print("CLASS_A_SYMBOLIC_IDENTITIES bootstrap_ladder_cycle_descent=true eigenvector=true conjugate_bracket=true")


def labelled(tables: SeedOverlapTables, top: Int, bottom: Int, x: Int, c: Int, y: Int) raises -> OverlapState:
    var v=length_matrix(tables).apply([x,c,y])
    return OverlapState(top,bottom,CubicElt(v[0],v[1],v[2]))


def checked_step(tables: SeedOverlapTables, parent: OverlapState, ti: Int, bi: Int, expected: OverlapState) raises -> OverlapState:
    if not interior_overlap(tables,parent):
        raise Error("source is not a strict overlap")
    var child=selected_overlap_child(tables,parent,ti,bi)
    if child!=expected:
        raise Error("ordered occurrence does not reach expected label")
    if not interior_overlap(tables,child):
        raise Error("child is boundary-only or disjoint")
    return child


def replay_family(n: Int, verbose: Bool=False) raises -> Int:
    if n<4:
        raise Error("uniform family replay requires n>=4")
    var tables=build_seed_overlap_tables_screened(member(n))
    var s=labelled(tables,1,0,-1,1,0)
    var found=False
    for v in seed_overlap_states(tables):
        found=found or v==s
    if not found:
        raise Error("bootstrap is not an actual swap seed")
    s=checked_step(tables,s,0,1,labelled(tables,1,2,0,1,-1))
    s=checked_step(tables,s,0,1,labelled(tables,1,2,1,0,-1))
    s=checked_step(tables,s,1,1,labelled(tables,2,2,2,-2,0))
    s=checked_step(tables,s,n+2,n,labelled(tables,1,2,2,-2,0))
    for k in range(2,n):
        s=checked_step(tables,s,k+1,1,labelled(tables,2,2,k+1,-k-1,0))
        s=checked_step(tables,s,n+2,n+1-k,labelled(tables,1,2,k+1,-k-1,0))
    var start=s
    s=checked_step(tables,s,n,0,labelled(tables,2,0,n,-n-1,1))
    _=checked_step(tables,s,n+2,1,start)
    # This path leaves the recurrent two-cycle. It is not an obstruction to BH.
    for k in range(n,0,-1):
        s=checked_step(tables,s,k+1,0,labelled(tables,2,0,k-1,-k,1))
    s=checked_step(tables,s,2,1,labelled(tables,2,2,0,0,0))
    if not s.is_coincidence():
        raise Error("family descent did not reach equal-letter coincidence")
    if verbose:
        print("FAMILY",n,"seed_steps",2*n,"cycle_steps",2,"hit_upper",n+2,"hit_lower_strict",n,"/10")
    return n+2


def complete_graph(n: Int, cap: Int=20000) raises -> SeedOverlapAutomaton:
    if cap<1 or cap>20000:
        raise Error("state budget requires 1..20000")
    var tables=build_seed_overlap_tables_screened(member(n))
    var g=build_seed_overlap_graph_from_tables(tables,cap)
    if g.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no hitting verdict")
    return g^


def probe(n: Int, export: Bool=False) raises -> List[Int]:
    var tables=build_seed_overlap_tables_screened(member(n))
    var g=complete_graph(n)
    var ds=first_left_aligned_depths(g)
    var lm=length_matrix(tables)
    var index=Dict[OverlapState,Int]()
    for i in range(g.size()):
        index[g.states[i]]=i
    var maximum=0
    var recurrent=0
    var rec_max=0
    var cs=recurrent_sccs(g)
    for c in cs:
        recurrent+=len(c)
        for i in c:
            rec_max=max(rec_max,ds[i])
    var witness=-1
    for i in range(g.size()):
        if ds[i]<0:
            raise Error("complete graph has a nonhitting state")
        maximum=max(maximum,ds[i])
        var v=g.states[i]
        var w=offset_vector(lm,v.shift)
        if v.top==1 and v.bottom==2 and w==List[Int]([n,-n,0]):
            witness=i
        if export:
            print("V",n,i,v.top,v.bottom,w[0],w[1],w[2],ds[i])
    if n>=4:
        if witness<0 or 10*ds[witness]<=n or ds[witness]>n+2:
            raise Error("explicit family or proved bounds disagree with complete graph")
    if export:
        for seed in seed_overlap_states(tables):
            print("SEED",n,index[seed])
        for i in range(g.size()):
            if g.states[i].is_coincidence():
                continue
            for e in ordered_child_occurrences(tables,g.states[i]):
                print("E",n,i,index[e.state],e.top_index,e.bottom_index)
    var wd=ds[witness] if witness>=0 else -1
    print("SUMMARY",n,g.size(),maximum,recurrent,rec_max,wd)
    return [g.size(),maximum,recurrent,rec_max,wd]
