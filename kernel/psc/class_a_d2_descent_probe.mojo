"""Exact finite d2 descent-witness replay; no parameter-uniform promotion.

Every seed-graph state from a complete exact graph is either already at
offset zero or has an actual directed child of strictly smaller FIRST
offset-zero distance. This is a finite certificate only. Future work must
replace finite first-hit distances by an affine, parity-dependent potential
with a quantified all-n child-occurrence proof.
"""
from psc.class_a_d2_parity_carrier import specimen
from psc.class_a_run_index import labelled
from psc.overlap_seed_patch import selected_overlap_child, interior_overlap, inferred_template
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened,build_seed_overlap_graph_from_tables,
    first_left_aligned_depths,
)
from psc.vertex_coincidence import length_matrix, offset_vector


def finite_d2_descent(n: Int) raises -> List[Int]:
    if n<4 or n>24:
        raise Error("finite d2 descent replay restricted to 4<=n<=24")
    var tables=build_seed_overlap_tables_screened(specimen(n))
    var g=build_seed_overlap_graph_from_tables(tables,20000)
    if g.capped:
        raise Error("D2_STATE_BUDGET_EXHAUSTED: no descent verdict")
    var depths=first_left_aligned_depths(g)
    if len(depths)!=g.size():
        raise Error("missing complete first-hit vector")
    var lm=length_matrix(tables)
    var zero=0
    var nonzero=0
    var maxdepth=0
    var centered=0
    var centerleft=-1
    var centermiddle=-1
    var centerright=-1
    for i in range(g.size()):
        var state=g.states[i]
        var d=depths[i]
        if d<0:
            raise Error("nonhitting exact finite d2 vertex")
        maxdepth=max(maxdepth,d)
        var w=offset_vector(lm,state.shift)
        if len(w)!=3:
            raise Error("bad integral offset dimension")
        if state.top==0 and state.bottom==0 and w[2]==0 and w[0]+w[1]==0:
            if w[0]==-1:
                centerleft=d
                centered+=1
            elif w[0]==0:
                centermiddle=d
                centered+=1
            elif w[0]==1:
                centerright=d
                centered+=1
        if state.shift.is_zero():
            zero+=1
            if d!=0:
                raise Error("zero shift must have first-hit depth zero")
            continue
        nonzero+=1
        var has_strict_child=False
        for child_id in g.adj[i]:
            if child_id<0 or child_id>=g.size():
                raise Error("malformed d2 actual child index")
            if depths[child_id]==d-1:
                has_strict_child=True
                break
        if not has_strict_child:
            raise Error("nonzero finite d2 state has no descending actual child")
    if centered!=3 or centerleft!=2 or centermiddle!=0 or centerright!=2:
        raise Error("d2 target-slice depth 2/0/2 regression")
    if zero!=8 or zero+nonzero!=g.size():
        raise Error("d2 finite offset-zero target count changed")
    print("CLASS_A_D2_FINITE_DESCENT", "n",n,"states",g.size(),
          "offset_zero_targets",zero,"nonzero_states",nonzero,
          "max_first_hit",maxdepth,"centered_row_depths=2,0,2",
          "all_selected_edges_real=true","uniform_parameter_proof=false")
    return [g.size(),zero,nonzero,maxdepth,centered]


def finite_d2_descent_replay() raises:
    for n in [7,8,9,10,11,12]:
        _=finite_d2_descent(n)
    print("D2_PARITY_DESCENT_PROBE", "finite_n=7..12", "all-n_rank=not_proved")


def uniform_centered_slice_obstruction(rows: List[List[Int]]) raises -> List[Int]:
    """A uniformly valid target-normalized rank cannot be affine in k on
    the complete x/x, s=y=0 three-point slice {k=-1,0,+1}.

    If X(k)=A*n+B*k+C and X(0)=0, then X(-1)=-B and X(1)=B.
    They cannot both be >=1, as a nonnegative integer potential whose
    every non-target step strictly lowers X must require. This does not
    exclude piecewise potentials or a rank with nonzero target value.
    """
    var found=False
    for row in rows:
        if len(row)==8 and row[0]==0 and row[1]==0 and row[2]==0 and row[3]==0:
            if row[4]==0 and row[5]==-1 and row[6]==0 and row[7]==1:
                found=True
    if not found:
        raise Error("missing universally valid three-point d2 target slice")
    # An affine rank with center zero has endpoints -B and B. The
    # inequalities -B>=1 and B>=1 are integer-inconsistent: 0>=2.
    if 0>=2:
        raise Error("unexpected inconsistent arithmetic invariant")
    print("CLASS_A_D2_TARGET_NORMALIZED_AFFINE_OBSTRUCTION",
          "typed_slice=(x,x,0,0)", "k=-1,0,+1",
          "rank_affine_in_k_on_entire_slice=false",
          "piecewise_potential_required_if_target_zero=true")
    return [3,1]


def uniform_centered_slice_replay() raises:
    _=uniform_centered_slice_obstruction(inferred_template(8,12))
    _=uniform_centered_slice_obstruction(inferred_template(9,13))


# ---------------------------------------------------------------------------
# Genuine uniform all-n two-occurrence paths in the central typed slice.
# These do NOT solve descent on the rest of the parity carrier.
# ---------------------------------------------------------------------------

def _two_step_prefix(index: Int) raises -> List[Int]:
    """For x or y at indices 0,1,2 (n>=4), the proper prefixes are
    empty, x, x*y. All corresponding child letters are x,y,y."""
    if index==0:
        return [0,0,0]
    if index==1:
        return [1,0,0]
    if index==2:
        return [1,0,1]
    raise Error("only uniformly valid low prefix indices 0,1,2")


def _two_step_child(parent: List[Int], ti: Int, bi: Int) raises -> List[Int]:
    """Exact d2 incidence and proper-prefix identity for every integer n.

    Every state used below has s=k+c+y=0, so the coefficient of n in
    M*w=(k+s,s-k,n*s+2*k+y) vanishes symbolically. This is the
    exact all-parameter (not sampled) child transformation.
    """
    if len(parent)!=5 or (parent[0]!=0 and parent[0]!=2) or (
        parent[1]!=0 and parent[1]!=2):
        raise Error("uniform path requires x/y parent letters")
    var k=parent[2]
    var c=parent[3]
    var y=parent[4]
    var s=k+c+y
    if s!=0:
        raise Error("uniform path cancellation requires zero coordinate sum")
    var a=_two_step_prefix(ti)
    var b=_two_step_prefix(bi)
    var top=0 if ti==0 else 2
    var bottom=0 if bi==0 else 2
    return [top,bottom,k+s+b[0]-a[0],s-k+b[1]-a[1],
            2*k+y+b[2]-a[2]]


def _positive_strict_margin(poly: List[Int]) raises:
    """Proof f(h)>0 for every h>0: positive constant and other
    coefficients nonnegative. This checks the exact d2 Perron lengths."""
    if len(poly)!=3 or poly[0]<=0 or poly[1]<0 or poly[2]<0:
        raise Error("uniform d2 chosen path does not have proved strict overlap")


def _strict_real_uniform(vertex: List[Int]) raises:
    """With d=2,eps=1, L=(1+2h+2h²,1,1+h) in a common positive scale."""
    if len(vertex)!=5:
        raise Error("malformed d2 path label")
    var t=vertex[0]
    var b=vertex[1]
    if t<0 or t>2 or b<0 or b>2:
        raise Error("wrong chosen path letter")
    var L=List[List[Int]]([[1,2,2],[1,0,0],[1,1,0]])
    var k=vertex[2]
    var c=vertex[3]
    var y=vertex[4]
    var shift=List[Int]([k+c+y,2*k+y,2*k])
    var left=List[Int]()
    var right=List[Int]()
    for j in range(3):
        left.append(L[b][j]+shift[j])
        right.append(L[t][j]-shift[j])
    _positive_strict_margin(left)
    _positive_strict_margin(right)


def certify_d2_uniform_center_paths() raises -> List[Int]:
    """Both nonzero centered x/x states hit (y,y,0) in exactly two
    *explicit actual proper-prefix occurrence steps* for all n>=4."""
    var l=List[Int]([0,0,-1,1,0])
    var l1=List[Int]([0,2,0,1,-1])
    var r=List[Int]([0,0,1,-1,0])
    var r1=List[Int]([2,0,0,-1,1])
    var target=List[Int]([2,2,0,0,0])
    for st in [l.copy(),l1.copy(),r.copy(),r1.copy(),target.copy()]:
        _strict_real_uniform(st)
    if _two_step_child(l,0,2)!=l1:
        raise Error("left centered path first symbolic occurrence changed")
    if _two_step_child(l1,1,2)!=target:
        raise Error("left centered path second symbolic occurrence changed")
    if _two_step_child(r,2,0)!=r1:
        raise Error("right centered path first symbolic occurrence changed")
    if _two_step_child(r1,2,1)!=target:
        raise Error("right centered path second symbolic occurrence changed")
    # Every index 0,1,2 exists for x and y when n>=4 by their exact word
    # definitions. Above coefficient identities have NO remaining n-term.
    print("CLASS_A_D2_UNIFORM_TWO_STEP", "n>=4",
          "from_left=(x,x,-1,1,0):[0,2],[1,2]",
          "from_right=(x,x,1,-1,0):[2,0],[2,1]",
          "target=(y,y,0,0,0)", "strict=true",
          "all_n_hitting=false")
    return [2,4,5]


def replay_d2_center_paths(n: Int) raises:
    """Independent finite differential replay against exact proper-prefix
    reader. Not used as a substitute for the symbolic all-n argument."""
    if n<4 or n>24:
        raise Error("finite differential replay budget 4<=n<=24")
    from psc.class_a_run_index import labelled
    from psc.overlap_seed_patch import selected_overlap_child, interior_overlap
    var tables=build_seed_overlap_tables_screened(specimen(n))
    for sign in [-1,1]:
        var src=labelled(tables,0,0,sign,-sign,0)
        var first_t=0 if sign<0 else 2
        var first_b=2 if sign<0 else 0
        var mid_t=0 if sign<0 else 2
        var mid_b=2 if sign<0 else 0
        var middle_y=-1 if sign<0 else 1
        var middle_c=1 if sign<0 else -1
        var mid=labelled(tables,mid_t,mid_b,0,middle_c,middle_y)
        var target=labelled(tables,2,2,0,0,0)
        if not interior_overlap(tables,src) or not interior_overlap(tables,mid):
            raise Error("d2 finite centered path has non-strict member")
        var first=selected_overlap_child(tables,src,first_t,first_b)
        if first!=mid:
            raise Error("d2 finite centered path first exact occurrence differs")
        var second_t=1 if sign<0 else 2
        var second_b=2 if sign<0 else 1
        var second=selected_overlap_child(tables,mid,second_t,second_b)
        if second!=target:
            raise Error("d2 finite centered path second exact occurrence differs")
    print("CLASS_A_D2_CENTERED_FINITE_DIFFERENTIAL", "n",n,
          "both_paths_exact=true")
