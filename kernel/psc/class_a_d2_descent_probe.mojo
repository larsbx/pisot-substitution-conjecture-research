"""Exact finite d2 descent-witness replay; no parameter-uniform promotion.

Every seed-graph state from a complete exact graph is either already at
offset zero or has an actual directed child of strictly smaller FIRST
offset-zero distance. This is a finite certificate only. Future work must
replace finite first-hit distances by an affine, parity-dependent potential
with a quantified all-n child-occurrence proof.
"""
from psc.class_a_d2_parity_carrier import specimen
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
