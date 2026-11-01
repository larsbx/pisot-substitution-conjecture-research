"""Canonical selected-tail contracts for CY, CC and X first choices.

Twelve disjoint integer chambers k=0,1,2,>=3 and t=0,1,>=2.
Affine recipe rows are proposals. All coefficient identities and word
bounds are re-proved, and every path label's strict margins are certified
on the inherited open Perron polygon. No all-later-choice or PSC claim.
"""
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, geometric_state, verify_member_edge
from psc.class_a_boundary_u_children import reverse_label
from psc.class_a_boundary_r4_children import _transition
from psc.class_a_boundary_tx_children import certify_tx_children
from psc.class_a_boundary_occurrences import FIRST, RUN, LAST
from psc.param_poly import QX, qx_const, qx_affine2, qx_add, qx_sub, qx_mul, qx_is_zero
from psc.class_a_selected_recipe_tables import recipe_sources
from finite_linear_algebra.scalar import q_int
from psc.exact import q_sign
from finite_exact.checked_int import checked_add, checked_mul
from psc.overlap_seed_patch import SeedOverlapTables


def _letter_coeff(letter: Int) raises -> List[Int]:
    if letter==0:return [2,0,1]
    if letter==1:return [1,1,0]
    if letter==2:return [1,0,0]
    raise Error("not an actual letter")


def certify_selected_label(w: BoundaryLabel) raises:
    var shift=List[Int]([2*w.x+w.c+w.y,w.c,w.x])
    var top=_letter_coeff(w.top)
    var bottom=_letter_coeff(w.bottom)
    for side in range(2):
        var a=bottom[0]+shift[0] if side==0 else top[0]-shift[0]
        var b=bottom[1]+shift[1] if side==0 else top[1]-shift[1]
        var c=bottom[2]+shift[2] if side==0 else top[2]-shift[2]
        var positive=False
        for vertex in range(4):
            var h=q_int(0) if vertex<2 else q_int(1).div(q_int(5))
            var rho=q_int(0) if vertex==0 else (q_int(1) if vertex==1 else q_int(1 if vertex==2 else 3).div(q_int(5)))
            var value=q_int(a).add(q_int(b).mul(h)).add(q_int(c).mul(rho))
            if value.rejected:raise Error("rejected exact margin")
            if q_sign(value)<0:raise Error("selected label is not strict on inherited Perron polygon")
            positive=positive or q_sign(value)>0
        if not positive:raise Error("selected strict margin vanishes identically")


def _index(row: List[Int],start: Int,k: QX,t: QX) -> QX:
    return qx_add(qx_add(qx_const(row[start]),qx_mul(qx_const(row[start+1]),k)),qx_mul(qx_const(row[start+2]),t))


def _kind(letter: Int,index: QX,n: QX,d: QX) raises -> Int:
    if qx_is_zero(index):return FIRST
    var count=qx_add(n,d) if letter==0 else (n.copy() if letter==1 else qx_sub(n,qx_const(1)))
    if qx_is_zero(qx_sub(index,qx_add(count,qx_const(1)))):return LAST
    return RUN  # the existing exact prefix routine proves both RUN bounds


def certify_selected_recipes(rows: List[List[Int]],roots: Bool=True) raises -> Int:
    for row in rows:
        if len(row)!=15 or row[0]<0 or row[0]>=12 or row[1]<0 or row[1]>=3:
            raise Error("out-of-scope selected recipe row")
        if row[2]<0 or row[2]>=len(recipe_sources(row[1])) or row[3]<0 or row[3]>5:
            raise Error("unregistered selected source or ordinal")
    if roots:certify_tx_children() # inherits the exact beta and polygon bounds
    var edges=0
    for cell in range(12):
        var k0=cell//3
        var t0=cell%3
        var k=qx_affine2(k0,1 if k0==3 else 0,0)
        var t=qx_affine2(t0,0,1 if t0==2 else 0)
        var n=qx_add(qx_add(k,t),qx_const(3))
        var d=qx_add(qx_add(k,qx_mul(qx_const(2),t)),qx_const(5))
        for family in range(3):
            var sources=recipe_sources(family)
            for source_id in range(len(sources)):
                var state=sources[source_id]
                certify_selected_label(state)
                var step=0
                for row in rows:
                    if len(row)!=15:raise Error("malformed selected recipe row")
                    if row[0]!=cell or row[1]!=family or row[2]!=source_id:continue
                    if row[3]!=step:raise Error("missing or duplicate selected path step")
                    var i=_index(row,4,k,t)
                    var j=_index(row,7,k,t)
                    var target=BoundaryLabel(row[10],row[11],row[12],row[13],row[14])
                    var ti=_kind(state.top,i,n,d)
                    var bj=_kind(state.bottom,j,n,d)
                    _transition(n,d,state,ti,i,bj,j,target)
                    _transition(n,d,reverse_label(state),bj,j,ti,i,reverse_label(target))
                    certify_selected_label(target)
                    state=target
                    step+=1;edges+=2
                if step==0 or step>(6 if family==0 else (4 if family==1 else 5)):
                    raise Error("selected path length outside its scoped bound")
                if state!=BoundaryLabel(2,2,0,0,0):raise Error("path is not typed coincidence")
    if edges!=2*len(rows):raise Error("unverified selected recipe row")
    return edges


def selected_recipe_path(rows: List[List[Int]],family: Int,source_id: Int,k: Int,t: Int,flip: Int=0) raises -> List[BoundaryEdge]:
    if k<0 or t<0 or k>1000 or t>1000 or (flip!=0 and flip!=1):raise Error("selected member replay budget/sign")
    var sources=recipe_sources(family)
    if source_id<0 or source_id>=len(sources):raise Error("unknown selected source")
    var cell=min(k,3)*3+min(t,2)
    var out=List[BoundaryEdge]()
    for row in rows:
        if row[0]!=cell or row[1]!=family or row[2]!=source_id:continue
        if row[3]!=len(out):raise Error("missing path step")
        var i=checked_add(checked_add(row[4],checked_mul(row[5],k)),checked_mul(row[6],t))
        var j=checked_add(checked_add(row[7],checked_mul(row[8],k)),checked_mul(row[9],t))
        var target=BoundaryLabel(row[10],row[11],row[12],row[13],row[14])
        out.append(BoundaryEdge(j,i,reverse_label(target)) if flip==1 else BoundaryEdge(i,j,target))
    if len(out)==0:raise Error("empty path")
    return out^


def verify_selected_recipe_path(tables: SeedOverlapTables,rows: List[List[Int]],family: Int,source_id: Int,k: Int,t: Int,flip: Int=0) raises:
    var sources=recipe_sources(family)
    var state=reverse_label(sources[source_id]) if flip==1 else sources[source_id]
    var n=k+t+3
    var d=k+2*t+5
    for edge in selected_recipe_path(rows,family,source_id,k,t,flip):
        verify_member_edge(tables,-1,k,n,d,state,edge.i,edge.j,edge.target)
        state=edge.target
    if state!=BoundaryLabel(2,2,0,0,0):raise Error("noncoincident selected terminal")


def first_choice_source(family: Int) raises -> BoundaryLabel:
    if family==0:return BoundaryLabel(1,2,0,-2,2)
    if family==1:return BoundaryLabel(1,1,0,-2,3)
    if family==2:return BoundaryLabel(0,0,1,0,-1)
    raise Error("unknown first-choice source")


def first_choice_allowed(family: Int,k: Int,t: Int,i: Int,j: Int) raises -> Bool:
    if k<0 or t<0 or k>1000 or t>1000:raise Error("first-choice member budget")
    var n=k+t+3
    var d=k+2*t+5
    var A=n+d
    var topmax=n+1 if family<2 else A+1
    var bottommax=n if family==0 else topmax
    if i<0 or i>topmax or j<0 or j>bottommax:raise Error("nonexistent first-choice address")
    if family==0:
        if i==0:return j==0 or j==1
        if i==n+1 or j==0:return False
        if j<n:return j-i==0 or j-i==1
        return i==n-1 or i==n
    if family==1:return (i==n and j==0) or (i==n+1 and j>=0 and j<=2)
    if family==2:
        if i>=1 and i<=A:return (j==0 and i>=d and i<=d+3) or (j>=1 and j<=A and (i-j==d+2 or i-j==d+3))
        return i==A+1 and j>=n-2 and j<=n+1
    raise Error("unknown first-choice family")
