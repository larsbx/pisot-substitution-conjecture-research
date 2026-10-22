"""Exact all-n ordered-child closure of the parity-indexed class-A d=2 carriers.

Parametrize n=4*l+r, r in 0..3. This resolves the half-integral
FIRST/RUN/LAST occurrence difference bounds without dropping index parity.
For each residue and all l>=3, integer-affine comparisons are stable, and
all possible child y' outside -4..4 have nonpositive overlap. Subtract all
matching destination intervals for the remaining y' and certify all 9,692
gap cases by exact nonnegative coefficient polynomials for the root interval
0<h<1/(n0+1). Every crossing/incomplete sign refuses.

The finite prefix n=4..11 is separately checked by existing exact
complete-graph tests. This proves all-n FORWARD CLOSURE and seed coverage
on the selected d=2 class-A line, *not* all-n boundary hitting.
Source: docs/class-a-d2-uniform-child-closure-2026-10-22.md.
"""
from psc.class_a_d2_parity_carrier import (
    inferred_template,exact_profile,certify_finite_parity,
)
from psc.class_a_d2_uniform_geometry import certify_rows


def _a(a: Int, b: Int) -> List[Int]:
    return [a,b]


def _add(x: List[Int], y: List[Int]) -> List[Int]:
    return [x[0]+y[0],x[1]+y[1]]


def _sub(x: List[Int], y: List[Int]) -> List[Int]:
    return [x[0]-y[0],x[1]-y[1]]


def _inc(x: List[Int], v: Int) -> List[Int]:
    return [x[0],x[1]+v]


def _le(x: List[Int], y: List[Int], l0: Int) raises -> Bool:
    var slope=y[0]-x[0]
    var at=l0*slope+y[1]-x[1]
    if slope>=0 and at>=0:
        return True
    if slope<=0 and at<0:
        return False
    raise Error("UNDECIDED d2 affine order on infinite residue ray")


def _min(x: List[Int], y: List[Int], l0: Int) raises -> List[Int]:
    return x.copy() if _le(x,y,l0) else y.copy()


def _max(x: List[Int], y: List[Int], l0: Int) raises -> List[Int]:
    return y.copy() if _le(x,y,l0) else x.copy()


def _floor_half(v: Int) -> Int:
    return v//2 if v>=0 else -((-v+1)//2)


def _ceil_half(v: Int) -> Int:
    return -_floor_half(-v)


def _ceil_aff_half(x: List[Int]) raises -> List[Int]:
    if x[0]%2!=0:
        raise Error("d2 parity slicing did not clear occurrence denominator")
    return [x[0]//2,_ceil_half(x[1])]


def _floor_aff_half(x: List[Int]) raises -> List[Int]:
    if x[0]%2!=0:
        raise Error("d2 parity slicing did not clear occurrence denominator")
    return [x[0]//2,_floor_half(x[1])]


def _phase(letter: Int, part: Int, residue: Int) raises -> List[Int]:
    """[prefix-y low slope,const, high slope,const, child, prefix-x,c]."""
    if letter<0 or letter>2 or part<0 or part>2 or residue<0 or residue>3:
        raise Error("invalid d2 occurrence phase")
    var run=_a(4,residue+(2 if letter==0 else 0 if letter==1 else 1))
    if part==0:
        return [0,0,0,0,1 if letter==1 else 0,0,0]
    var px=0 if letter==1 else 1
    var pc=1-px
    if part==1:
        return [0,0,run[0],run[1]-1,2,px,pc]
    return [run[0],run[1],run[0],run[1],1 if letter==2 else 0,px,pc]


def _tile(letter: Int) raises -> List[Int]:
    if letter==0:
        return [1,2,2,0]
    if letter==1:
        return [1,0,0,0]
    if letter==2:
        return [1,1,0,0]
    raise Error("invalid d2 child tile")


def _shift(s: Int, dx: Int, dc: Int, k: List[Int],
           child_y: Int, residue: Int) raises -> List[Int]:
    """At k=a*l+b, child T in the d2 Perron length scale.

    n=4*l+residue; 4*l*h*(1+h)
       =1-(residue+1)h-(residue+2)h^2-2h^3.
    """
    if len(k)!=2 or k[0]%2!=0:
        raise Error("d2 affine child offset has wrong parity")
    var half=k[0]//2
    var k0=k[1]+s+dx
    var cs=2*s+dx+dc+child_y
    return [cs+half,
            -(residue+1)*half+2*k0+child_y,
            -(residue+2)*half+2*k0,
            -2*half]


def _nonnegative(poly: List[Int], q: Int) raises -> Bool:
    if len(poly)!=4 or q<8:
        raise Error("malformed d2 strict-overlap sign certificate")
    var a=poly[0]
    var b=poly[1]
    var c=poly[2]
    var d=poly[3]
    var q2=q*q
    var q3=q2*q
    return q3*a>=0 and (3*q3*a+q2*b)>=0 and (
        3*q3*a+2*q2*b+q*c)>=0 and (q3*a+q2*b+q*c+d)>=0


def _gap_exclusion(
    top: Int,bottom: Int,s: Int,dx: Int,dc: Int,
    residue: Int,child_y: Int,klo: List[Int],khi: List[Int],q: Int,
) raises -> Int:
    var lo=_shift(s,dx,dc,klo,child_y,residue)
    var hi=_shift(s,dx,dc,khi,child_y,residue)
    var lt=_tile(top)
    var lb=_tile(bottom)
    var left=List[Int]()
    var right=List[Int]()
    for j in range(4):
        left.append(-hi[j]-lb[j])
        right.append(lo[j]-lt[j])
    if _nonnegative(left,q):
        return 1
    if _nonnegative(right,q):
        return 2
    raise Error("d2 actual strict child outside parity carrier: gap not excluded")


def _residue_rows(template: List[List[Int]], residue: Int) raises -> List[List[Int]]:
    var out=List[List[Int]]()
    for row in template:
        if len(row)!=8:
            raise Error("invalid d2 parity row")
        # m=floor(n/2)=2*l+floor(residue/2).
        var h=residue//2
        out.append([row[0],row[1],row[2],row[3],
                    2*row[4],row[4]*h+row[5],
                    2*row[6],row[6]*h+row[7]])
    return out^


def certify_residue(template: List[List[Int]], residue: Int) raises -> List[Int]:
    """Exact all-l>=3 closure for n=4*l+residue."""
    if residue<0 or residue>3:
        raise Error("only four integer residue rays")
    var parity=residue%2
    if len(template)!=(93 if parity==0 else 87):
        raise Error("incorrect d2 parity row count")
    var rows=_residue_rows(template,residue)
    var l0=3
    var q=4*l0+residue+1
    var cells=0
    var gaps=0
    var left=0
    var right=0
    var window=0
    for source in rows:
        var top=source[0]
        var bottom=source[1]
        var s=source[2]
        var y=source[3]
        if abs(s)>1:
            raise Error("d2 child y' window assumes coordinate sum bound")
        var boundlo=_a(source[4],source[5])
        var boundhi=_a(source[6],source[7])
        # The coincidence top==bottom,s=y=k=0 is terminal.
        var terminal=(top==bottom and s==0 and y==0)
        for part in range(2 if terminal else 1):
            var parentlo=boundlo.copy()
            var parenthi=boundhi.copy()
            if terminal:
                if part==0:
                    parenthi=_min(parenthi,_a(0,-1),l0)
                else:
                    parentlo=_max(parentlo,_a(0,1),l0)
            if not _le(parentlo,parenthi,l0):
                continue
            for tp in range(3):
                var a=_phase(top,tp,residue)
                for bp in range(3):
                    var b=_phase(bottom,bp,residue)
                    var ct=a[4]
                    var cb=b[4]
                    var dx=b[5]-a[5]
                    var dc=b[6]-a[6]
                    # y' monotone: outside [-4,4] lies at or beyond tile
                    # endpoints, established on the whole Perron root interval.
                    for endpoint in range(2):
                        var child_y=5 if endpoint==0 else -5
                        var k=parentlo.copy() if endpoint==0 else parenthi.copy()
                        var sh=_shift(s,dx,dc,k,child_y,residue)
                        var lt=_tile(ct)
                        var lb=_tile(cb)
                        var cert=List[Int]()
                        for z in range(4):
                            cert.append(sh[z]-lt[z] if endpoint==0 else -sh[z]-lb[z])
                        if not _nonnegative(cert,q):
                            raise Error("d2 finite child y' window is unproved")
                        window+=1
                    for yy in range(-4,5):
                        # y'=(4*l+r)s+2k+y+z_b-z_t; the y-prefix
                        # difference realizes EVERY integer in the
                        # interval [z_b^lo-z_t^hi,z_b^hi-z_t^lo].
                        var base=_a(-4*s,yy-residue*s-y)
                        var occ_lo=_ceil_aff_half(
                            _sub(base,_sub(_a(b[2],b[3]),_a(a[0],a[1]))))
                        var occ_hi=_floor_aff_half(
                            _sub(base,_sub(_a(b[0],b[1]),_a(a[2],a[3]))))
                        var lo=_max(parentlo,occ_lo,l0)
                        var hi=_min(parenthi,occ_hi,l0)
                        if not _le(lo,hi,l0):
                            continue
                        cells+=1
                        var child_s=2*s+dx+dc+yy
                        var cursor=lo.copy()
                        # Typed intervals are already ordered and pairwise
                        # disjoint for every parameter by the prerequisite
                        # PR #313 geometry certificate. A crossing refuses.
                        var preceding=False
                        var old_end=_a(0,0)
                        for target in rows:
                            if target[0]!=ct or target[1]!=cb or target[2]!=child_s or target[3]!=yy:
                                continue
                            var shift=s+dx
                            var d_lo=_a(target[4],target[5]-shift)
                            var d_hi=_a(target[6],target[7]-shift)
                            if preceding and not _le(_inc(old_end,1),d_lo,l0):
                                raise Error("d2 target interval reorders on residue ray")
                            preceding=True
                            old_end=d_hi.copy()
                            if not _le(cursor,hi,l0):
                                break
                            if _le(d_hi,_inc(cursor,-1),l0):
                                continue
                            if _le(_inc(hi,1),d_lo,l0):
                                break
                            var gapend=_min(hi,_inc(d_lo,-1),l0)
                            if _le(cursor,gapend,l0):
                                gaps+=1
                                var v=_gap_exclusion(ct,cb,s,dx,dc,residue,yy,cursor,gapend,q)
                                if v==1:
                                    left+=1
                                else:
                                    right+=1
                            cursor=_max(cursor,_inc(d_hi,1),l0)
                        if _le(cursor,hi,l0):
                            gaps+=1
                            var v=_gap_exclusion(ct,cb,s,dx,dc,residue,yy,cursor,hi,q)
                            if v==1:
                                left+=1
                            else:
                                right+=1
    var expected_cells=3005 if parity==0 else 2845
    var expected_gaps=2483 if parity==0 else 2363
    var expected_left=1249 if parity==0 else 1189
    var expected_right=1234 if parity==0 else 1174
    var expected_window=1710 if parity==0 else 1602
    if cells!=expected_cells or gaps!=expected_gaps or left!=expected_left or (
        right!=expected_right or window!=expected_window):
        raise Error("d2 symbolic closure partition counts changed")
    print("CLASS_A_D2_UNIFORM_RESIDUE", "r",residue,"n>= ",12+residue,
          "cells",cells,"gap_exclusions",gaps,"left",left,"right",right,
          "window",window,"uniform_forward_closed=true","hitting=false")
    return [cells,gaps,left,right,window]


def certify_d2_all_n_closure() raises -> List[Int]:
    var even=inferred_template(8,12)
    var odd=inferred_template(9,13)
    # The earlier theorem-facing component must pass before it can be
    # used to infer seed inclusion, real parent geometry, and disjointness.
    _=certify_rows(even,0)
    _=certify_rows(odd,1)
    for n in [4,5,6]:
        _=exact_profile(n)
    for n in [7,8,9,10,11]:
        if n%2==0:
            _=certify_finite_parity(n,even)
        else:
            _=certify_finite_parity(n,odd)
    var summary=List[Int]()
    for r in range(4):
        if r%2==0:
            var row=certify_residue(even,r)
            summary.append(row[1])
        else:
            var row=certify_residue(odd,r)
            summary.append(row[1])
    print("CLASS_A_D2_UNIFORM_FORWARD_CLOSURE",
          "n>=4", "all_reachable_children_covered=true",
          "uniform_hitting=false","candidate_equals_all_reachable=not_asserted")
    return summary^
