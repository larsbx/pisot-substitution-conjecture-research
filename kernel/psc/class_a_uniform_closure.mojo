"""Exact uniform all-child closure of the selected class-A 89-row carrier.

The proof enumerates only affine cells, not large substitutions. For n>=8
it proves 1006 integer-affine uncovered gaps exclude strict child geometry
using exact polynomial coefficients valid on 0<h<1/9. For 4<=n<=7
the existing complete exact finite carrier checker supplies the base cases.

No arbitrary-n hitting, carrier=reachable assertion, or universal #139
promotion follows. See docs/class-a-uniform-forward-closure-2026-10-22.md.
"""
from psc.class_a_typed_carrier import template_rows, certify_finite
from psc.class_a_uniform_geometry import certify_uniform_components


struct Affine(Copyable, Movable):
    var a: Int
    var b: Int

    def __init__(out self, a: Int, b: Int):
        self.a=a
        self.b=b


struct Segment(Copyable, Movable):
    var lo: Affine
    var hi: Affine

    def __init__(out self, lo: Affine, hi: Affine):
        self.lo=lo
        self.hi=hi


struct Phase(Copyable, Movable):
    var lo: Affine
    var hi: Affine
    var child: Int
    var x: Int

    def __init__(out self, lo: Affine, hi: Affine, child: Int, x: Int):
        self.lo=lo
        self.hi=hi
        self.child=child
        self.x=x


def _add(x: Affine, y: Affine) -> Affine:
    return Affine(x.a+y.a,x.b+y.b)


def _sub(x: Affine, y: Affine) -> Affine:
    return Affine(x.a-y.a,x.b-y.b)


def _inc(x: Affine, b: Int) -> Affine:
    return Affine(x.a,x.b+b)


def _le_tail(x: Affine, y: Affine) raises -> Bool:
    """Exact total line order on n>=8, or refusal if it changes."""
    var da=y.a-x.a
    var d8=8*da+y.b-x.b
    if da>=0 and d8>=0:
        return True
    if da<=0 and d8<0:
        return False
    raise Error("affine line order changes beyond n=8")


def _min_tail(x: Affine, y: Affine) raises -> Affine:
    return x if _le_tail(x,y) else y


def _max_tail(x: Affine, y: Affine) raises -> Affine:
    return y if _le_tail(x,y) else x


def _phase(parent: Int, part: Int) raises -> Phase:
    if parent<0 or parent>2 or part<0 or part>2:
        raise Error("invalid occurrence class")
    if part==0:
        return Phase(Affine(0,0),Affine(0,0),1 if parent==1 else 0,0)
    var m=Affine(1,0 if parent==1 else 1)
    if part==1:
        return Phase(Affine(0,1),m,2,0 if parent==1 else 1)
    return Phase(_inc(m,1),_inc(m,1),1 if parent==2 else 0,0 if parent==1 else 1)


def _tile(letter: Int) raises -> List[Int]:
    if letter==0:
        return [1,1,1,0]
    if letter==1:
        return [1,0,0,0]
    if letter==2:
        return [1,1,0,0]
    raise Error("bad child letter")


def _shift_coeff(
    q: Int,s: Int,k: Affine,top: Int,bottom: Int,tp: Int,bp: Int,
) -> List[Int]:
    # The exact root equation eliminates n from k*h*(1+h):
    # n*h*(1+h)=1-h-h*h-h*h*h.
    var du=(0 if bp==0 else (-1 if bottom==1 else 0))-(0 if tp==0 else (-1 if top==1 else 0))
    var dv=(0 if bp==0 else (0 if bottom==1 else 1))-(0 if tp==0 else (0 if top==1 else 1))
    return [q+k.a, q-k.a+k.b-s+du, k.b-k.a+s+dv, -k.a]


def _nonnegative_on_small_h(poly: List[Int]) raises -> Bool:
    """Certificate of p(h)>=0 for all 0<h<1/9.

    9^3*(1+t)^3*p(t/(9*(1+t))) has the following integer
    coefficients. Every term t^j is nonnegative for t>0.
    """
    if len(poly)!=4:
        raise Error("expected cubic sign polynomial")
    var a=poly[0]
    var b=poly[1]
    var c=poly[2]
    var d=poly[3]
    var v=List[Int]([
        729*a,
        2187*a+81*b,
        2187*a+162*b+9*c,
        729*a+81*b+9*c+d,
    ])
    for coefficient in v:
        if coefficient<0:
            return False
    return True


def _gap_excluded(
    q: Int,s: Int,klo: Affine,khi: Affine,
    child_top: Int,child_bottom: Int,
    top: Int,bottom: Int,tp: Int,bp: Int,
) raises -> Int:
    """Return 1 for left separation, 2 for right; refuse otherwise."""
    var lo_shift=_shift_coeff(q,s,klo,top,bottom,tp,bp)
    var hi_shift=_shift_coeff(q,s,khi,top,bottom,tp,bp)
    var lt=_tile(child_top)
    var lb=_tile(child_bottom)
    var negative_left=List[Int]()
    var negative_right=List[Int]()
    for i in range(4):
        negative_left.append(-lb[i]-hi_shift[i])
        negative_right.append(lo_shift[i]-lt[i])
    # Shift strictly increases with parent k: at the rightmost k,
    # left margin <=0 means no interior child in the whole interval.
    if _nonnegative_on_small_h(negative_left):
        return 1
    # If at the leftmost k the right margin <=0, likewise.
    if _nonnegative_on_small_h(negative_right):
        return 2
    raise Error("unexcluded actual child outside uniform typed carrier")


def certify_tail_rows(rows: List[List[Int]]) raises -> List[Int]:
    """All n>=8: 1528 nonempty symbolic case cells, 1006 excluded gaps."""
    if len(rows)!=89:
        raise Error("uniform transfer requires exactly 89 canonical rows")
    var cells=0
    var gaps=0
    var left=0
    var right=0
    for source in rows:
        if len(source)!=8:
            raise Error("malformed source interval")
        var top=source[0]
        var bottom=source[1]
        var s=source[2]
        var y=source[3]
        # Required for the proof that a positive-interior child has
        # coordinate sum q in {-2,-1,0,1,2}; enforce for every row.
        if abs(s)>1:
            raise Error("child-sum bound requires |s|<=1")
        if source[4]<-1 or 4*(source[4]+1)+source[5]<-1:
            raise Error("child-sum bound requires k>=-n-1")
        if source[6]>1 or 4*(1-source[6])+1-source[7]<0:
            raise Error("child-sum bound requires k<=n+1")
        var parent_segments=List[Segment]()
        var full=Segment(Affine(source[4],source[5]),Affine(source[6],source[7]))
        if top==bottom and s==0 and y==0:
            # Zero-offset equal-letter states are terminal in the canonical
            # seed graph. Inflate no children of such a state.
            parent_segments.append(Segment(full.lo,_min_tail(full.hi,Affine(0,-1))))
            parent_segments.append(Segment(_max_tail(full.lo,Affine(0,1)),full.hi))
        else:
            parent_segments.append(full)
        for parent in parent_segments:
            if not _le_tail(parent.lo,parent.hi):
                continue
            for tp in range(3):
                var a=_phase(top,tp)
                for bp in range(3):
                    var b=_phase(bottom,bp)
                    var deltax=b.x-a.x
                    var di=(0 if bp==0 else 1)-(0 if tp==0 else 1)
                    for q in range(-2,3):
                        var qy=q-2*s-di
                        # Every possible index difference j-i in the two
                        # first/run/last classes is between jlo-ihi and
                        # jhi-ilo. This yields the complete integer k window.
                        var base=Affine(-s,q-2*s-y)
                        var occur_lo=_add(base,_sub(a.lo,b.hi))
                        var occur_hi=_add(base,_sub(a.hi,b.lo))
                        var lo=_max_tail(parent.lo,occur_lo)
                        var hi=_min_tail(parent.hi,occur_hi)
                        if not _le_tail(lo,hi):
                            continue
                        cells+=1
                        var cursor=lo
                        # template_rows is ordered by typed slice and then
                        # by affine lower k, uniformly for n>=8.
                        var have_previous=False
                        var prev=Affine(0,0)
                        for target in rows:
                            if target[0]!=a.child or target[1]!=b.child or target[2]!=q or target[3]!=qy:
                                continue
                            var lower=_inc(Affine(target[4],target[5]),-s-deltax)
                            var upper=_inc(Affine(target[6],target[7]),-s-deltax)
                            if have_previous and not _le_tail(_inc(prev,1),lower):
                                raise Error("typed target intervals reordered or overlap")
                            have_previous=True
                            prev=upper
                            if not _le_tail(cursor,hi):
                                break
                            if _le_tail(upper,_inc(cursor,-1)):
                                continue
                            if _le_tail(_inc(hi,1),lower):
                                break
                            var gapend=_min_tail(hi,_inc(lower,-1))
                            if _le_tail(cursor,gapend):
                                gaps+=1
                                var verdict=_gap_excluded(q,s,cursor,gapend,a.child,b.child,top,bottom,tp,bp)
                                if verdict==1:
                                    left+=1
                                else:
                                    right+=1
                            cursor=_max_tail(cursor,_inc(upper,1))
                        if _le_tail(cursor,hi):
                            gaps+=1
                            var verdict=_gap_excluded(q,s,cursor,hi,a.child,b.child,top,bottom,tp,bp)
                            if verdict==1:
                                left+=1
                            else:
                                right+=1
    if cells!=1528 or gaps!=1006 or left!=505 or right!=501:
        raise Error("uniform typed carrier transfer partition count changed")
    print("CLASS_A_UNIFORM_FORWARD_TAIL", "n>=8", "cases",cells,
          "geometry_excluded_gaps",gaps,"left",left,"right",right,
          "all_child_closed=true","hitting=false")
    return [cells,gaps,left,right]


def certify_uniform_forward_closure() raises -> List[Int]:
    var rows=template_rows()
    # The exact previous component proof is an executable prerequisite:
    # strict geometry, all nine seeds, and the 40*n+115 cardinality.
    var components=certify_uniform_components()
    if components!=List[Int]([89,178,9,40,115]):
        raise Error("uniform geometry and seed prerequisite failed")
    # The accepted component proof establishes strict geometry and all seeds;
    # these four small parameters close the complete finite prefix exactly.
    for n in [4,5,6,7]:
        var record=certify_finite(n)
        if record[0]!=40*n+115 or record[1]!=record[0]:
            raise Error("finite base failed complete typed-carrier check")
    var tail=certify_tail_rows(rows)
    print("CLASS_A_UNIFORM_FORWARD_CLOSURE", "all_n_ge_4=true",
          "finite_base=4..7","strict_geometry_depends_on=class_a_uniform_geometry",
          "all_seed_depends_on=class_a_uniform_geometry","all_state_hitting=false")
    return tail
