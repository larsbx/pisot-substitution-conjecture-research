"""Uniform geometry/seeds for parity-indexed *candidate* class-A d=2 carriers.

The even 93-row and odd 87-row templates are inferred from complete exact
finite graphs (psc.class_a_d2_parity_carrier). Here, INDEPENDENT OF ANY
FURTHER FINITE n SWEEP, integer polynomial inequalities prove for all
even n>=8 / all odd n>=7:
 - each candidate interval is nonempty and strict real overlap geometry;
 - all intervals in each typed slice are disjoint;
 - every one of the nine strict canonical swap seeds is included;
 - cardinality equals 40m+105 / 40m+111 for m=floor(n/2).
This is NOT all-child closure, all-state reachability, hitting, or PSC.
"""
from psc.class_a_d2_parity_carrier import inferred_template


def _endpoint(s: Int, y: Int, a: Int, b: Int, residue: Int) -> List[Int]:
    """At k=a*m+b, n=2*m+residue, T(h)=s+2k h(1+h)+y h.

    P_2(n,h)=1-(n+1)h-(n+2)h^2-2h^3=0, so
    2*m h(1+h)=1-(1+residue)h-(2+residue)h^2-2h^3.
    """
    return [s+a, -a*(1+residue)+2*b+y,
            -a*(2+residue)+2*b, -2*a]


def _tile(letter: Int) raises -> List[Int]:
    # At d=2, epsilon=+1: (Lx,Lc,Ly)=(1+2h+2h^2,1,1+h).
    if letter==0:
        return [1,2,2,0]
    if letter==1:
        return [1,0,0,0]
    if letter==2:
        return [1,1,0,0]
    raise Error("d2 carrier contains invalid tile letter")


def _strict_on_root_interval(poly: List[Int], q: Int) raises:
    """Exact sufficient all-h certificate for 0<h<1/q.

    Substitute h=t/(q*(1+t)), multiply by q^3*(1+t)^3.
    All four integer coefficients >=0 and one >0 imply strict positivity
    for every t>0; zero boundary contacts are *not* accepted.
    """
    if len(poly)!=4 or (q!=8 and q!=9):
        raise Error("invalid cubic or unproved root bound")
    var a=poly[0]
    var b=poly[1]
    var c=poly[2]
    var d=poly[3]
    var q2=q*q
    var q3=q2*q
    var co=List[Int]([
        q3*a,
        3*q3*a+q2*b,
        3*q3*a+2*q2*b+q*c,
        q3*a+q2*b+q*c+d,
    ])
    var strictly=False
    for v in co:
        if v<0:
            raise Error("uniform strict d2 Perron margin not certified")
        if v>0:
            strictly=True
    if not strictly:
        raise Error("d2 geometry only touches boundary, not strict")


def _gap_for_all_m(left_a: Int, left_b: Int, right_a: Int,
                   right_b: Int, m0: Int, distance: Int) -> Bool:
    """Left endpoint exceeds right endpoint + distance for all m>=m0."""
    var da=left_a-right_a
    var at_m0=da*m0+left_b-right_b
    return da>=0 and at_m0>=distance


def canonical_seeds() -> List[List[Int]]:
    # Strict swap patch seeds when Lx>Ly>Lc, valid for d=2 plus and n>=4.
    return [
        [0,1,0,0,0], [1,0,-1,1,0], [0,0,0,1,0],
        [0,2,0,0,0], [2,0,-1,0,1], [0,0,0,0,1],
        [1,2,0,0,0], [2,1,0,-1,1], [2,2,0,-1,0],
    ]


def _contains_uniform_seed(rows: List[List[Int]], m0: Int,
                            seed: List[Int]) raises -> Bool:
    if len(seed)!=5:
        raise Error("invalid d2 seed label")
    var s=seed[2]+seed[3]+seed[4]
    for row in rows:
        if len(row)!=8:
            raise Error("malformed d2 interval row")
        if row[0]==seed[0] and row[1]==seed[1] and row[2]==s and row[3]==seed[4]:
            if row[4]<=0 and row[6]>=0:
                if row[4]*m0+row[5]<=seed[2] and seed[2]<=row[6]*m0+row[7]:
                    return True
    return False


def certify_rows(rows: List[List[Int]], parity: Int) raises -> List[Int]:
    if parity!=0 and parity!=1:
        raise Error("d2 uniform geometry requires an even/odd residue")
    var n0=8 if parity==0 else 7
    var m0=n0//2
    var q=n0+1
    var expected_rows=93 if parity==0 else 87
    var expected_slices=82 if parity==0 else 80
    var expected_constant=105 if parity==0 else 111
    if len(rows)!=expected_rows:
        raise Error("d2 parity row-count changed")
    var slopes=0
    var constants=0
    var slices=0
    for i in range(len(rows)):
        var row=rows[i]
        if len(row)!=8:
            raise Error("malformed d2 parity interval")
        var top=row[0]
        var bottom=row[1]
        if top<0 or top>2 or bottom<0 or bottom>2:
            raise Error("d2 tile type out of range")
        # All m>=m0: upper-minus-lower is affine, nonnegative.
        if not _gap_for_all_m(row[6],row[7],row[4],row[5],m0,0):
            raise Error("d2 interval empty at some parameter")
        slopes+=row[6]-row[4]
        constants+=row[7]-row[5]+1
        var new_slice=True
        for j in range(i):
            var earlier=rows[j]
            if earlier[0]!=top or earlier[1]!=bottom or earlier[2]!=row[2] or earlier[3]!=row[3]:
                continue
            new_slice=False
            # If neither interval sits wholly to one side for every m,
            # the inferred template is not an all-n disjoint carrier.
            var after_earlier=_gap_for_all_m(row[4],row[5],earlier[6],earlier[7],m0,1)
            var before_earlier=_gap_for_all_m(earlier[4],earlier[5],row[6],row[7],m0,1)
            if not after_earlier and not before_earlier:
                raise Error("d2 typed intervals overlap or reorder for some m")
        if new_slice:
            slices+=1
        var lo=_endpoint(row[2],row[3],row[4],row[5],parity)
        var hi=_endpoint(row[2],row[3],row[6],row[7],parity)
        var lb=_tile(bottom)
        var lt=_tile(top)
        var left=List[Int]()
        var right=List[Int]()
        for k in range(4):
            left.append(lo[k]+lb[k])
            right.append(lt[k]-hi[k])
        _strict_on_root_interval(left,q)
        _strict_on_root_interval(right,q)
    if slopes!=40 or constants!=expected_constant or slices!=expected_slices:
        raise Error("d2 all-n candidate cardinality/slice count changed")
    var seeds=canonical_seeds()
    if len(seeds)!=9:
        raise Error("d2 canonical seed count changed")
    for seed in seeds:
        if not _contains_uniform_seed(rows,m0,seed):
            raise Error("canonical d2 swap seed omitted at some parameter")
    print("CLASS_A_D2_UNIFORM_GEOMETRY", "parity",parity,"n_floor",n0,
          "rows",expected_rows,"margins",2*expected_rows,"typed_slices",slices,
          "seeds",len(seeds),"size_slope",slopes,"size_constant",constants,
          "all_parameter_geometry=true","all_child_closed=false","hitting=false")
    return [expected_rows,2*expected_rows,slices,len(seeds),slopes,constants]


def certify_uniform_d2_geometry() raises:
    var even=inferred_template(8,12)
    var odd=inferred_template(9,13)
    var e=certify_rows(even,0)
    var o=certify_rows(odd,1)
    if e!=List[Int]([93,186,82,9,40,105]):
        raise Error("unexpected d2 even geometry certificate")
    if o!=List[Int]([87,174,80,9,40,111]):
        raise Error("unexpected d2 odd geometry certificate")
    print("CLASS_A_D2_UNIFORM_CANDIDATE_GEOMETRY", "even_n>=8", "odd_n>=7",
          "all_n_closure=not_proved","all_n_boundary_hitting=not_proved")
