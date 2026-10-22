"""Uniform class-A typed carrier geometry and canonical seed inclusion.

For n>=4 the class-A Perron substitution has h=1/(beta-1) in (0,1/5)
satisfying P(n,h)=h^3+(n+1)(h+h^2)-1=0. Consequently
n*h*(1+h)=1-h-h^2-h^3. For a row (top,bottom,s,y,a,b,c,d)
and an endpoint k=A*n+B, the *scaled* physical shift is

 T = s+k*h*(1+h)+y*h
   = (s+A)+(-A+B+y)*h+(-A+B)*h^2-A*h^3.

The scaled tile lengths are x=(1+h+h^2), c=1, y=(1+h).
As T increases with k, every row is strictly interior exactly when
L_bottom+T(lower)>0 and L_top-T(upper)>0. These 178 inequalities are
certified UNIFORMLY by nonnegative degree-three Bernstein coefficients on
0<5*h<1, at least one coefficient strictly positive for each margin.

Nine canonical strict swap-patch seeds are checked by an all-n affine
interval membership rule; disjointness/nonemptiness of 89 intervals and
the formal 40*n+115 cardinality are checked symbolically as well.

This does NOT certify all-child forward closure, seed-reachability of
every template state, arbitrary-n hitting, or #139/#84/PSC.
"""
from psc.class_a_typed_carrier import template_rows


def _length_coeff(letter: Int) raises -> List[Int]:
    if letter==0:
        return [1,1,1,0]
    if letter==1:
        return [1,0,0,0]
    if letter==2:
        return [1,1,0,0]
    raise Error("invalid class-A letter type")


def _shift_endpoint(s: Int, y: Int, a: Int, b: Int) -> List[Int]:
    # Substitute n*h*(1+h)=(1-h-h^2-h^3).
    return [s+a,-a+b+y,-a+b,-a]


def _strict_positive_fifth(poly: List[Int]) raises:
    """Sufficient and exact certificate of strict positivity on 0<h<1/5.

    Set t=5h. The cubic 125*f(t/5) has integer monomial coefficients
    A0=125*c0,A1=25*c1,A2=5*c2,A3=c3. Its Bernstein degree-3
    coefficients multiplied by 3 are
    3*A0, 3*A0+A1, 3*A0+2*A1+A2, 3*(A0+A1+A2+A3).
    Every cubic Bernstein basis function is positive when 0<t<1.
    """
    if len(poly)!=4:
        raise Error("a cubic margin must have exactly four coefficients")
    var a0=125*poly[0]
    var a1=25*poly[1]
    var a2=5*poly[2]
    var a3=poly[3]
    var coeffs=List[Int]([
        3*a0,
        3*a0+a1,
        3*a0+2*a1+a2,
        3*(a0+a1+a2+a3),
    ])
    var has_positive=False
    for c in coeffs:
        if c<0:
            raise Error("unproved class-A geometry: negative Bernstein coefficient")
        if c>0:
            has_positive=True
    if not has_positive:
        raise Error("uniform geometry requires strict, not zero, margin")


def _check_strict_row(row: List[Int]) raises:
    if len(row)!=8:
        raise Error("malformed uniform class-A row")
    var top=row[0]
    var bottom=row[1]
    var s=row[2]
    var y=row[3]
    var lower=_shift_endpoint(s,y,row[4],row[5])
    var upper=_shift_endpoint(s,y,row[6],row[7])
    var lb=_length_coeff(bottom)
    var lt=_length_coeff(top)
    var lo_margin=List[Int]()
    var hi_margin=List[Int]()
    for j in range(4):
        lo_margin.append(lb[j]+lower[j])
        hi_margin.append(lt[j]-upper[j])
    _strict_positive_fifth(lo_margin)
    _strict_positive_fifth(hi_margin)


def _uniform_seed_in_rows(rows: List[List[Int]], seed: List[Int]) raises -> Bool:
    if len(seed)!=5:
        raise Error("invalid canonical swap seed")
    var top=seed[0]
    var bottom=seed[1]
    var k=seed[2]
    var c=seed[3]
    var y=seed[4]
    var s=k+c+y
    for row in rows:
        if len(row)!=8:
            raise Error("malformed candidate seed row")
        if row[0]==top and row[1]==bottom and row[2]==s and row[3]==y:
            # Lower endpoint nonincreasing, upper nondecreasing for n>=4.
            if row[4]<=0 and row[6]>=0:
                if 4*row[4]+row[5]<=k and k<=4*row[6]+row[7]:
                    return True
    return False


def canonical_seeds() -> List[List[Int]]:
    """All three unordered swap pairs, three strict positions each.

    Tile order is L_x>L_y>L_c throughout h>0. The seed shifts are 0,
    plus the shorter tile length on (long,long), and the difference
    e_b-e_a on the pair of second tiles. For (c,y), the same-type seed
    has shift -e_c instead, since y is longer than c.
    """
    return [
        [0,1,0,0,0],[1,0,-1,1,0],[0,0,0,1,0],
        [0,2,0,0,0],[2,0,-1,0,1],[0,0,0,0,1],
        [1,2,0,0,0],[2,1,0,-1,1],[2,2,0,-1,0],
    ]


def certify_uniform_components_rows(rows: List[List[Int]]) raises -> List[Int]:
    """Parametric integer/field certificate; NO finite substitution sweep."""
    if len(rows)!=89:
        raise Error("typed geometry requires exactly 89 affine intervals")
    var slope=0
    var constant=0
    for row in rows:
        if len(row)!=8:
            raise Error("malformed template interval")
        if row[0]<0 or row[0]>2 or row[1]<0 or row[1]>2:
            raise Error("invalid typed interval letters")
        # Nonempty for every n>=4.
        var ds=row[6]-row[4]
        var dc=row[7]-row[5]
        if ds<0 or 4*ds+dc<0:
            raise Error("affine interval not nonempty for all n>=4")
        slope+=ds
        constant+=dc+1
        _check_strict_row(row)
    if slope!=40 or constant!=115:
        raise Error("unexpected uniform candidate cardinality")
    # Require every two intervals of the same typed slice to remain
    # disjoint at n=4 and as n increases; either ordering is allowed.
    for i in range(len(rows)):
        var a=rows[i]
        for j in range(i+1,len(rows)):
            var b=rows[j]
            if a[0]!=b[0] or a[1]!=b[1] or a[2]!=b[2] or a[3]!=b[3]:
                continue
            var b_after_a=b[4]-a[6]
            var b_after_const=b[5]-a[7]
            var a_after_b=a[4]-b[6]
            var a_after_const=a[5]-b[7]
            if not (
                (b_after_a>=0 and 4*b_after_a+b_after_const>=1)
                or (a_after_b>=0 and 4*a_after_b+a_after_const>=1)
            ):
                raise Error("affine typed intervals overlap for some n>=4")
    var seeds=canonical_seeds()
    if len(seeds)!=9:
        raise Error("canonical seed count changed")
    for seed in seeds:
        if not _uniform_seed_in_rows(rows,seed):
            raise Error("canonical swap seed is not in the template uniformly")
    print("CLASS_A_UNIFORM_TYPED_COMPONENTS", "rows",89,"strict_margins",178,
          "canonical_seeds",9,"cardinality_slope",40,"constant",115,
          "all_n_ge_4=true","forward_closure=false","hitting=false")
    return [89,178,9,40,115]


def certify_uniform_components() raises -> List[Int]:
    return certify_uniform_components_rows(template_rows())
