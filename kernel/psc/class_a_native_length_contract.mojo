"""Exact native Perron length normalization for minus class-A Parikh overlaps.

The current native perron_tile_lengths_in chooses the first nonzero cross
product of rows of M^T-beta I, then orients it positively. For the class-A
matrix that candidate is nonzero and strictly positive. This contract
verifies the ACTUAL native SeedOverlapTables lengths, not just the cubic.
No assumption about the normalizations of other substitution families.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul, checked_neg
from psc.perron_field3 import (
    CubicElt, TileLengths3, cubic_add_checked, cubic_mul, cubic_mul_beta,
    sign_at_perron,
)
from psc.overlap_seed_patch import (
    SeedOverlapTables, OverlapState, selected_overlap_child, interior_overlap,
)
from psc.class_a_parikh_field_bridge import (
    check_minus_class_a_field, class_a_lengths, parikh_shift,
)

def expected_native_lengths(n: Int, d: Int) raises -> TileLengths3:
    if n < 3 or d < 5:
        raise Error("invalid class-A Perron native normalization parameters")
    var A=checked_add(n,d)
    return TileLengths3(
        CubicElt(checked_neg(A),A,0),
        CubicElt(checked_sub(d,n),n,0),
        CubicElt(2,-3,1))

def native_scale(n: Int, d: Int) raises -> CubicElt:
    # gamma=(beta-2)/beta = beta^2-(n+2)beta+(n-d).
    return CubicElt(checked_sub(n,d),checked_neg(checked_add(n,2)),1)

def check_literal_minus_class_a_words(tables: SeedOverlapTables,n: Int,d: Int) raises:
    var A=checked_add(n,d)
    if len(tables.sigma)!=3:
        raise Error("class-A normalization requires three actual words")
    if len(tables.sigma[0])!=checked_add(A,2) or (
        len(tables.sigma[1])!=checked_add(n,2)) or (
        len(tables.sigma[2])!=checked_add(n,1)):
        raise Error("substitution word lengths do not match minus class A")
    for i in range(len(tables.sigma[0])):
        var expected=0 if i==0 or i==A+1 else 2
        if tables.sigma[0][i]!=expected:
            raise Error("wrong ordered x substitution image")
    for i in range(len(tables.sigma[1])):
        var expected=1 if i==0 else 0 if i==n+1 else 2
        if tables.sigma[1][i]!=expected:
            raise Error("wrong ordered c substitution image")
    for i in range(len(tables.sigma[2])):
        var expected=0 if i==0 else 1 if i==n else 2
        if tables.sigma[2][i]!=expected:
            raise Error("wrong ordered y substitution image")

def verify_native_length_normalization(tables: SeedOverlapTables,n: Int,d: Int) raises -> CubicElt:
    """Verify native cofactor normalization, scalar ratio and positivity.

    The first two rows of M^T-beta I are (2-beta,0,A) and
    (1,1-beta,n), whose cross product is the expected vector.
    Native code is not trusted to keep this algorithm in the future:
    any difference is rejected by the exact equality check.
    """
    check_minus_class_a_field(tables.field,n,d)
    check_literal_minus_class_a_words(tables,n,d)
    var gamma=native_scale(n,d)
    if sign_at_perron(tables.field,gamma)<=0:
        raise Error("native/common normalization factor not positive")
    var reference=class_a_lengths(d)
    var native=expected_native_lengths(n,d)
    for i in range(3):
        if cubic_mul(tables.field,gamma,reference.at(i))!=native.at(i):
            raise Error("canonical/native scale coefficient identity failed")
        if tables.lengths.at(i)!=native.at(i):
            raise Error("actual native positive lengths do not match checked cofactor scale")
        if sign_at_perron(tables.field,tables.lengths.at(i))<=0:
            raise Error("native length is not strictly positive")
    return gamma

def native_parikh_shift(n: Int,d: Int,p: Int,q: Int,r: Int) raises -> CubicElt:
    """The EXACT native cross-product scale, no division or numeric beta."""
    var A=checked_add(n,d)
    var u=checked_add(checked_add(
        checked_neg(checked_mul(A,p)),checked_mul(checked_sub(d,n),q)),
        checked_mul(2,r))
    var v=checked_sub(checked_add(checked_mul(A,p),checked_mul(n,q)),
                      checked_mul(3,r))
    return CubicElt(u,v,r)

def decode_native_parikh_shift(n: Int,d: Int,shift: CubicElt) raises -> List[Int]:
    """Invert native lattice of absolute determinant d*(n+d)."""
    if n<3 or d<5:
        raise Error("invalid native length-lattice chamber")
    var A=checked_add(n,d)
    var total=checked_add(checked_add(shift.a0,shift.a1),shift.a2)
    if total % d != 0:
        raise Error("native cubic shift lies outside index-d first congruence")
    var q=total//d
    var pnumerator=checked_add(checked_sub(shift.a1,checked_mul(n,q)),
                               checked_mul(3,shift.a2))
    if pnumerator % A != 0:
        raise Error("native cubic shift lies outside index-A second congruence")
    var p=pnumerator//A
    var r=shift.a2
    if native_parikh_shift(n,d,p,q,r)!=shift:
        raise Error("native Parikh recovery does not round-trip")
    return [p,q,r]

def actual_prefix_parikh(tables: SeedOverlapTables,parent: Int,index: Int) raises -> List[Int]:
    if parent<0 or parent>=3 or index<0 or index>=len(tables.sigma[parent]):
        raise Error("nonexistent actual substitution occurrence")
    var counts=List[Int]([0,0,0])
    for i in range(index):
        var letter=tables.sigma[parent][i]
        if letter<0 or letter>=3:
            raise Error("invalid letter in literal prefix")
        counts[letter]=checked_add(counts[letter],1)
    return counts^

def verify_native_indexed_child(
    tables: SeedOverlapTables,n: Int,d: Int,
    top: Int,bottom: Int,p: Int,q: Int,r: Int,
    i: Int,j: Int,
) raises -> List[Int]:
    """Verify a full five-coordinate child against REAL native geometry.

    The full-Parikh coordinates are not recovered by guessing a global
    tile-length independence hypothesis: they are encoded in the exact
    native index-d*(n+d) sublattice, then checked against original word
    occurrences and strict cubic Perron overlap.
    """
    _=verify_native_length_normalization(tables,n,d)
    if top<0 or top>=3 or bottom<0 or bottom>=3:
        raise Error("not an actual ordered tile-type pair")
    var source=OverlapState(top,bottom,native_parikh_shift(n,d,p,q,r))
    if not interior_overlap(tables,source):
        raise Error("source does not overlap strictly in native field")
    var pt=actual_prefix_parikh(tables,top,i)
    var pb=actual_prefix_parikh(tables,bottom,j)
    var A=checked_add(n,d)
    var x=checked_add(checked_add(checked_mul(2,p),q),r)
    var c=checked_add(q,r)
    var y=checked_add(
        checked_add(checked_mul(A,p),checked_mul(n,q)),
        checked_mul(checked_sub(n,1),r))
    var xp=checked_sub(checked_add(x,pb[0]),pt[0])
    var cp=checked_sub(checked_add(c,pb[1]),pt[1])
    var yp=checked_sub(checked_add(y,pb[2]),pt[2])
    var child=selected_overlap_child(tables,source,i,j)
    if not interior_overlap(tables,child):
        raise Error("selected literal child is not a strict overlap")
    var target=OverlapState(tables.sigma[top][i],tables.sigma[bottom][j],
                            native_parikh_shift(n,d,xp,cp,yp))
    if child!=target:
        raise Error("native exact ordered child violates Parikh-field transport")
    var decoded=decode_native_parikh_shift(n,d,child.shift)
    if decoded[0]!=xp or decoded[1]!=cp or decoded[2]!=yp:
        raise Error("native cubic child decodes to wrong full Parikh")
    return [child.top,child.bottom,xp,cp,yp]
