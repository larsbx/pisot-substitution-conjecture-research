"""Actual level-m prefix-pair carry test over the Class-A nonunit lattice.

Consumes a pair of genuine zero-based Dumont-Thomas occurrence paths,
ROOT-TO-LEAF (most significant level first). Each prefix digit is computed
from the actual Class-A substitution word rather than supplied as an
untrusted algebraic vector.

For D=prefix_top-prefix_bottom at level m, write D=sum_(j<m) M^j d_j,
where d_0 is the *deepest* digit correction. The exact carry recurrence is
c_0=0 and c_(j+1)=M^-1(c_j+d_j) whenever this inverse is integral.
All m steps succeed iff D lies in M^m Z^3, and the final carry is the
unique level-m zero-offset parent. Failure at any parity gate is a genuine
nonmembership result for the GIVEN actual pair, not a nonproductivity proof.

This supplies no graph reachability, no uniform entry from X, and no BH.
"""
from finite_exact.checked_int import checked_add, checked_sub
from psc.class_a_boundary_children import _prefix, _letter
from psc.class_a_madic_digits import parameters, invert_image


struct PrefixCarryCertificate(Copyable, Movable):
    var valid: Bool
    var first_failure: Int
    var parent: List[Int]
    var depth: Int

    def __init__(out self, valid: Bool, first_failure: Int,
                 parent: List[Int], depth: Int):
        self.valid=valid
        self.first_failure=first_failure
        self.parent=parent.copy()
        self.depth=depth


def actual_prefix_corrections(
    k: Int, t: Int, top: Int, bottom: Int,
    top_path: List[Int], bottom_path: List[Int],
) raises -> List[List[Int]]:
    """Return differences of real proper-prefix vectors, deepest first.

    No arbitrary digit arrays accepted; each successive parent letter is
    the literal letter at the preceding occurrence.
    """
    var par=parameters(k,t)
    var n=par[0]
    var d=par[1]
    if top<0 or top>=3 or bottom<0 or bottom>=3:
        raise Error("invalid oriented root letters")
    var depth=len(top_path)
    if depth<1 or depth>32 or len(bottom_path)!=depth:
        raise Error("unequal paths or unsupported address depth")
    var corrections=List[List[Int]]()
    var a=top
    var b=bottom
    for h in range(depth):
        var i=top_path[h]
        var j=bottom_path[h]
        # Both helpers independently check the actual zero-based bounds.
        var pa=_prefix(-1,n,d,a,i)
        var pb=_prefix(-1,n,d,b,j)
        var diff: List[Int] = [
            checked_sub(pa[0],pb[0]),
            checked_sub(pa[1],pb[1]),
            checked_sub(pa[2],pb[2]),
        ]
        corrections.append(diff)
        a=_letter(-1,n,d,a,i)
        b=_letter(-1,n,d,b,j)
    var low_first=List[List[Int]]()
    for back in range(depth):
        low_first.append(corrections[depth-1-back])
    return low_first^


def exact_prefix_pair_carry(
    k: Int, t: Int, top: Int, bottom: Int,
    top_path: List[Int], bottom_path: List[Int],
) raises -> PrefixCarryCertificate:
    var digits=actual_prefix_corrections(k,t,top,bottom,top_path,bottom_path)
    var carry: List[Int] = [0,0,0]
    for level in range(len(digits)):
        var v=digits[level]
        var next: List[Int] = [
            checked_add(carry[0],v[0]),
            checked_add(carry[1],v[1]),
            checked_add(carry[2],v[2]),
        ]
        if checked_sub(next[0],next[1]) % 2 != 0:
            return PrefixCarryCertificate(False,level,[0,0,0],len(digits))
        carry=invert_image(k,t,next)
    return PrefixCarryCertificate(True,-1,carry,len(digits))


def unique_actual_zero_parent(
    k: Int, t: Int, top: Int, bottom: Int,
    top_path: List[Int], bottom_path: List[Int],
) raises -> List[Int]:
    var cert=exact_prefix_pair_carry(k,t,top,bottom,top_path,bottom_path)
    if not cert.valid:
        raise Error("actual prefix pair fails finite-place zero-parent carry")
    return cert.parent.copy()
