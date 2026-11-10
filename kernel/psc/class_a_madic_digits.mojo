"""Canonical finite-place digit ladder for minus Class A (det M = -2).

For every integer v, produce unique bits b[0..m) and integer tail u such that
v = sum_(j<m) M^j (b[j],0,0) + M^m u.
This is an exact integral coset normal form, NOT a `Z/2^m` group
isomorphism and NOT a boundary-hitting theorem. In particular arbitrary
binary words need not be compatible with substitution prefix occurrences.

The class-A digit interface is a transparent specialization of the generic
finite-cokernel/Cramer construction, independently checked in regressions.
"""

from finite_exact.checked_int import checked_add, checked_sub, checked_mul


struct MAdicDigits(Copyable, Movable):
    var bits: List[Int]
    var tail: List[Int]

    def __init__(out self, bits: List[Int], tail: List[Int]):
        self.bits = bits.copy()
        self.tail = tail.copy()


def parameters(k: Int, t: Int) raises -> List[Int]:
    if k < 0 or t < 0:
        raise Error("outside minus Class-A integer chamber")
    var n = checked_add(checked_add(k, t), 3)
    var d = checked_add(checked_add(k, checked_mul(2,t)), 5)
    return [n, d]


def apply_incidence(k: Int, t: Int, v: List[Int]) raises -> List[Int]:
    if len(v) != 3:
        raise Error("full three-coordinate integral Parikh vector required")
    var p = parameters(k,t)
    var n = p[0]
    var a = checked_add(n,p[1])
    var x = checked_add(checked_add(checked_mul(2,v[0]),v[1]),v[2])
    var c = checked_add(v[1],v[2])
    var y = checked_add(checked_add(checked_mul(a,v[0]),
                                    checked_mul(n,v[1])),
                        checked_mul(checked_sub(n,1),v[2]))
    return [x,c,y]


def invert_image(k: Int,t: Int,v: List[Int]) raises -> List[Int]:
    """Integer M^{-1} v, refusing the exact index-two parity obstruction."""
    if len(v) != 3:
        raise Error("three coordinate image required")
    var p = parameters(k,t)
    var n = p[0]
    var a = checked_add(n,p[1])
    var diff = checked_sub(v[0],v[1])
    if diff % 2 != 0:
        raise Error("vector outside M Z^3: X-C is odd")
    var x = diff // 2
    var c = checked_sub(checked_sub(v[2],checked_mul(a,x)),
                        checked_mul(checked_sub(n,1),v[1]))
    var y = checked_sub(checked_add(checked_mul(a,x),
                                    checked_mul(n,v[1])),v[2])
    var result: List[Int] = [x,c,y]
    var check = apply_incidence(k,t,result)
    for i in range(3):
        if check[i] != v[i]:
            raise Error("inverse parity solution failed exact matrix replay")
    return result^


def extract_digits(k: Int, t: Int, v: List[Int], levels: Int) raises -> MAdicDigits:
    """Canonical coset digits and integral tail through a bounded exact level.

    The level bound is an executable resource contract; the theorem holds
    for every finite level. Abort rather than silently truncate.
    """
    if len(v) != 3 or levels < 0 or levels > 64:
        raise Error("invalid integral vector or digit-depth budget")
    _ = parameters(k,t)
    var bits = List[Int]()
    var current = v.copy()
    for _ in range(levels):
        var diff = checked_sub(current[0],current[1])
        var bit = 1 if diff % 2 != 0 else 0
        var adjusted: List[Int] = [
            checked_sub(current[0],bit), current[1], current[2],
        ]
        var next = invert_image(k,t,adjusted)
        bits.append(bit)
        current = next^
    return MAdicDigits(bits,current)


def reconstruct_digits(k: Int,t: Int, digits: MAdicDigits) raises -> List[Int]:
    if len(digits.tail) != 3 or len(digits.bits) > 64:
        raise Error("malformed integral M-adic digit record")
    _ = parameters(k,t)
    var out = digits.tail.copy()
    for backward in range(len(digits.bits)):
        var j = len(digits.bits)-1-backward
        var bit = digits.bits[j]
        if bit != 0 and bit != 1:
            raise Error("nonbinary finite-place digit")
        var shifted = apply_incidence(k,t,out)
        shifted[0] = checked_add(shifted[0],bit)
        out = shifted^
    return out^


def in_image_power(k: Int,t: Int,v: List[Int],levels: Int) raises -> Bool:
    """v in M^levels Z^3, not an approximate contracting-space test."""
    var record = extract_digits(k,t,v,levels)
    for b in record.bits:
        if b != 0:
            return False
    return True


def same_power_coset(k: Int,t: Int,a: List[Int],b: List[Int],
                     levels: Int) raises -> Bool:
    """Exact equality modulo M^levels Z^3; do not treat bits as a sum mod 2^m."""
    if len(a) != 3 or len(b) != 3:
        raise Error("full integral image vector required")
    var v: List[Int] = [
        checked_sub(a[0],b[0]),checked_sub(a[1],b[1]),
        checked_sub(a[2],b[2]),
    ]
    return in_image_power(k,t,v,levels)


def recover_zero_parent(k: Int,t: Int,prefix_top_minus_bottom: List[Int],
                        levels: Int) raises -> List[Int]:
    """The unique integral parent offset whose level-m literal child is zero.

    The caller must separately supply *actual* top/bottom substitution
    prefixes at level m. This tests only the finite-place lattice condition;
    neither a made-up prefix vector nor an arbitrary digit word is legal.
    For actual prefixes, strict geometry follows from the common positive-
    length level-m child, but seed-reachability and any uniform hitting claim
    remain separate.
    """
    var record = extract_digits(k,t,prefix_top_minus_bottom,levels)
    for bit in record.bits:
        if bit != 0:
            raise Error("prefix difference outside M^m Z^3")
    return record.tail.copy()
