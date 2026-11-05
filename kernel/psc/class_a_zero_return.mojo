"""Uniform one-step offset-zero predecessor geometry for minus Class A.

Exact integer arithmetic only. Unlike finite graph searches, this works for
all k,t >= 0 and returns the entire literal-address interval of one-step
offset-zero CHILDREN for an oriented full-Parikh parent.

A zero-offset child need not have equal tile letters. A nonempty legal
predecessor address has strict parent and child geometry by containment of
positive-length common child intervals in both inflated parent tiles; this
is separately checked in native tests. The result only characterizes one
inflation level: it does NOT show seed-reachable entry or universal BH.
"""

from finite_exact.checked_int import checked_add, checked_sub, checked_mul, checked_neg
from psc.class_a_boundary_children import BoundaryLabel, _run, member_transport


struct ZeroReturnAddresses(Copyable, Movable):
    """Positive index pairs (i,i-gap) for lo<=i<=hi, plus optional (0,0)."""
    var lo: Int
    var hi: Int
    var gap: Int
    var first_first: Bool

    def __init__(out self, lo: Int, hi: Int, gap: Int, first_first: Bool):
        self.lo = lo
        self.hi = hi
        self.gap = gap
        self.first_first = first_first

    def positive_count(self) -> Int:
        return self.hi - self.lo + 1 if self.lo <= self.hi else 0


def _parameters(k: Int, t: Int) raises -> List[Int]:
    if k < 0 or t < 0:
        raise Error("minus Class-A parameters k,t must be nonnegative")
    var n = checked_add(checked_add(k, t), 3)
    var d = checked_add(checked_add(k, checked_mul(2, t)), 5)
    return [n, d]


def _delta(top: Int, bottom: Int) raises -> Int:
    if top < 0 or top > 2 or bottom < 0 or bottom > 2:
        raise Error("Class-A parent tile type is not 0=x, 1=c or 2=y")
    # Initial letters are f(x)=x, f(c)=c and f(y)=x.
    return (0 if top == 1 else 1) - (0 if bottom == 1 else 1)


def zero_return_addresses(k: Int, t: Int, w: BoundaryLabel) raises -> ZeroReturnAddresses:
    """All exact integer (i,j) with child Parikh offset 0.

    A nonempty inverse interval has strict parent and child overlaps, by the
    common positive-length inflated child argument; this routine is the
    arithmetic filter, and does not certify positivity for unvalidated words.
    No assertion of seed-reachability or typed coincidence is made.
    """
    var par = _parameters(k, t)
    var n = par[0]
    var d = par[1]
    var delta = _delta(w.top, w.bottom)
    var first = w.x == 0 and w.c == 0 and w.y == 0
    if w.x != delta or checked_add(checked_add(w.x, w.c), w.y) != 0:
        return ZeroReturnAddresses(1, 0, 0, first)
    var gap = checked_add(w.c, checked_mul(checked_add(d, 1), delta))
    var lo = max(1, checked_add(1, gap))
    var hi = min(checked_add(_run(-1, n, d, w.top), 1),
                 checked_add(checked_add(_run(-1, n, d, w.bottom), 1), gap))
    return ZeroReturnAddresses(lo, hi, gap, first)


def one_step_zero_at(k: Int, t: Int, w: BoundaryLabel, i: Int, j: Int) raises -> Bool:
    """Is the actual child at ordered occurrence (i,j) of exact offset zero?"""
    var par = _parameters(k, t)
    var n = par[0]
    var d = par[1]
    _ = _delta(w.top, w.bottom)
    if i < 0 or j < 0 or i > checked_add(_run(-1, n, d, w.top), 1) or (
        j > checked_add(_run(-1, n, d, w.bottom), 1)
    ):
        raise Error("nonexistent top/bottom zero-based occurrence index")
    var hits = zero_return_addresses(k, t, w)
    if i == 0 or j == 0:
        return i == 0 and j == 0 and hits.first_first
    return hits.lo <= i and i <= hits.hi and j == checked_sub(i, hits.gap)


def zero_return_predecessor(k: Int, t: Int, top: Int, bottom: Int,
                            i: Int, j: Int) raises -> BoundaryLabel:
    """Unique integer parent Parikh vector for a legal same-kind start.

    When exactly one occurrence index is zero, the prefix difference is
    outside M Z^3 (the determinant-two image lattice), hence no integer
    predecessor exists: fail closed instead of manufacturing one.
    """
    var par = _parameters(k, t)
    var n = par[0]
    var d = par[1]
    var delta = _delta(top, bottom)
    if i < 0 or j < 0 or i > checked_add(_run(-1, n, d, top), 1) or (
        j > checked_add(_run(-1, n, d, bottom), 1)
    ):
        raise Error("nonexistent occurrence address")
    if (i == 0) != (j == 0):
        raise Error("mixed FIRST/non-FIRST parity forbids integer zero-return predecessor")
    if i == 0:
        return BoundaryLabel(top, bottom, 0, 0, 0)
    var difference = checked_sub(i, j)
    return BoundaryLabel(top, bottom, delta,
        checked_sub(difference, checked_mul(checked_add(d, 1), delta)),
        checked_add(checked_neg(difference), checked_mul(d, delta)))


def independently_check_zero_return(k: Int, t: Int, w: BoundaryLabel,
                                    i: Int, j: Int) raises -> Bool:
    """Check formula against canonical literal indexed Parikh child transport."""
    var par = _parameters(k, t)
    var child = member_transport(-1, k, par[0], par[1], w, i, j)
    var actual = child.x == 0 and child.c == 0 and child.y == 0
    if actual != one_step_zero_at(k, t, w, i, j):
        raise Error("one-step interval disagrees with actual full-Parikh transport")
    return actual


def enumerate_zero_predecessor_states(k: Int, t: Int) raises -> List[BoundaryLabel]:
    """All DISTINCT oriented strict overlap states with a literal zero child.

    This is a parameter-uniform description, not a forward reachable graph.
    There are exactly 18*n+6*d+7 states, including the nine zero-offset
    oriented parent pairs. A typed full-zero source is terminalized in
    the normal graph, even though its literal unterminalized children exist.
    """
    var par = _parameters(k, t)
    var n = par[0]
    var d = par[1]
    var result = List[BoundaryLabel]()
    for a in range(3):
        for b in range(3):
            var delta = _delta(a, b)
            # The FIRST/FIRST source is always zero, and is also the
            # positive-strip m=0 state precisely when delta=0.
            result.append(BoundaryLabel(a, b, 0, 0, 0))
            var rb = _run(-1, n, d, b)
            var ra = _run(-1, n, d, a)
            for m in range(checked_neg(rb), checked_add(ra, 1)):
                if delta == 0 and m == 0:
                    continue
                var q = checked_sub(m, checked_mul(checked_add(d, 1), delta))
                var r = checked_add(checked_neg(m), checked_mul(d, delta))
                result.append(BoundaryLabel(a, b, delta, q, r))
    var expected = checked_add(checked_add(checked_mul(18, n),
                                           checked_mul(6, d)), 7)
    if len(result) != expected:
        raise Error("one-step predecessor linear-strip cardinality mismatch")
    return result^
