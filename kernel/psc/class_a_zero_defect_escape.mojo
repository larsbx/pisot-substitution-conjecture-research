"""Actual occurrence escapes for the strict minus-Class-A zero-defect slice.

Every accepted output is a literal composable path ending at full integral
offset zero. This constructor does not assert that arbitrary seed descendants
enter the slice. Nonzero out-of-slice sources and non-strict endpoint cases
refuse; no bounded search is used. The geometric reduction and occurrence
table are in docs/class-a-zero-defect-escape-2026-11-14.md; tests provide
finite replay. Executed integer arithmetic is checked: an oversized
intermediate refuses, while the written theorem uses arbitrary integers.
"""

from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, _run, member_transport
from psc.class_a_zero_return import _parameters, _delta, zero_return_addresses
from psc.class_a_x_ladder import reversed_label


def _zero(w: BoundaryLabel) -> Bool:
    return w.x == 0 and w.c == 0 and w.y == 0


def xx5_strict_domain(k: Int, t: Int) raises -> Bool:
    """Exact strict domain for (x,x,-1,0,5), with no numerical root test.

    The boundary polynomial has sign
    (2k+3t+13)(2t-2k-3)-25. Its positive integer domain simplifies to
    t-k>=3, or t-k=2 with k>=2; there is no integral equality case.
    """
    _ = _parameters(k, t)
    var difference = checked_sub(t, k)
    return difference >= 3 or (difference == 2 and k >= 2)


def _walk(k: Int, t: Int, source: BoundaryLabel,
          addresses: List[List[Int]]) raises -> List[BoundaryEdge]:
    var parameters = _parameters(k, t)
    var result = List[BoundaryEdge]()
    var w = source
    for address in addresses:
        if len(address) != 2:
            raise Error("an occurrence address must retain both literal indices")
        w = member_transport(-1, k, parameters[0], parameters[1],
                             w, address[0], address[1])
        result.append(BoundaryEdge(address[0], address[1], w))
    if not _zero(w):
        raise Error("selected occurrence path did not reach the integral zero offset")
    return result^


def endpoint_escape(k: Int, t: Int, top: Int, bottom: Int,
                    s: Int) raises -> List[BoundaryEdge]:
    """Escape from B_ef(s)=(e,f,-e_f+s e_y), retaining boundary letters.

    The strict cases are cx/xc with 1<=s<=3, cc with 1<=s<=2,
    and xx with 1<=s<=4, plus xx5 on xx5_strict_domain(k,t).
    The final child can have different top and bottom letters.
    """
    var parameters = _parameters(k, t)
    var n = parameters[0]
    var d = parameters[1]
    var a = checked_add(n, d)
    if top < 0 or top > 1 or bottom < 0 or bottom > 1 or s < 1:
        raise Error("outside the two endpoint tile types and positive endpoint offset")
    var addresses = List[List[Int]]()
    if top == 1 and bottom == 0:
        if s == 1:
            addresses = [[1, checked_add(d, 2)]]
        elif s == 2:
            addresses = [[checked_add(n, 1), checked_add(d, 1)],
                         [checked_add(d, 2), 0], [1, 2]]
        elif s == 3 and k >= 1:
            addresses = [[checked_add(k, 3), 0], [checked_add(t, 3), 0],
                         [1, checked_add(t, 5)], [3, 1]]
        elif s == 3:
            addresses = [[3, 0], [n, 0], [0, n],
                         [checked_add(n, 1), 0], [1, 4]]
        else:
            raise Error("uncovered cx endpoint offset")
    elif top == 0 and bottom == 1:
        if s == 1:
            addresses = [[0, 1], [2, 1]]
        elif s == 2:
            addresses = [[checked_add(n, 1), 1], [3, 1]]
        elif s == 3 and k >= 1:
            addresses = [[checked_add(checked_mul(2, n), 2), 0],
                         [checked_add(t, 3), 0], [0, checked_add(t, 4)], [4, 1]]
        elif s == 3:
            addresses = [[checked_add(checked_mul(2, n), 2), 0],
                         [n, 0], [0, n], [0, checked_sub(n, 1)],
                         [checked_add(n, 1), 0], [checked_add(t, 3), 1], [1, 3]]
        else:
            raise Error("uncovered xc endpoint offset")
    elif top == 1 and bottom == 1:
        if s == 1:
            addresses = [[1, 2]]
        elif s == 2:
            addresses = [[checked_add(n, 1), 0],
                         [checked_add(d, 1), checked_add(n, 1)],
                         [0, checked_add(d, 2)], [2, 1]]
        else:
            raise Error("uncovered cc endpoint offset")
    else:
        if s == 1:
            addresses = [[0, checked_add(d, 1)], [2, 1]]
        elif s == 2:
            addresses = [[1, checked_add(t, 3)], [3, 1]]
        elif s == 3:
            addresses = [[checked_add(k, 3), 0], [0, checked_sub(n, 2)], [1, 2]]
        elif s == 4:
            addresses.append([checked_add(a, 1), checked_add(checked_mul(2, t), 1)])
            if checked_add(k, t) >= 1:
                addresses.append([checked_add(checked_mul(2, t), 9), 1])
                if checked_add(k, t) >= 2:
                    addresses.append([1, 5])
                else:
                    addresses.append([0, 4])
                    addresses.append([checked_add(a, 1), 4])
            else:
                addresses.append([7, 0])
                addresses.append([1, 7])
                addresses.append([3, 1])
        elif s == 5:
            if not xx5_strict_domain(k, t):
                raise Error("xx5 is not a strict endpoint overlap at these parameters")
            var difference = checked_sub(t, k)
            if difference == 2:
                if k >= 3:
                    addresses = [[checked_add(a, 1), 0],
                                 [checked_add(checked_mul(4, k), 18), 0],
                                 [checked_sub(n, 2), 0], [2, 1]]
                else:
                    # The remaining strict D=2 case is exactly (k,t)=(2,4).
                    addresses = [[25, 0], [25, 0], [19, 0], [0, 2], [1, 4]]
            elif difference == 3:
                addresses = [[checked_add(a, 1), 0],
                             [checked_add(checked_mul(2, t), 10), 1], [1, 5]]
            elif difference == 4:
                addresses = [[checked_add(a, 1), 0], [7, 0],
                             [1, checked_add(checked_mul(2, t), 10)], [5, 1]]
            else:
                var first = checked_add(
                    checked_add(checked_mul(3, k), checked_mul(2, t)), 13)
                if k >= 1:
                    addresses = [[first, 0], [checked_add(difference, 3), 0],
                                 [1, checked_add(checked_mul(2, t), 10)], [5, 1]]
                else:
                    addresses = [[first, 0], [checked_add(difference, 3), 0],
                                 [1, checked_add(checked_mul(2, t), 9)],
                                 [n, 0], [1, 0], [n, 0], [0, n],
                                 [checked_add(n, 1), 0], [1, 4]]
        else:
            raise Error("uncovered xx endpoint offset")
    var source = BoundaryLabel(top, bottom,
        -1 if bottom == 0 else 0, -1 if bottom == 1 else 0, s)
    return _walk(k, t, source, addresses)


def zero_defect_escape(k: Int, t: Int,
                       source: BoundaryLabel) raises -> List[BoundaryEdge]:
    """Return a supplied-address zero path, or refuse an invalid source.

    Nonzero sources must satisfy p=delta and p+q+r=0. A legal one-step
    target is handled directly. Otherwise genuine reversal makes the gap
    positive, and the literal LAST/FIRST edge reduces to endpoint_escape.
    The written geometric theorem covers all strict sources in this slice.
    This function makes no assertion of seed-reachable entry into the slice.
    """
    var parameters = _parameters(k, t)
    var n = parameters[0]
    var d = parameters[1]
    var delta = _delta(source.top, source.bottom)
    if _zero(source):
        return List[BoundaryEdge]()
    if source.x != delta or checked_add(checked_add(source.x, source.c), source.y) != 0:
        raise Error("source is outside the affine zero-defect slice")
    var hits = zero_return_addresses(k, t, source)
    if hits.positive_count() > 0:
        return _walk(k, t, source, [[hits.lo, checked_sub(hits.lo, hits.gap)]])

    var flip = hits.gap < 0
    var w = reversed_label(source) if flip else source
    var positive_hits = zero_return_addresses(k, t, w)
    var run = _run(-1, n, d, w.top)
    if positive_hits.gap <= run:
        raise Error("empty one-step interval did not normalize to the positive endpoint tail")
    var i = checked_add(run, 1)
    var s = checked_sub(positive_hits.gap, run)
    var endpoint = member_transport(-1, k, n, d, w, i, 0)
    var expected = BoundaryLabel(endpoint.top, endpoint.bottom,
        -1 if endpoint.bottom == 0 else 0,
        -1 if endpoint.bottom == 1 else 0, s)
    if endpoint != expected:
        raise Error("LAST/FIRST reduction changed an endpoint Parikh coordinate")
    var result = List[BoundaryEdge]()
    result.append(BoundaryEdge(i, 0, endpoint))
    var tail = endpoint_escape(k, t, endpoint.top, endpoint.bottom, s)
    for edge in tail:
        result.append(edge)
    if flip:
        var reversed = List[BoundaryEdge]()
        for edge in result:
            reversed.append(BoundaryEdge(edge.j, edge.i, reversed_label(edge.target)))
        return reversed^
    return result^
