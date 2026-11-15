"""Exact interval images give finite integer carriers, with checked keying.

The caller authenticates the chart and reachability invariant.  This module
only encloses a supplied inverse-chart image of three certified intervals.
It does not assert that an arbitrary off-strip overlap is empty.
"""

from finite_exact.checked_int import checked_add, checked_mul, checked_neg, checked_sub
from finite_exact.closed_interval import IQ
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from psc.exact import require_iq, require_q


struct CarrierBox(Copyable, Movable):
    var lower: List[Int]
    var upper: List[Int]
    var capacity: Int

    def __init__(out self, lower: List[Int], upper: List[Int], capacity: Int):
        self.lower = lower.copy()
        self.upper = upper.copy()
        self.capacity = capacity


def bounded_floor(value: Q, limit: Int = 1024) raises -> Int:
    _ = require_q(value, "carrier integer rounding")
    if limit < 1 or limit > 1000000:
        raise Error("unsupported carrier rounding budget")
    if not q_int(-limit).le(value) or not value.le(q_int(limit)):
        raise Error("carrier rounding budget exhausted; inconclusive")
    var lo = -limit
    var hi = limit
    while lo < hi:
        var mid = lo + (hi - lo + 1) // 2
        if q_int(mid).le(value):
            lo = mid
        else:
            hi = mid - 1
    return lo


def bounded_ceil(value: Q, limit: Int = 1024) raises -> Int:
    var floor = bounded_floor(value, limit)
    if q_int(floor).eq(value):
        return floor
    return checked_add(floor, 1)


def checked_carrier(lower: List[Int], upper: List[Int]) raises -> CarrierBox:
    if len(lower) != 3 or len(upper) != 3:
        raise Error("carrier must have three coordinate intervals")
    var capacity = 1
    for i in range(3):
        if lower[i] < -1000000 or upper[i] > 1000000 or lower[i] > upper[i]:
            raise Error("invalid bounded carrier interval")
        var width = checked_add(checked_sub(upper[i], lower[i]), 1)
        capacity = checked_mul(capacity, width)
    return CarrierBox(lower, upper, capacity)


def validate_carrier(box: CarrierBox) raises:
    var expected = checked_carrier(box.lower, box.upper)
    if box.capacity != expected.capacity:
        raise Error("carrier capacity is not its exact integer box count")


def enclose_inverse_chart(inverse_phi: List[IQ], axes: List[IQ], limit: Int = 1024) raises -> CarrierBox:
    if len(inverse_phi) != 9 or len(axes) != 3:
        raise Error("inverse chart requires nine entries and three axes")
    for value in inverse_phi:
        _ = require_iq(value, "inverse chart entry")
    for value in axes:
        _ = require_iq(value, "chart axis interval")
    var lower = List[Int]()
    var upper = List[Int]()
    for row in range(3):
        var bound = IQ.singleton(Q.zero())
        for column in range(3):
            bound = require_iq(bound.add(inverse_phi[3 * row + column].mul(axes[column])), "inverse chart row")
        # Coordinates are integers.  Inclusive rational endpoints require
        # ceil(lower), floor(upper); equality is retained at either endpoint.
        lower.append(bounded_ceil(bound.lo, limit))
        upper.append(bounded_floor(bound.hi, limit))
    return checked_carrier(lower, upper)


def hull_carriers(boxes: List[CarrierBox]) raises -> CarrierBox:
    if len(boxes) < 1 or len(boxes) > 9:
        raise Error("carrier hull requires one through nine boxes")
    validate_carrier(boxes[0])
    var lower = boxes[0].lower.copy()
    var upper = boxes[0].upper.copy()
    for index in range(1, len(boxes)):
        validate_carrier(boxes[index])
        for coordinate in range(3):
            if boxes[index].lower[coordinate] < lower[coordinate]:
                lower[coordinate] = boxes[index].lower[coordinate]
            if boxes[index].upper[coordinate] > upper[coordinate]:
                upper[coordinate] = boxes[index].upper[coordinate]
    return checked_carrier(lower, upper)


def contains_offset(box: CarrierBox, offset: List[Int]) raises -> Bool:
    validate_carrier(box)
    if len(offset) != 3:
        raise Error("offset must have three coordinates")
    for i in range(3):
        if offset[i] < box.lower[i] or offset[i] > box.upper[i]:
            return False
    return True


def offset_key(box: CarrierBox, offset: List[Int]) raises -> Int:
    if not contains_offset(box, offset):
        raise Error("offset outside its proved integer carrier")
    var key = 0
    for coordinate in range(3):
        var width = checked_add(checked_sub(box.upper[coordinate], box.lower[coordinate]), 1)
        key = checked_add(checked_mul(key, width), checked_sub(offset[coordinate], box.lower[coordinate]))
    if key < 0 or key >= box.capacity:
        raise Error("impossible carrier key")
    return key


def canonical_pair_index(first: Int, second: Int) raises -> Int:
    if first < 0 or first > second or second > 2:
        raise Error("pair must be canonical on the three-letter alphabet")
    if first == 0:
        return second
    if first == 1:
        return second + 2
    return 5


def canonical_pair(first: Int, second: Int, x: Int, y: Int, z: Int) raises -> List[Int]:
    if first < 0 or first > 2 or second < 0 or second > 2:
        raise Error("overlap normalization requires three-letter labels")
    var positive = x > 0 or (x == 0 and y > 0) or (x == 0 and y == 0 and z > 0)
    if first > second or (first == second and positive):
        return [second,first,checked_neg(x),checked_neg(y),checked_neg(z)]
    return [first,second,x,y,z]


def typed_offset_key(global_box: CarrierBox, first: Int, second: Int, offset: List[Int]) raises -> Int:
    var pair = canonical_pair_index(first, second)
    return checked_add(checked_mul(pair, global_box.capacity), offset_key(global_box, offset))
