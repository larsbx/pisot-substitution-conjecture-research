"""Exact order-sensitive affine ancestry traces for the open G1b-2 gate.

For a relative renewal address let q_t be the difference between the Parikh
vectors of the proper prefixes preceding the selected top and bottom children
at ancestry level t. The exact recurrence x_(t+1) = M x_t + q_t starts at the
source defect and ends at zero. This is finite diagnostic machinery, not a
proof that the trace has finitely many states uniformly over all returns.
"""

from psc.renewal import Diff3
from psc.renewal_address import RelativeRenewalAddress


struct AffineAncestryTrace(Copyable, Movable):
    var top_letters: List[Int]
    var bottom_letters: List[Int]
    var defects: List[Int]

    def __init__(out self, top_letters: List[Int], bottom_letters: List[Int], defects: List[Int]):
        self.top_letters = top_letters.copy()
        self.bottom_letters = bottom_letters.copy()
        self.defects = defects.copy()

    def state_count(self) -> Int:
        return len(self.top_letters)

    def depth(self) -> Int:
        return self.state_count() - 1

    def defect_at(self, level: Int) raises -> Diff3:
        if level < 0 or level >= self.state_count():
            raise Error("affine-trace level is out of range")
        var k = 3 * level
        return Diff3(self.defects[k], self.defects[k + 1], self.defects[k + 2])

    def closes(self) raises -> Bool:
        return self.defect_at(self.depth()).is_zero()


def _validate_sigma(sigma: List[List[Int]]) raises:
    if len(sigma) != 3:
        raise Error("affine trace requires a three-letter substitution")
    for a in range(3):
        if len(sigma[a]) == 0:
            raise Error("affine trace requires a non-erasing substitution")
        for j in range(len(sigma[a])):
            if sigma[a][j] < 0 or sigma[a][j] >= 3:
                raise Error("affine-trace substitution letter lies outside 0..2")


def _incidence_action(sigma: List[List[Int]], x: Diff3) -> Diff3:
    var out = Diff3(0, 0, 0)
    for a in range(3):
        var coefficient = x.x
        if a == 1:
            coefficient = x.y
        elif a == 2:
            coefficient = x.z
        for j in range(len(sigma[a])):
            var b = sigma[a][j]
            if b == 0:
                out.x += coefficient
            elif b == 1:
                out.y += coefficient
            else:
                out.z += coefficient
    return out^


def _prefix_parikh(sigma: List[List[Int]], parent: Int, child_index: Int) raises -> Diff3:
    if parent < 0 or parent >= 3:
        raise Error("affine-trace parent letter lies outside 0..2")
    if child_index < 0 or child_index >= len(sigma[parent]):
        raise Error("affine-trace child index lies outside parent image")
    var out = Diff3(0, 0, 0)
    for j in range(child_index):
        var a = sigma[parent][j]
        if a == 0:
            out.x += 1
        elif a == 1:
            out.y += 1
        else:
            out.z += 1
    return out^


def affine_ancestry_trace(sigma: List[List[Int]], address: RelativeRenewalAddress) raises -> AffineAncestryTrace:
    _validate_sigma(sigma)
    if address.level <= 0:
        raise Error("affine trace requires a positive address level")
    if len(address.top_digits) != 2 * address.level or len(address.bottom_digits) != 2 * address.level:
        raise Error("affine-trace digit length does not match address level")
    var top_letters = List[Int]()
    var bottom_letters = List[Int]()
    var defects = List[Int]()
    var top = address.top_source_letter
    var bottom = address.bottom_source_letter
    var x = address.source_defect.copy()
    top_letters.append(top)
    bottom_letters.append(bottom)
    defects.append(x.x)
    defects.append(x.y)
    defects.append(x.z)
    for t in range(address.level):
        var top_parent = address.top_digits[2 * t]
        var top_index = address.top_digits[2 * t + 1]
        var bottom_parent = address.bottom_digits[2 * t]
        var bottom_index = address.bottom_digits[2 * t + 1]
        if top_parent != top or bottom_parent != bottom:
            raise Error("affine-trace digits do not follow substitution paths")
        var tp = _prefix_parikh(sigma, top_parent, top_index)
        var bp = _prefix_parikh(sigma, bottom_parent, bottom_index)
        var next = _incidence_action(sigma, x)
        next.x += tp.x - bp.x
        next.y += tp.y - bp.y
        next.z += tp.z - bp.z
        top = sigma[top_parent][top_index]
        bottom = sigma[bottom_parent][bottom_index]
        x = next.copy()
        top_letters.append(top)
        bottom_letters.append(bottom)
        defects.append(x.x)
        defects.append(x.y)
        defects.append(x.z)
    var trace = AffineAncestryTrace(top_letters, bottom_letters, defects)
    if not trace.closes():
        raise Error("affine ancestry recurrence does not close at the renewal cut")
    return trace^


def same_affine_state(a: AffineAncestryTrace, ai: Int, b: AffineAncestryTrace, bi: Int) raises -> Bool:
    if ai < 0 or ai >= a.state_count() or bi < 0 or bi >= b.state_count():
        raise Error("affine-state comparison index is out of range")
    return a.top_letters[ai] == b.top_letters[bi] and a.bottom_letters[ai] == b.bottom_letters[bi] and a.defect_at(ai) == b.defect_at(bi)


def common_terminal_trace_length(a: AffineAncestryTrace, b: AffineAncestryTrace) raises -> Int:
    var count = 0
    var ai = a.state_count() - 1
    var bi = b.state_count() - 1
    while ai >= 0 and bi >= 0 and same_affine_state(a, ai, b, bi):
        count += 1
        ai -= 1
        bi -= 1
    return count


def first_repeated_affine_state(trace: AffineAncestryTrace) raises -> Tuple[Int, Int]:
    for right in range(1, trace.state_count()):
        for left in range(right):
            if same_affine_state(trace, left, trace, right):
                return (left, right)
    return (-1, -1)
