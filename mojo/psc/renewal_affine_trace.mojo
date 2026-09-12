"""Order-sensitive affine prefix-suffix traces for the open G1b-2 program.

This module is a finite symbolic diagnostic.  It does not assert renewal
finiteness and does not identify a shortened symbolic path with the same
physical renewal state unless that shortened path is independently observed and
certified elsewhere.

For a paired substitution edge at ancestry level t, let q_t be the difference
between the top and bottom proper-prefix Parikh vectors.  Starting from the
source prefix defect delta, evolve

    x_0 = delta
    x_{t+1} = M x_t + q_t.

For a certified renewal address the terminal residual is zero.  The trace state
at a boundary between ancestry levels is

    (top_current_letter, bottom_current_letter, x_t).

If the same exact state occurs at two *proper internal* boundaries 0 < i < j < d,
the paired edge block i..j-1 is a candidate symbolic pump cycle: deleting it
preserves path compatibility at the splice and preserves the terminal affine
residual.  Start/terminal repeats are deliberately excluded so an interior
renewal address is not collapsed to a trivial depth-zero boundary.
"""

from psc.renewal import Diff3
from psc.renewal_address import RelativeRenewalAddress, RenewalAddressTables


struct AffinePath(Copyable, Movable):
    """Symbolic path data needed by the affine trace, without certification claims."""

    var source_index_delta: Int
    var source_defect: Diff3
    var top_source_letter: Int
    var bottom_source_letter: Int
    var top_digits: List[Int]
    var bottom_digits: List[Int]

    def __init__(
        out self,
        source_index_delta: Int,
        source_defect: Diff3,
        top_source_letter: Int,
        bottom_source_letter: Int,
        top_digits: List[Int],
        bottom_digits: List[Int],
    ):
        self.source_index_delta = source_index_delta
        self.source_defect = source_defect.copy()
        self.top_source_letter = top_source_letter
        self.bottom_source_letter = bottom_source_letter
        self.top_digits = top_digits.copy()
        self.bottom_digits = bottom_digits.copy()

    def level(self) -> Int:
        return len(self.top_digits) // 2


struct AffineTrace(Copyable, Movable):
    """Flat exact states `[top,bottom,x,y,z]` for boundaries 0..level."""

    var level: Int
    var states: List[Int]

    def __init__(out self, level: Int, states: List[Int]):
        self.level = level
        self.states = states.copy()

    def state_count(self) -> Int:
        return self.level + 1

    def top_letter(self, index: Int) raises -> Int:
        if index < 0 or index >= self.state_count():
            raise Error("affine-trace state index is out of range")
        return self.states[5 * index]

    def bottom_letter(self, index: Int) raises -> Int:
        if index < 0 or index >= self.state_count():
            raise Error("affine-trace state index is out of range")
        return self.states[5 * index + 1]

    def residual(self, index: Int) raises -> Diff3:
        if index < 0 or index >= self.state_count():
            raise Error("affine-trace state index is out of range")
        var k = 5 * index + 2
        return Diff3(self.states[k], self.states[k + 1], self.states[k + 2])

    def same_state(self, i: Int, j: Int) raises -> Bool:
        if i < 0 or i >= self.state_count() or j < 0 or j >= self.state_count():
            raise Error("affine-trace state comparison index is out of range")
        var a = 5 * i
        var b = 5 * j
        for q in range(5):
            if self.states[a + q] != self.states[b + q]:
                return False
        return True


struct ProperAffineRepeat(Copyable, Movable):
    var found: Bool
    var start: Int
    var end: Int

    def __init__(out self, found: Bool, start: Int, end: Int):
        self.found = found
        self.start = start
        self.end = end

    def length(self) -> Int:
        if not self.found:
            return 0
        return self.end - self.start


def affine_path_from_address(address: RelativeRenewalAddress) raises -> AffinePath:
    if address.level <= 0:
        raise Error("affine trace requires a positive-level renewal address")
    if len(address.top_digits) != 2 * address.level:
        raise Error("affine trace top digit length does not match address level")
    if len(address.bottom_digits) != 2 * address.level:
        raise Error("affine trace bottom digit length does not match address level")
    if not address.certificate_closes():
        raise Error("affine trace requires a closing renewal certificate")
    return AffinePath(
        address.source_index_delta,
        address.source_defect,
        address.top_source_letter,
        address.bottom_source_letter,
        address.top_digits,
        address.bottom_digits,
    )


def same_affine_path(a: AffinePath, b: AffinePath) -> Bool:
    return (
        a.source_index_delta == b.source_index_delta
        and a.source_defect == b.source_defect
        and a.top_source_letter == b.top_source_letter
        and a.bottom_source_letter == b.bottom_source_letter
        and a.top_digits == b.top_digits
        and a.bottom_digits == b.bottom_digits
    )


def _append_state(
    mut out: List[Int], top_letter: Int, bottom_letter: Int, residual: Diff3
):
    out.append(top_letter)
    out.append(bottom_letter)
    out.append(residual.x)
    out.append(residual.y)
    out.append(residual.z)


def _proper_prefix_parikh(
    tables: RenewalAddressTables, parent: Int, child_index: Int
) raises -> Diff3:
    if parent < 0 or parent >= 3:
        raise Error("affine-trace parent letter lies outside 0..2")
    if child_index < 0 or child_index >= len(tables.sigma[parent]):
        raise Error("affine-trace child index lies outside parent image")
    var x = 0
    var y = 0
    var z = 0
    for j in range(child_index):
        var a = tables.sigma[parent][j]
        if a == 0:
            x += 1
        elif a == 1:
            y += 1
        elif a == 2:
            z += 1
        else:
            raise Error("affine-trace substitution letter lies outside 0..2")
    return Diff3(x, y, z)


def _apply_incidence(tables: RenewalAddressTables, v: Diff3) raises -> Diff3:
    if tables.depth < 1:
        raise Error("affine trace requires incidence data through level one")
    var c0 = tables.image_parikh(1, 0)
    var c1 = tables.image_parikh(1, 1)
    var c2 = tables.image_parikh(1, 2)
    return Diff3(
        c0.x * v.x + c1.x * v.y + c2.x * v.z,
        c0.y * v.x + c1.y * v.y + c2.y * v.z,
        c0.z * v.x + c1.z * v.y + c2.z * v.z,
    )


def build_affine_trace(
    tables: RenewalAddressTables, path: AffinePath
) raises -> AffineTrace:
    var level = path.level()
    if level <= 0:
        raise Error("affine trace requires a nonempty symbolic path")
    if level > tables.depth:
        raise Error("affine trace path exceeds prepared substitution depth")
    if len(path.bottom_digits) != 2 * level:
        raise Error("affine trace side digit lengths disagree")
    if path.top_source_letter < 0 or path.top_source_letter >= 3:
        raise Error("affine trace top source letter lies outside 0..2")
    if path.bottom_source_letter < 0 or path.bottom_source_letter >= 3:
        raise Error("affine trace bottom source letter lies outside 0..2")

    var states = List[Int]()
    var top_current = path.top_source_letter
    var bottom_current = path.bottom_source_letter
    var x = path.source_defect.copy()
    _append_state(states, top_current, bottom_current, x)

    for t in range(level):
        var top_parent = path.top_digits[2 * t]
        var top_child_index = path.top_digits[2 * t + 1]
        var bottom_parent = path.bottom_digits[2 * t]
        var bottom_child_index = path.bottom_digits[2 * t + 1]
        if top_parent != top_current or bottom_parent != bottom_current:
            raise Error("affine trace digit path parent continuity failed")

        var top_prefix = _proper_prefix_parikh(
            tables, top_parent, top_child_index
        )
        var bottom_prefix = _proper_prefix_parikh(
            tables, bottom_parent, bottom_child_index
        )
        var mx = _apply_incidence(tables, x)
        x = Diff3(
            mx.x + top_prefix.x - bottom_prefix.x,
            mx.y + top_prefix.y - bottom_prefix.y,
            mx.z + top_prefix.z - bottom_prefix.z,
        )
        top_current = tables.sigma[top_parent][top_child_index]
        bottom_current = tables.sigma[bottom_parent][bottom_child_index]
        _append_state(states, top_current, bottom_current, x)

    if x.x != 0 or x.y != 0 or x.z != 0:
        raise Error("affine trace terminal residual does not close")
    return AffineTrace(level, states)


def first_proper_affine_repeat(trace: AffineTrace) raises -> ProperAffineRepeat:
    """Find the earliest repeated state strictly inside the path boundaries."""
    if trace.level < 3:
        return ProperAffineRepeat(False, -1, -1)
    for end in range(2, trace.level):
        for start in range(1, end):
            if trace.same_state(start, end):
                return ProperAffineRepeat(True, start, end)
    return ProperAffineRepeat(False, -1, -1)


def delete_proper_affine_cycle(
    tables: RenewalAddressTables,
    path: AffinePath,
    start: Int,
    end: Int,
) raises -> AffinePath:
    """Delete one certified repeated-state block from the symbolic path only."""
    var trace = build_affine_trace(tables, path)
    if start <= 0 or end <= start or end >= trace.level:
        raise Error("affine cycle deletion requires 0 < start < end < level")
    if not trace.same_state(start, end):
        raise Error("affine cycle deletion endpoints are not the same exact state")

    var top = List[Int]()
    var bottom = List[Int]()
    for t in range(trace.level):
        if t < start or t >= end:
            top.append(path.top_digits[2 * t])
            top.append(path.top_digits[2 * t + 1])
            bottom.append(path.bottom_digits[2 * t])
            bottom.append(path.bottom_digits[2 * t + 1])

    var reduced = AffinePath(
        path.source_index_delta,
        path.source_defect,
        path.top_source_letter,
        path.bottom_source_letter,
        top,
        bottom,
    )
    # Rebuild the trace to verify splice continuity and terminal closure.  This
    # validates a symbolic affine reduction only, not physical realization.
    _ = build_affine_trace(tables, reduced)
    return reduced^


def reduce_first_proper_affine_cycle(
    tables: RenewalAddressTables, path: AffinePath
) raises -> AffinePath:
    var trace = build_affine_trace(tables, path)
    var repeat = first_proper_affine_repeat(trace)
    if not repeat.found:
        return AffinePath(
            path.source_index_delta,
            path.source_defect,
            path.top_source_letter,
            path.bottom_source_letter,
            path.top_digits,
            path.bottom_digits,
        )
    return delete_proper_affine_cycle(tables, path, repeat.start, repeat.end)
