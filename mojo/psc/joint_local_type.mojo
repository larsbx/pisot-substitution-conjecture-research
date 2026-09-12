"""Finite-window joint local projections for the G1b-2 renewal program.

This module deliberately does not assert that any fixed projection is complete.
It combines bounded source-word context with bounded head/tail windows of the
symbolic renewal address and is intended to *falsify* insufficient finite-state
proposals before they are promoted into a theorem.

For fixed `source_radius` and `digit_window`, the stored source context and digit
windows have bounded size independent of substitution depth.  The projection
omits absolute source indices, total inflated length, substitution level,
`M^d delta`, and the full digit path.  These omissions are intentional: the
object is a candidate finite local type, not a complete address.
"""

from psc.renewal import Diff3
from psc.renewal_address import (
    RenewalPairCensusState,
    RelativeRenewalAddress,
    renewal_cut_address_from_state,
)


struct JointLocalType(Copyable, Movable):
    """One bounded local projection of a certified renewal cut."""

    var source_radius: Int
    var digit_window: Int
    var source_index_delta: Int
    var source_defect: Diff3
    var top_source_letter: Int
    var bottom_source_letter: Int
    var source_context: List[Int]
    var top_head: List[Int]
    var top_tail: List[Int]
    var bottom_head: List[Int]
    var bottom_tail: List[Int]

    def __init__(
        out self,
        source_radius: Int,
        digit_window: Int,
        source_index_delta: Int,
        source_defect: Diff3,
        top_source_letter: Int,
        bottom_source_letter: Int,
        source_context: List[Int],
        top_head: List[Int],
        top_tail: List[Int],
        bottom_head: List[Int],
        bottom_tail: List[Int],
    ):
        self.source_radius = source_radius
        self.digit_window = digit_window
        self.source_index_delta = source_index_delta
        self.source_defect = source_defect.copy()
        self.top_source_letter = top_source_letter
        self.bottom_source_letter = bottom_source_letter
        self.source_context = source_context.copy()
        self.top_head = top_head.copy()
        self.top_tail = top_tail.copy()
        self.bottom_head = bottom_head.copy()
        self.bottom_tail = bottom_tail.copy()


def _source_index(boundaries: List[Int], source_length: Int, cut: Int) raises -> Int:
    if source_length <= 0 or len(boundaries) != source_length + 1:
        raise Error("joint-local source metadata is malformed")
    if cut < 0 or cut >= boundaries[len(boundaries) - 1]:
        raise Error("joint-local cut lies outside the prepared source side")

    var lo = 0
    var hi = source_length
    while lo < hi:
        var mid = (lo + hi) // 2
        if boundaries[mid + 1] <= cut:
            lo = mid + 1
        else:
            hi = mid
    return lo


def _append_context(
    mut out: List[Int], letters: List[Int], index: Int, radius: Int
):
    # Sentinel 3 is outside the standing alphabet 0..2.
    for j in range(index - radius, index + radius + 1):
        if j < 0 or j >= len(letters):
            out.append(3)
        else:
            out.append(letters[j])


def _digit_head(digits: List[Int], window: Int) raises -> List[Int]:
    if len(digits) % 2 != 0:
        raise Error("joint-local digit path must contain parent/index pairs")
    var levels = len(digits) // 2
    var take = window
    if take > levels:
        take = levels
    var out = List[Int]()
    for i in range(2 * take):
        out.append(digits[i])
    return out^


def _digit_tail(digits: List[Int], window: Int) raises -> List[Int]:
    if len(digits) % 2 != 0:
        raise Error("joint-local digit path must contain parent/index pairs")
    var levels = len(digits) // 2
    var take = window
    if take > levels:
        take = levels
    var out = List[Int]()
    var start = len(digits) - 2 * take
    for i in range(start, len(digits)):
        out.append(digits[i])
    return out^


def joint_local_type_from_address(
    state: RenewalPairCensusState,
    cut: Int,
    address: RelativeRenewalAddress,
    source_radius: Int,
    digit_window: Int,
) raises -> JointLocalType:
    """Project one certified address to bounded source/digit context."""
    if source_radius < 0 or digit_window < 0:
        raise Error("joint-local radius and digit window must be nonnegative")
    if cut <= 0 or cut >= state.inflated_length:
        raise Error("joint-local cut must be interior")

    var top_index = _source_index(
        state.top.boundaries, state.top.source_length(), cut
    )
    var bottom_index = _source_index(
        state.bottom.boundaries, state.bottom.source_length(), cut
    )

    var context = List[Int]()
    _append_context(context, state.top.letters, top_index, source_radius)
    _append_context(context, state.bottom.letters, bottom_index, source_radius)

    return JointLocalType(
        source_radius,
        digit_window,
        address.source_index_delta,
        address.source_defect,
        address.top_source_letter,
        address.bottom_source_letter,
        context,
        _digit_head(address.top_digits, digit_window),
        _digit_tail(address.top_digits, digit_window),
        _digit_head(address.bottom_digits, digit_window),
        _digit_tail(address.bottom_digits, digit_window),
    )


def joint_local_type(
    state: RenewalPairCensusState,
    cut: Int,
    source_radius: Int,
    digit_window: Int,
) raises -> JointLocalType:
    var address = renewal_cut_address_from_state(state, cut)
    return joint_local_type_from_address(
        state, cut, address, source_radius, digit_window
    )


def same_joint_local_type(a: JointLocalType, b: JointLocalType) -> Bool:
    return (
        a.source_radius == b.source_radius
        and a.digit_window == b.digit_window
        and a.source_index_delta == b.source_index_delta
        and a.source_defect == b.source_defect
        and a.top_source_letter == b.top_source_letter
        and a.bottom_source_letter == b.bottom_source_letter
        and a.source_context == b.source_context
        and a.top_head == b.top_head
        and a.top_tail == b.top_tail
        and a.bottom_head == b.bottom_head
        and a.bottom_tail == b.bottom_tail
    )
