"""Finite first-child hub-phase classifier for alphabet-3 endpoint maps.

Fix a Barge-Diamond-good unordered pair G={a,b} and let c be the complementary
hub. A strict right-boundary first pair must be one of the other two edges and
must remain distinct while avoiding G under every iterate of the prefix endpoint
map h.

For a canonical ordered pair p=(lo,hi), the parent hub side is determined by
whether c=lo or c=hi. The raw first child begins with (h(lo),h(hi)), so the
physical child hub side is known before normalization. Their xor is exactly the
hub residual on the deterministic first-child occurrence.

For endpoint types C-F, exhaustive finite classification shows that every viable
strict pair for one fixed (h,G) has the same residual bit. C/D give phase 0; F
gives phase 1; E gives phase 0 or 1 depending on the position of G. Some C/F
placements admit no viable strict pair at all.
"""

from psc.bd_endpoint import complementary_hub_letter, unordered_pair_id
from psc.endpoint_core import endpoint_type


def _validate_letter(a: Int) raises:
    if a < 0 or a >= 3:
        raise Error("letter lies outside 0..2")


def _validate_map(h: List[Int]) raises:
    if len(h) != 3:
        raise Error("endpoint map must have exactly three letters")
    for i in range(3):
        _validate_letter(h[i])


def _sorted_pair(a: Int, b: Int) raises -> List[Int]:
    _ = unordered_pair_id(a, b)
    if a < b:
        return [a, b]
    return [b, a]


def pair_equals(a: Int, b: Int, c: Int, d: Int) raises -> Bool:
    var p = _sorted_pair(a, b)
    var q = _sorted_pair(c, d)
    return p[0] == q[0] and p[1] == q[1]


def strict_star_pair_viable(
    h: List[Int], good_a: Int, good_b: Int, pair_a: Int, pair_b: Int
) raises -> Bool:
    """Necessary endpoint-orbit condition for one strict first-letter pair.

    A viable orbit must remain distinct and avoid the fixed Barge-Diamond-good
    edge forever. On three unordered pairs, four nonterminal steps suffice to
    reach a repeated pair if neither forbidden event occurs.
    """
    _validate_map(h)
    _ = unordered_pair_id(good_a, good_b)
    _ = unordered_pair_id(pair_a, pair_b)
    if pair_equals(good_a, good_b, pair_a, pair_b):
        return False

    var x = pair_a
    var y = pair_b
    var seen_mask = 0
    for _ in range(4):
        if x == y:
            return False
        if pair_equals(good_a, good_b, x, y):
            return False
        var bit = 1 << unordered_pair_id(x, y)
        if (seen_mask & bit) != 0:
            return True
        seen_mask |= bit
        x = h[x]
        y = h[y]
    return True


def first_child_hub_residual(
    h: List[Int], good_a: Int, good_b: Int, pair_a: Int, pair_b: Int
) raises -> Int:
    """Hub-side residual bit on the raw deterministic first-child occurrence.

    Returns -1 when the supplied strict pair is not viable for the fixed good
    edge. Otherwise returns 0/1 according to whether the physical hub stays on
    the same canonical side from parent to first child.
    """
    _validate_map(h)
    if not strict_star_pair_viable(h, good_a, good_b, pair_a, pair_b):
        return -1
    var hub = complementary_hub_letter(good_a, good_b)
    var p = _sorted_pair(pair_a, pair_b)
    if p[0] != hub and p[1] != hub:
        raise Error("viable strict pair does not contain the complementary hub")
    var parent_side = 0
    if p[1] == hub:
        parent_side = 1

    var raw_top = h[p[0]]
    var raw_bottom = h[p[1]]
    if raw_top == raw_bottom:
        raise Error("viable strict pair unexpectedly coalesces at first child")
    var child_side = -1
    if raw_top == hub:
        child_side = 0
    elif raw_bottom == hub:
        child_side = 1
    else:
        raise Error("viable first child lost the complementary hub")
    return parent_side ^ child_side


def strict_star_selector_phase(h: List[Int], good_a: Int, good_b: Int) raises -> Int:
    """Constant first-child hub residual over viable strict star pairs.

    Return values:
      -1 : no viable strict first-pair orbit for this (h, good edge),
       0/1: all viable strict pairs have that common residual bit,
       2 : mixed residual bits (generic sentinel; does not occur for C-F).
    """
    _validate_map(h)
    _ = unordered_pair_id(good_a, good_b)
    var phase = -1
    for a in range(3):
        for b in range(a + 1, 3):
            var r = first_child_hub_residual(h, good_a, good_b, a, b)
            if r < 0:
                continue
            if phase == -1:
                phase = r
            elif phase != r:
                return 2
    return phase


def cdef_phase_is_uniform(h: List[Int], good_a: Int, good_b: Int) raises -> Bool:
    """Exact finite normal-form assertion for endpoint types C/D/E/F."""
    var t = endpoint_type(h)
    if t < 2 or t > 5:
        return False
    return strict_star_selector_phase(h, good_a, good_b) != 2
