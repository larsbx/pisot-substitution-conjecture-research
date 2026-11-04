"""Replay a supplied coincidence address to an actual one-step newborn cut."""

from psc.bpa import apply_substitution, coincidence_boundaries, image_prefix_lengths
from psc.words import ALPHABET, Pair, is_balanced
from substitution_dynamics.substitution import validate_word


struct AddressedNewborn(Copyable, Movable):
    var parent: Pair
    # The final ordinal selects the first diagonal; earlier ordinals select its ancestors.
    var ordinals: List[Int]
    var cut: Int
    var sync_right: Bool

    def __init__(out self, parent: Pair, ordinals: List[Int], cut: Int, sync_right: Bool):
        self.parent = parent.copy()
        self.ordinals = ordinals.copy()
        self.cut = cut
        self.sync_right = sync_right


def _factor_at(cuts: List[Int], pos: Int) -> Int:
    for j in range(len(cuts) - 1):
        if pos < cuts[j + 1]:
            return j
    return -1


def addressed_newborn(
    sigma: List[List[Int]], root: Pair, top_source: Int, bottom_source: Int,
    top_digits: List[Int], bottom_digits: List[Int], word_cap: Int = 4096,
) raises -> AddressedNewborn:
    """Use literal child words and validate the entire supplied witness.

    The output is the first diagonal on the marked path. A genuine witness
    can never split across an inherited cut. Caps are diagnostic only.
    """
    if len(sigma) != ALPHABET or word_cap <= 0 or word_cap > 65536:
        raise Error("invalid addressed newborn alphabet or word budget")
    for a in range(ALPHABET):
        if len(sigma[a]) == 0 or len(sigma[a]) > word_cap:
            raise Error("invalid addressed newborn image size")
        validate_word(sigma[a], ALPHABET)
    if root.length() < 2 or root.length() > word_cap or len(root.u) != len(root.v):
        raise Error("addressed newborn source length invalid")
    validate_word(root.u, ALPHABET)
    validate_word(root.v, ALPHABET)
    if not is_balanced(root) or len(coincidence_boundaries(root.u, root.v)) != 2:
        raise Error("addressed newborn source must be irreducible balanced")
    if top_source < 0 or top_source >= root.length() or bottom_source < 0 or bottom_source >= root.length():
        raise Error("addressed newborn source index invalid")
    if len(top_digits) == 0 or len(top_digits) != len(bottom_digits):
        raise Error("addressed newborn paths need equal positive depth")

    var parent = root.copy()
    var top_mark = top_source
    var bottom_mark = bottom_source
    var path = List[Int]()
    var witness = AddressedNewborn(root, path, -1, False)
    for depth in range(len(top_digits)):
        var top_digit = top_digits[depth]
        var bottom_digit = bottom_digits[depth]
        if top_digit < 0 or top_digit >= len(sigma[parent.u[top_mark]]):
            raise Error("addressed newborn top digit invalid")
        if bottom_digit < 0 or bottom_digit >= len(sigma[parent.v[bottom_mark]]):
            raise Error("addressed newborn bottom digit invalid")

        var top_bounds = image_prefix_lengths(sigma, parent.u)
        var bottom_bounds = image_prefix_lengths(sigma, parent.v)
        var length = top_bounds[len(top_bounds) - 1]
        if length > word_cap:
            raise Error("addressed newborn inflation exceeds word budget")
        var top_pos = top_bounds[top_mark] + top_digit
        var bottom_pos = bottom_bounds[bottom_mark] + bottom_digit
        var top = apply_substitution(sigma, parent.u)
        var bottom = apply_substitution(sigma, parent.v)
        var cuts = coincidence_boundaries(top, bottom)
        var ordinal = _factor_at(cuts, top_pos)
        if ordinal < 0 or ordinal != _factor_at(cuts, bottom_pos):
            raise Error("addressed newborn witness split across balanced factors")
        path.append(ordinal)

        var start = cuts[ordinal]
        var end = cuts[ordinal + 1]
        if end - start == 1 and witness.cut < 0:
            # The preceding parent is noncoincident and has length >= 2.
            # If the left cut is exterior, use the right cut of the diagonal.
            if start > 0:
                witness = AddressedNewborn(parent, path, start, True)
            else:
                witness = AddressedNewborn(parent, path, end, False)

        var child_u = List[Int]()
        var child_v = List[Int]()
        for k in range(start, end):
            child_u.append(top[k])
            child_v.append(bottom[k])
        parent = Pair(child_u, child_v)
        top_mark = top_pos - start
        bottom_mark = bottom_pos - start

    if not parent.is_coincidence() or witness.cut < 0:
        raise Error("addressed newborn paths do not end in coincidence")
    return witness^
