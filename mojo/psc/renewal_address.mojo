"""Level-scaled symbolic renewal addresses for the G1b-2 program.

This module augments the labelled first-return representation with exact
substitution ancestry for an interior zero-return cut of sigma^depth(pair).
It deliberately stays in integer/symbolic coordinates.  No inverse incidence
matrix, Euclidean stable projection, lattice assumption, or unit determinant is
used.

For a selected zero-return cut, desubstitution gives a prefix defect delta at
the source level plus two finite substitution-digit paths.  Their partial-image
correction c satisfies the exact certificate

    M^depth delta + c = 0.

The record stores only the *relative* source-index displacement, source defect,
source letters, and digit paths.  Absolute source indices and inflated word
length are not part of the address.  The address is auxiliary data and must be
retained together with the labelled return word: distinct labelled returns can
share the same relative address.

Inflated words are never materialized.  Image lengths and full-image Parikh
vectors are obtained by three-coordinate dynamic/matrix recurrences, while the
selected cut is descended through one substitution image at each level.
"""

from psc.bpa import substitution_incidence
from psc.legal_tower import image_lengths_at_depth
from psc.renewal import Diff3, strict_first_return_word
from psc.words import Pair


struct _SourceLocation(Copyable, Movable):
    var index: Int
    var letter: Int
    var offset: Int

    def __init__(out self, index: Int, letter: Int, offset: Int):
        self.index = index
        self.letter = letter
        self.offset = offset


struct _SideAddress(Copyable, Movable):
    var digits: List[Int]
    var prefix: Diff3

    def __init__(out self, digits: List[Int], prefix: Diff3):
        self.digits = digits.copy()
        self.prefix = prefix.copy()


struct RelativeRenewalAddress(Copyable, Movable):
    """Relative symbolic address of one inflated interior renewal cut.

    `top_digits` and `bottom_digits` are flat `(parent_letter, child_index)`
    pairs, one pair per substitution level.  Child letters are determined by
    sigma and are therefore not duplicated in the record.
    """

    var level: Int
    var source_index_delta: Int
    var source_defect: Diff3
    var top_source_letter: Int
    var bottom_source_letter: Int
    var top_digits: List[Int]
    var bottom_digits: List[Int]
    var scaled_defect: Diff3
    var correction: Diff3

    def __init__(
        out self,
        level: Int,
        source_index_delta: Int,
        source_defect: Diff3,
        top_source_letter: Int,
        bottom_source_letter: Int,
        top_digits: List[Int],
        bottom_digits: List[Int],
        scaled_defect: Diff3,
        correction: Diff3,
    ):
        self.level = level
        self.source_index_delta = source_index_delta
        self.source_defect = source_defect.copy()
        self.top_source_letter = top_source_letter
        self.bottom_source_letter = bottom_source_letter
        self.top_digits = top_digits.copy()
        self.bottom_digits = bottom_digits.copy()
        self.scaled_defect = scaled_defect.copy()
        self.correction = correction.copy()

    def digit_levels(self) -> Int:
        return len(self.top_digits) // 2

    def certificate_closes(self) -> Bool:
        return (
            self.scaled_defect.x + self.correction.x == 0
            and self.scaled_defect.y + self.correction.y == 0
            and self.scaled_defect.z + self.correction.z == 0
        )


def _validate_sigma(sigma: List[List[Int]]) raises:
    if len(sigma) != 3:
        raise Error("renewal-address kernel requires a three-letter substitution")
    for a in range(3):
        if len(sigma[a]) == 0:
            raise Error("renewal-address substitution must be non-erasing")
        for j in range(len(sigma[a])):
            if sigma[a][j] < 0 or sigma[a][j] >= 3:
                raise Error("renewal-address substitution letter lies outside 0..2")


def _unit(a: Int) raises -> Diff3:
    if a == 0:
        return Diff3(1, 0, 0)
    if a == 1:
        return Diff3(0, 1, 0)
    if a == 2:
        return Diff3(0, 0, 1)
    raise Error("renewal-address source letter lies outside 0..2")


def _add(a: Diff3, b: Diff3) -> Diff3:
    return Diff3(a.x + b.x, a.y + b.y, a.z + b.z)


def _sub(a: Diff3, b: Diff3) -> Diff3:
    return Diff3(a.x - b.x, a.y - b.y, a.z - b.z)


def _matrix_apply(m: List[Int], v: Diff3) raises -> Diff3:
    if len(m) != 9:
        raise Error("renewal-address incidence matrix must be 3x3")
    return Diff3(
        m[0] * v.x + m[1] * v.y + m[2] * v.z,
        m[3] * v.x + m[4] * v.y + m[5] * v.z,
        m[6] * v.x + m[7] * v.y + m[8] * v.z,
    )


def _matrix_apply_n(m: List[Int], v: Diff3, depth: Int) raises -> Diff3:
    if depth < 0:
        raise Error("renewal-address depth must be nonnegative")
    var out = v.copy()
    for _ in range(depth):
        out = _matrix_apply(m, out)
    return out^


def _prefix_defect(pair: Pair, top_cut: Int, bottom_cut: Int) raises -> Diff3:
    if (
        top_cut < 0
        or top_cut > len(pair.u)
        or bottom_cut < 0
        or bottom_cut > len(pair.v)
    ):
        raise Error("renewal-address source prefix lies outside the pair")
    var x = 0
    var y = 0
    var z = 0
    for i in range(top_cut):
        var a = pair.u[i]
        if a == 0:
            x += 1
        elif a == 1:
            y += 1
        elif a == 2:
            z += 1
        else:
            raise Error("renewal-address pair letter lies outside 0..2")
    for i in range(bottom_cut):
        var a = pair.v[i]
        if a == 0:
            x -= 1
        elif a == 1:
            y -= 1
        elif a == 2:
            z -= 1
        else:
            raise Error("renewal-address pair letter lies outside 0..2")
    return Diff3(x, y, z)


def _word_image_length(
    sigma: List[List[Int]], word: List[Int], depth: Int
) raises -> Int:
    var lengths = image_lengths_at_depth(sigma, depth)
    var total = 0
    for i in range(len(word)):
        var a = word[i]
        if a < 0 or a >= 3:
            raise Error("renewal-address word letter lies outside 0..2")
        total += lengths[a]
    return total


def _locate_source(
    sigma: List[List[Int]], word: List[Int], depth: Int, cut: Int
) raises -> _SourceLocation:
    var lengths = image_lengths_at_depth(sigma, depth)
    var total = 0
    for i in range(len(word)):
        total += lengths[word[i]]
    if cut < 0 or cut >= total:
        raise Error("renewal-address cut must select a source supertile")

    var cursor = 0
    for i in range(len(word)):
        var a = word[i]
        var next = cursor + lengths[a]
        if cut < next:
            return _SourceLocation(i, a, cut - cursor)
        cursor = next
    raise Error("renewal-address source location was not found")


def _prefix_inside_source_letter(
    sigma: List[List[Int]],
    incidence: List[Int],
    source_letter: Int,
    depth: Int,
    offset: Int,
) raises -> _SideAddress:
    """Descend one cut through sigma^depth(source_letter) without expanding it."""
    if depth <= 0:
        raise Error("renewal-address symbolic path requires positive depth")
    var full_lengths = image_lengths_at_depth(sigma, depth)
    if offset < 0 or offset >= full_lengths[source_letter]:
        raise Error("renewal-address within-supertile offset is out of range")

    var digits = List[Int]()
    var prefix = Diff3(0, 0, 0)
    var current_letter = source_letter
    var residual = offset
    var level = depth

    while level > 0:
        var child_lengths = image_lengths_at_depth(sigma, level - 1)
        var child_start = 0
        var found = False
        for j in range(len(sigma[current_letter])):
            var child = sigma[current_letter][j]
            var block_length = child_lengths[child]
            if residual < child_start + block_length:
                digits.append(current_letter)
                digits.append(j)
                residual -= child_start
                current_letter = child
                found = True
                break
            var complete = _matrix_apply_n(incidence, _unit(child), level - 1)
            prefix = _add(prefix, complete)
            child_start += block_length
        if not found:
            raise Error("renewal-address digit descent failed to select a child")
        level -= 1

    if residual != 0:
        raise Error("renewal-address leaf residual must vanish")
    return _SideAddress(digits, prefix)


def same_relative_address(a: RelativeRenewalAddress, b: RelativeRenewalAddress) -> Bool:
    return (
        a.level == b.level
        and a.source_index_delta == b.source_index_delta
        and a.source_defect == b.source_defect
        and a.top_source_letter == b.top_source_letter
        and a.bottom_source_letter == b.bottom_source_letter
        and a.top_digits == b.top_digits
        and a.bottom_digits == b.bottom_digits
        and a.scaled_defect == b.scaled_defect
        and a.correction == b.correction
    )


def renewal_cut_address(
    sigma: List[List[Int]], pair: Pair, depth: Int, cut: Int
) raises -> RelativeRenewalAddress:
    """Return the exact relative address of an interior zero return.

    `pair` itself must be a strict labelled first return. `cut` is an aligned
    physical position in `sigma^depth(pair.u)` and `sigma^depth(pair.v)` whose
    prefix Parikh vectors agree.  The implementation verifies the zero-return
    property through the integer certificate rather than materializing either
    inflated word.
    """
    _validate_sigma(sigma)
    if depth <= 0:
        raise Error("renewal-address depth must be positive")

    # Reuse the canonical strict contract from the labelled-renewal layer.
    var checked = strict_first_return_word(pair)
    if not checked.first_return:
        raise Error("renewal-address source pair is not a first return")

    var top_length = _word_image_length(sigma, pair.u, depth)
    var bottom_length = _word_image_length(sigma, pair.v, depth)
    if top_length != bottom_length:
        raise Error("balanced renewal pair has unequal inflated side lengths")
    if cut <= 0 or cut >= top_length:
        raise Error("renewal-address cut must be interior")

    var incidence = substitution_incidence(sigma)
    var top = _locate_source(sigma, pair.u, depth, cut)
    var bottom = _locate_source(sigma, pair.v, depth, cut)
    var top_side = _prefix_inside_source_letter(
        sigma, incidence, top.letter, depth, top.offset
    )
    var bottom_side = _prefix_inside_source_letter(
        sigma, incidence, bottom.letter, depth, bottom.offset
    )

    var defect = _prefix_defect(pair, top.index, bottom.index)
    var source_index_delta = top.index - bottom.index
    if defect.x + defect.y + defect.z != source_index_delta:
        raise Error("renewal-address source displacement/defect identity failed")

    var scaled = _matrix_apply_n(incidence, defect, depth)
    var correction = _sub(top_side.prefix, bottom_side.prefix)
    var closure = _add(scaled, correction)
    if not closure.is_zero():
        raise Error("renewal-address cut is not a zero return")

    return RelativeRenewalAddress(
        depth,
        source_index_delta,
        defect,
        top.letter,
        bottom.letter,
        top_side.digits,
        bottom_side.digits,
        scaled,
        correction,
    )
