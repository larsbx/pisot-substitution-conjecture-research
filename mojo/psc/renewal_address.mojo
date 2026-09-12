"""Level-scaled symbolic renewal addresses for the G1b-2 program.

This module augments the labelled first-return representation with exact
substitution ancestry for an interior zero-return cut of sigma^depth(pair).
It deliberately stays in integer/symbolic coordinates. No inverse incidence
matrix, Euclidean stable projection, lattice assumption, or unit determinant is
used.

For a selected zero-return cut, desubstitution gives a prefix defect delta at
the source level plus two finite substitution-digit paths. Their partial-image
correction c satisfies the exact certificate

    M^depth delta + c = 0.

The record stores only the *relative* source-index displacement, source defect,
source letters, and digit paths. Absolute source indices and inflated word
length are not part of the address. The address is auxiliary data and must be
retained together with the labelled return word: distinct labelled returns can
share the same relative address.

Inflated words are never materialized. `RenewalAddressTables` precomputes all
three image lengths and image Parikh columns for levels `0..depth` in O(depth)
once. A census can reuse that table across every cut at the same substitution
and depth; each address then performs only the linear symbolic digit descent.
"""

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


struct RenewalAddressTables(Copyable, Movable):
    """Reusable substitution-local tables through one requested depth.

    `lengths[3*level+a] = |sigma^level(a)|`.
    `parikhs[9*level+3*a+i]` is coordinate `i` of
    `Parikh(sigma^level(a))`, equivalently column `a` of `M^level`.

    The ordered substitution itself is retained because digit descent depends
    on child order, not merely on the incidence matrix.
    """

    var sigma: List[List[Int]]
    var depth: Int
    var lengths: List[Int]
    var parikhs: List[Int]

    def __init__(
        out self,
        sigma: List[List[Int]],
        depth: Int,
        lengths: List[Int],
        parikhs: List[Int],
    ):
        self.sigma = sigma.copy()
        self.depth = depth
        self.lengths = lengths.copy()
        self.parikhs = parikhs.copy()

    def image_length(self, level: Int, letter: Int) raises -> Int:
        if level < 0 or level > self.depth:
            raise Error("renewal-address table level lies outside 0..depth")
        if letter < 0 or letter >= 3:
            raise Error("renewal-address table letter lies outside 0..2")
        return self.lengths[3 * level + letter]

    def image_parikh(self, level: Int, letter: Int) raises -> Diff3:
        if level < 0 or level > self.depth:
            raise Error("renewal-address table level lies outside 0..depth")
        if letter < 0 or letter >= 3:
            raise Error("renewal-address table letter lies outside 0..2")
        var k = 9 * level + 3 * letter
        return Diff3(self.parikhs[k], self.parikhs[k + 1], self.parikhs[k + 2])


struct RelativeRenewalAddress(Copyable, Movable):
    """Relative symbolic address of one inflated interior renewal cut.

    `top_digits` and `bottom_digits` are flat `(parent_letter, child_index)`
    pairs, one pair per substitution level. Child letters are determined by
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


def _add(a: Diff3, b: Diff3) -> Diff3:
    return Diff3(a.x + b.x, a.y + b.y, a.z + b.z)


def _sub(a: Diff3, b: Diff3) -> Diff3:
    return Diff3(a.x - b.x, a.y - b.y, a.z - b.z)


def build_renewal_address_tables(
    sigma: List[List[Int]], depth: Int
) raises -> RenewalAddressTables:
    """Precompute image lengths and Parikh columns once for `0..depth`."""
    _validate_sigma(sigma)
    if depth < 0:
        raise Error("renewal-address depth must be nonnegative")

    var current_lengths: List[Int] = [1, 1, 1]
    var current_parikhs: List[Int] = [1, 0, 0, 0, 1, 0, 0, 0, 1]
    var all_lengths = current_lengths.copy()
    var all_parikhs = current_parikhs.copy()

    for _ in range(depth):
        var next_lengths: List[Int] = [0, 0, 0]
        var next_parikhs: List[Int] = [0, 0, 0, 0, 0, 0, 0, 0, 0]
        for a in range(3):
            for j in range(len(sigma[a])):
                var child = sigma[a][j]
                next_lengths[a] += current_lengths[child]
                next_parikhs[3 * a] += current_parikhs[3 * child]
                next_parikhs[3 * a + 1] += current_parikhs[3 * child + 1]
                next_parikhs[3 * a + 2] += current_parikhs[3 * child + 2]
        for a in range(3):
            all_lengths.append(next_lengths[a])
        for k in range(9):
            all_parikhs.append(next_parikhs[k])
        current_lengths = next_lengths^
        current_parikhs = next_parikhs^

    return RenewalAddressTables(sigma, depth, all_lengths, all_parikhs)


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


def _word_image_length(word: List[Int], tables: RenewalAddressTables) raises -> Int:
    var total = 0
    for i in range(len(word)):
        var a = word[i]
        if a < 0 or a >= 3:
            raise Error("renewal-address word letter lies outside 0..2")
        total += tables.image_length(tables.depth, a)
    return total


def _locate_source(
    word: List[Int], cut: Int, tables: RenewalAddressTables
) raises -> _SourceLocation:
    var total = _word_image_length(word, tables)
    if cut < 0 or cut >= total:
        raise Error("renewal-address cut must select a source supertile")

    var cursor = 0
    for i in range(len(word)):
        var a = word[i]
        var next = cursor + tables.image_length(tables.depth, a)
        if cut < next:
            return _SourceLocation(i, a, cut - cursor)
        cursor = next
    raise Error("renewal-address source location was not found")


def _prefix_inside_source_letter(
    tables: RenewalAddressTables,
    source_letter: Int,
    offset: Int,
) raises -> _SideAddress:
    """Descend one cut through sigma^depth(source_letter) using cached tables."""
    if tables.depth <= 0:
        raise Error("renewal-address symbolic path requires positive depth")
    if offset < 0 or offset >= tables.image_length(tables.depth, source_letter):
        raise Error("renewal-address within-supertile offset is out of range")

    var digits = List[Int]()
    var prefix = Diff3(0, 0, 0)
    var current_letter = source_letter
    var residual = offset
    var level = tables.depth

    while level > 0:
        var child_start = 0
        var found = False
        for j in range(len(tables.sigma[current_letter])):
            var child = tables.sigma[current_letter][j]
            var block_length = tables.image_length(level - 1, child)
            if residual < child_start + block_length:
                digits.append(current_letter)
                digits.append(j)
                residual -= child_start
                current_letter = child
                found = True
                break
            prefix = _add(prefix, tables.image_parikh(level - 1, child))
            child_start += block_length
        if not found:
            raise Error("renewal-address digit descent failed to select a child")
        level -= 1

    if residual != 0:
        raise Error("renewal-address leaf residual must vanish")
    return _SideAddress(digits, prefix)


def _scale_defect(tables: RenewalAddressTables, defect: Diff3) raises -> Diff3:
    var c0 = tables.image_parikh(tables.depth, 0)
    var c1 = tables.image_parikh(tables.depth, 1)
    var c2 = tables.image_parikh(tables.depth, 2)
    return Diff3(
        defect.x * c0.x + defect.y * c1.x + defect.z * c2.x,
        defect.x * c0.y + defect.y * c1.y + defect.z * c2.y,
        defect.x * c0.z + defect.y * c1.z + defect.z * c2.z,
    )


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


def renewal_cut_address_with_tables(
    tables: RenewalAddressTables, pair: Pair, cut: Int
) raises -> RelativeRenewalAddress:
    """Address one cut using reusable substitution/depth tables.

    A joint-address census should build `RenewalAddressTables` once and call
    this function for every candidate cut at the same depth.
    """
    if tables.depth <= 0:
        raise Error("renewal-address depth must be positive")

    var checked = strict_first_return_word(pair)
    if not checked.first_return:
        raise Error("renewal-address source pair is not a first return")

    var top_length = _word_image_length(pair.u, tables)
    var bottom_length = _word_image_length(pair.v, tables)
    if top_length != bottom_length:
        raise Error("balanced renewal pair has unequal inflated side lengths")
    if cut <= 0 or cut >= top_length:
        raise Error("renewal-address cut must be interior")

    var top = _locate_source(pair.u, cut, tables)
    var bottom = _locate_source(pair.v, cut, tables)
    var top_side = _prefix_inside_source_letter(tables, top.letter, top.offset)
    var bottom_side = _prefix_inside_source_letter(tables, bottom.letter, bottom.offset)

    var defect = _prefix_defect(pair, top.index, bottom.index)
    var source_index_delta = top.index - bottom.index
    if defect.x + defect.y + defect.z != source_index_delta:
        raise Error("renewal-address source displacement/defect identity failed")

    var scaled = _scale_defect(tables, defect)
    var correction = _sub(top_side.prefix, bottom_side.prefix)
    var closure = _add(scaled, correction)
    if not closure.is_zero():
        raise Error("renewal-address cut is not a zero return")

    return RelativeRenewalAddress(
        tables.depth,
        source_index_delta,
        defect,
        top.letter,
        bottom.letter,
        top_side.digits,
        bottom_side.digits,
        scaled,
        correction,
    )


def renewal_cut_address(
    sigma: List[List[Int]], pair: Pair, depth: Int, cut: Int
) raises -> RelativeRenewalAddress:
    """Convenience wrapper for one address; batch callers should reuse tables."""
    var tables = build_renewal_address_tables(sigma, depth)
    return renewal_cut_address_with_tables(tables, pair, cut)
