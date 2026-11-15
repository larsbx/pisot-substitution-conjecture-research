"""Bounded complete matrix-adic quotients and literal block support profiles.

The quotient is Z^3 / M^q Z^3, with COLUMN lattice generators.  A deterministic
basis traversal records representatives, exact adjugate class keys, every
addition, and the actual reduction and induced incidence maps.  Every literal
position in every inflated source is retained before support is deduplicated.

This is finite algebra and address authentication.  A compact tile enclosure
still needs the supplied literal block tile equation and the Lean carrier
bridge.  Neither a finite compatible list nor a finite profile authenticates
an infinite coherent state, a Pisot tile, or compact overlap measure.

All bounds refuse the whole construction.  In particular the traversal must
process EVERY basis extension, including those after index-many classes have
already been found.  The pre-code gate is
docs/c4-madic-residue-literature-2026-11-11.md.
"""

from std.collections import Dict
from finite_exact.bigint_z import bigz_eq, bigz_from_i64
from finite_exact.checked_int import checked_abs, checked_add, checked_mul
from finite_linear_algebra.integer_matrix import matmul
from finite_linear_algebra.integer_vector import add, sub, matvec
from finite_linear_algebra.madic_ball import quotient_invariants
from finite_linear_algebra.mat3 import Mat3, identity3
from psc.c4_nonunit_residue_occupancy import checked_substitution, named_substitution, same_vector

comptime MADIC_DEPTH_CAP = 6
comptime MADIC_INDEX_CAP = 64
comptime MADIC_CANDIDATE_CAP = 192
comptime MADIC_WORD_CAP = 729
comptime MADIC_OCCURRENCE_CAP = 2187


struct ResidueLevel(Copyable, Movable):
    var depth: Int
    var index: Int
    var determinant: Int
    var candidates: Int
    var matrix: Mat3
    var adjugate: Mat3
    var smith: List[Int]
    # [representative3, exactKey3, birthParent, birthAxis]
    var representatives: List[List[Int]]
    var addition: List[List[Int]]
    var generators: List[Int]
    var inverse: List[Int]
    var orders: List[Int]
    var action: List[Int]
    # At q=0 this is the identity on the singleton.  Otherwise Q_q -> Q_(q-1).
    var reduction: List[Int]
    var words: List[List[Int]]
    # [source,position,selected,prefix3,suffix3,classId].  Together with the
    # complete source word, source/position determines literal prefix/suffix.
    var occurrences: List[List[Int]]
    # All [letter,classId,countSource0,countSource1,countSource2], even zeros.
    var counts: List[List[Int]]
    var profiles: List[List[Int]]

    def __init__(out self, depth: Int, power: Mat3) raises:
        if depth < 0 or depth > MADIC_DEPTH_CAP or len(power.e) != 9:
            raise Error("matrix-adic level constructor shape or depth")
        for entry in power.e:
            if entry < 0 or entry > MADIC_WORD_CAP:
                raise Error("matrix-adic level constructor arithmetic bound")
        self.depth = depth
        self.matrix = power.copy()
        self.adjugate = power.adjugate()
        self.determinant = power.det()
        self.index = checked_abs(self.determinant)
        self.candidates = 0
        self.smith = List[Int]()
        self.representatives = List[List[Int]]()
        self.addition = List[List[Int]]()
        self.generators = List[Int]()
        self.inverse = List[Int]()
        self.orders = List[Int]()
        self.action = List[Int]()
        self.reduction = List[Int]()
        self.words = List[List[Int]]()
        self.occurrences = List[List[Int]]()
        self.counts = List[List[Int]]()
        self.profiles = List[List[Int]]()


struct MadicResidue(Copyable, Movable):
    var images: List[List[Int]]
    var depth: Int
    var determinant: Int
    var matrix: Mat3
    var index_cap: Int
    var candidate_cap: Int
    var word_cap: Int
    var occurrence_cap: Int
    var levels: List[ResidueLevel]

    def __init__(out self, images: List[List[Int]], depth: Int, matrix: Mat3,
            index_cap: Int, candidate_cap: Int, word_cap: Int, occurrence_cap: Int,
            levels: List[ResidueLevel]):
        self.images = images.copy()
        self.depth = depth
        self.matrix = matrix.copy()
        self.determinant = matrix.det()
        self.index_cap = index_cap
        self.candidate_cap = candidate_cap
        self.word_cap = word_cap
        self.occurrence_cap = occurrence_cap
        self.levels = levels.copy()


def _rows(matrix: Mat3) raises -> List[List[Int]]:
    if len(matrix.e) != 9:
        raise Error("matrix-adic matrix must have nine row-major entries")
    return [[matrix.e[0],matrix.e[1],matrix.e[2]],
            [matrix.e[3],matrix.e[4],matrix.e[5]],
            [matrix.e[6],matrix.e[7],matrix.e[8]]]


def _triple(row: List[Int], start: Int) -> List[Int]:
    return [row[start],row[start+1],row[start+2]]


def _normalized_key(adjugate_rows: List[List[Int]], index: Int, vector: List[Int]) raises -> List[Int]:
    if index < 1 or index > MADIC_INDEX_CAP or len(vector) != 3:
        raise Error("matrix-adic key index or vector shape outside bounded domain")
    # The vendored matvec checks every multiplication and addition before
    # normalization.  Public callers cannot overflow by supplying a huge v.
    var key = matvec(adjugate_rows,vector)
    for axis in range(3):
        key[axis] = key[axis]%index
        if key[axis] < 0:
            key[axis] += index
    return key^


def _packed_key(key: List[Int], index: Int) raises -> Int:
    if len(key) != 3 or index < 1 or index > MADIC_INDEX_CAP:
        raise Error("matrix-adic packed key shape")
    for axis in range(3):
        if key[axis] < 0 or key[axis] >= index:
            raise Error("matrix-adic key is not normalized")
    # At most 64^3-1, after the preceding guards.
    return key[0]+index*(key[1]+index*key[2])


def residue_class(level: ResidueLevel, vector: List[Int]) raises -> Int:
    """Class of an integer vector in a constructed or separately verified level."""
    var key = _normalized_key(_rows(level.adjugate),level.index,vector)
    var packed = _packed_key(key,level.index)
    if len(level.representatives) != level.index:
        raise Error("matrix-adic lookup requires the full representative inventory")
    for identity in range(level.index):
        if len(level.representatives[identity]) != 8:
            raise Error("matrix-adic representative shape")
        if _packed_key(_triple(level.representatives[identity],3),level.index) == packed:
            return identity
    raise Error("integer vector class missing from complete matrix-adic quotient")


def _small_smith(matrix: Mat3, depth: Int, index: Int) raises -> List[Int]:
    # Consume the vendored exact-Q determinantal-divisor implementation.
    # Its BigZ answers must belong to 1..index, which is already capped.
    var actual = quotient_invariants(matrix.e,3,depth)
    if len(actual) != 3:
        raise Error("matrix-adic Smith dimension")
    var result = List[Int]()
    var product = 1
    for axis in range(3):
        var found = 0
        for candidate in range(1,index+1):
            if bigz_eq(actual[axis],bigz_from_i64(Int64(candidate))):
                found = candidate
                break
        if found == 0:
            raise Error("matrix-adic Smith factor outside bounded quotient")
        if axis > 0 and found%result[axis-1] != 0:
            raise Error("matrix-adic Smith factors fail divisibility")
        result.append(found)
        product = checked_mul(product,found)
    if product != index:
        raise Error("matrix-adic Smith factors fail full index identity")
    return result^


def _quotient_level(matrix: Mat3, power: Mat3, depth: Int,
        index_cap: Int, candidate_cap: Int) raises -> ResidueLevel:
    # These guards justify the bounded Mat3 determinant and adjugate calls:
    # all entries <=729, every cofactor <=2*729^2 and |det|<=6*729^3.
    if len(power.e) != 9:
        raise Error("matrix-adic power shape")
    for entry in power.e:
        if entry < 0 or entry > MADIC_WORD_CAP:
            raise Error("matrix-adic power outside proven arithmetic bound")
    var level = ResidueLevel(depth,power)
    if level.index < 1 or level.index > index_cap:
        raise Error("complete quotient index exceeds budget or is singular")
    var adjugate_rows = _rows(level.adjugate)
    var identities = Dict[Int,Int]()
    identities[0] = 0
    level.representatives.append([0,0,0,0,0,0,-1,-1])
    var cursor = 0
    while cursor < len(level.representatives):
        for axis in range(3):
            if level.candidates >= candidate_cap:
                raise Error("complete quotient basis-extension budget exhausted")
            level.candidates += 1
            var representative = _triple(level.representatives[cursor],0)
            representative[axis] = checked_add(representative[axis],1)
            var key = _normalized_key(adjugate_rows,level.index,representative)
            var packed = _packed_key(key,level.index)
            if packed not in identities:
                if len(level.representatives) >= level.index or len(level.representatives) >= index_cap:
                    raise Error("quotient traversal disagrees with exact index or exceeds budget")
                identities[packed] = len(level.representatives)
                level.representatives.append([representative[0],representative[1],representative[2],
                    key[0],key[1],key[2],cursor,axis])
        cursor += 1
    if len(level.representatives) != level.index or level.candidates != 3*level.index:
        raise Error("basis traversal did not certify the entire quotient")
    level.smith = _small_smith(matrix,depth,level.index)
    for axis in range(3):
        var unit: List[Int] = [0,0,0]
        unit[axis] = 1
        var packed = _packed_key(_normalized_key(adjugate_rows,level.index,unit),level.index)
        if packed not in identities:
            raise Error("quotient basis generator missing")
        level.generators.append(identities[packed])
    var matrix_rows = _rows(matrix)
    for first in range(level.index):
        var row = List[Int]()
        var first_rep = _triple(level.representatives[first],0)
        for second in range(level.index):
            var sum_rep = add(first_rep,_triple(level.representatives[second],0))
            var packed = _packed_key(_normalized_key(adjugate_rows,level.index,sum_rep),level.index)
            if packed not in identities:
                raise Error("complete quotient is not closed under addition")
            row.append(identities[packed])
        level.addition.append(row^)
        var negative = sub([0,0,0],first_rep)
        var neg_key = _packed_key(_normalized_key(adjugate_rows,level.index,negative),level.index)
        if neg_key not in identities:
            raise Error("complete quotient is not closed under inverses")
        level.inverse.append(identities[neg_key])
        var image = matvec(matrix_rows,first_rep)
        var image_key = _packed_key(_normalized_key(adjugate_rows,level.index,image),level.index)
        if image_key not in identities:
            raise Error("induced incidence action escapes quotient")
        level.action.append(identities[image_key])
        level.reduction.append(0)
    for identity in range(level.index):
        var value = 0
        var order = 0
        for count in range(1,level.index+1):
            value = level.addition[value][identity]
            if value == 0:
                order = count
                break
        if order == 0 or level.addition[identity][level.inverse[identity]] != 0:
            raise Error("finite quotient order or inverse identity failed")
        level.orders.append(order)
        value = identity
        for _ in range(depth):
            value = level.action[value]
        if value != 0:
            raise Error("level-q incidence action must have q-th power zero")
        for other in range(level.index):
            if level.addition[identity][other] != level.addition[other][identity]:
                raise Error("finite quotient addition is not commutative")
            if level.action[level.addition[identity][other]] != level.addition[level.action[identity]][level.action[other]]:
                raise Error("induced incidence action is not additive")
    return level^


def _attach_occurrences(mut level: ResidueLevel, words: List[List[Int]], occurrence_cap: Int) raises:
    level.words = words.copy()
    for letter in range(3):
        for identity in range(level.index):
            level.counts.append([letter,identity,0,0,0])
    for source in range(3):
        var total: List[Int] = [0,0,0]
        for selected in words[source]:
            total[selected] += 1
        for selected in range(3):
            if total[selected] != level.matrix.at(selected,source):
                raise Error("literal block word disagrees with incidence power")
        var prefix: List[Int] = [0,0,0]
        for position in range(len(words[source])):
            if len(level.occurrences) >= occurrence_cap:
                raise Error("complete literal occurrence budget exhausted")
            var selected = words[source][position]
            var suffix = sub(total,prefix)
            suffix[selected] -= 1
            var identity = residue_class(level,prefix)
            level.occurrences.append([source,position,selected,prefix[0],prefix[1],prefix[2],
                suffix[0],suffix[1],suffix[2],identity])
            level.counts[selected*level.index+identity][source+2] += 1
            prefix[selected] += 1
    for letter in range(3):
        var support = List[Int]()
        for identity in range(level.index):
            var row = level.counts[letter*level.index+identity].copy()
            if row[2]+row[3]+row[4] > 0:
                support.append(identity)
        level.profiles.append(support^)


def build_madic_residue(images: List[List[Int]], depth: Int,
        index_cap: Int = MADIC_INDEX_CAP, candidate_cap: Int = MADIC_CANDIDATE_CAP,
        word_cap: Int = MADIC_WORD_CAP, occurrence_cap: Int = MADIC_OCCURRENCE_CAP) raises -> MadicResidue:
    if depth < 0 or depth > MADIC_DEPTH_CAP:
        raise Error("matrix-adic depth outside bounded domain 0..6")
    if index_cap < 1 or index_cap > MADIC_INDEX_CAP or candidate_cap < 1 or candidate_cap > MADIC_CANDIDATE_CAP:
        raise Error("matrix-adic quotient or candidate budget outside supported domain")
    if word_cap < 1 or word_cap > MADIC_WORD_CAP or occurrence_cap < 1 or occurrence_cap > MADIC_OCCURRENCE_CAP:
        raise Error("matrix-adic word or occurrence budget outside supported domain")
    var sigma = checked_substitution(images)
    var matrix = Mat3(sigma.incidence())
    if matrix.det() == 0:
        raise Error("singular incidence has no certified finite quotient in this constructor")
    var determinant = checked_abs(matrix.det())
    var levels = List[ResidueLevel]()
    var power = identity3()
    var words: List[List[Int]] = [[0],[1],[2]]
    var expected_index = 1
    for q in range(depth+1):
        if expected_index > index_cap:
            raise Error("complete quotient index exceeds budget")
        var level = _quotient_level(matrix,power,q,index_cap,candidate_cap)
        if level.index != expected_index:
            raise Error("incidence power determinant disagrees with quotient index")
        if q > 0:
            var previous = levels[q-1].copy()
            var fiber_sizes = List[Int](length=previous.index,fill=0)
            for identity in range(level.index):
                var reduced = residue_class(previous,_triple(level.representatives[identity],0))
                level.reduction[identity] = reduced
                fiber_sizes[reduced] += 1
                if residue_class(previous,matvec(_rows(matrix),_triple(level.representatives[identity],0))) != previous.action[reduced]:
                    raise Error("reduction does not commute with incidence action")
            for identity in range(level.index):
                if level.reduction[level.action[identity]] != previous.action[level.reduction[identity]]:
                    raise Error("actual reduction and action tables fail commutation")
                for other in range(level.index):
                    if level.reduction[level.addition[identity][other]] != previous.addition[level.reduction[identity]][level.reduction[other]]:
                        raise Error("actual reduction table is not additive")
            for size in fiber_sizes:
                if size != determinant:
                    raise Error("quotient reduction is not the complete uniform-fiber map")
        _attach_occurrences(level,words,occurrence_cap)
        levels.append(level^)
        if q < depth:
            # Refuse before materializing an oversized word; no prefix sample
            # is ever substituted for the complete requested block word.
            var next_words = List[List[Int]]()
            for source in range(3):
                var length = 0
                for selected in words[source]:
                    if len(images[selected]) > word_cap-length:
                        raise Error("complete block word exceeds budget")
                    length += len(images[selected])
                next_words.append(sigma.apply(words[source]))
            words = next_words^
            power = Mat3(matmul(power.e,matrix.e,3))
            expected_index = checked_mul(expected_index,determinant)
    return MadicResidue(images,depth,matrix,index_cap,candidate_cap,word_cap,occurrence_cap,levels)


def _same_rows(first: List[List[Int]], second: List[List[Int]]) -> Bool:
    if len(first) != len(second):
        return False
    for row in range(len(first)):
        if not same_vector(first[row],second[row]):
            return False
    return True


def verify_madic_residue(certificate: MadicResidue) raises:
    """Reconstruct every field; conservation alone never authenticates addresses."""
    var expected = build_madic_residue(certificate.images,certificate.depth,
        certificate.index_cap,certificate.candidate_cap,certificate.word_cap,certificate.occurrence_cap)
    if certificate.determinant != expected.determinant or not same_vector(certificate.matrix.e,expected.matrix.e):
        raise Error("matrix-adic certificate incidence metadata changed")
    if len(certificate.levels) != len(expected.levels):
        raise Error("matrix-adic certificate omitted or repeated a level")
    for q in range(len(expected.levels)):
        var actual = certificate.levels[q].copy()
        var canonical = expected.levels[q].copy()
        if actual.depth != q or actual.index != canonical.index or actual.determinant != canonical.determinant or actual.candidates != canonical.candidates:
            raise Error("matrix-adic level metadata changed")
        if not same_vector(actual.matrix.e,canonical.matrix.e) or not same_vector(actual.adjugate.e,canonical.adjugate.e):
            raise Error("matrix-adic level lattice changed")
        if not same_vector(actual.smith,canonical.smith) or not _same_rows(actual.representatives,canonical.representatives):
            raise Error("matrix-adic exact quotient representatives changed")
        if not _same_rows(actual.addition,canonical.addition) or not same_vector(actual.inverse,canonical.inverse) or not same_vector(actual.orders,canonical.orders):
            raise Error("matrix-adic full group operation changed")
        if not same_vector(actual.generators,canonical.generators) or not same_vector(actual.action,canonical.action) or not same_vector(actual.reduction,canonical.reduction):
            raise Error("matrix-adic basis, action or reduction map changed")
        if not _same_rows(actual.words,canonical.words) or not _same_rows(actual.occurrences,canonical.occurrences):
            raise Error("matrix-adic complete literal occurrence inventory changed")
        if not _same_rows(actual.counts,canonical.counts) or not _same_rows(actual.profiles,canonical.profiles):
            raise Error("matrix-adic complete support or multiplicity changed")


def residue_summary(level: ResidueLevel) raises -> List[Int]:
    var support = 0
    for profile in level.profiles:
        support += len(profile)
    var occupied_buckets = 0
    for row in level.counts:
        for source in range(3):
            if row[source+2] > 0:
                occupied_buckets += 1
    var kernel = 0
    var image = Dict[Int,Int]()
    for value in level.action:
        if value == 0:
            kernel += 1
        image[value] = 1
    return [level.index,level.candidates,len(level.occurrences),support,
        kernel,len(image),len(level.occurrences)-occupied_buckets]


def profile_intersection(level: ResidueLevel, first: Int, second: Int, shift: List[Int]) raises -> List[Int]:
    """C_first intersect ([shift]+C_second), on a constructed/verified level.

    Empty is a finite exclusion premise.  Nonempty asserts no compact overlap.
    """
    if first < 0 or first >= 3 or second < 0 or second >= 3 or len(level.profiles) != 3:
        raise Error("matrix-adic profile query letter or shape")
    var delta = residue_class(level,shift)
    var translated = Dict[Int,Int]()
    for identity in level.profiles[second]:
        if identity < 0 or identity >= level.index:
            raise Error("matrix-adic profile class outside quotient")
        translated[level.addition[delta][identity]] = 1
    var result = List[Int]()
    for identity in level.profiles[first]:
        if identity < 0 or identity >= level.index:
            raise Error("matrix-adic profile class outside quotient")
        if identity in translated:
            result.append(identity)
    return result^


def residue_fixture_images(fixture: Int) raises -> List[List[Int]]:
    if fixture == 0 or fixture == 1:
        var images = named_substitution()
        if fixture == 1:
            images[1] = [0,1,2]
        return images^
    if fixture == 2:
        return [[0,1],[0,2],[0]]
    if fixture == 3:
        return [[0,0],[1,1],[2,2]]
    raise Error("unknown matrix-adic residue fixture")


def residue_fixture(fixture: Int) raises -> MadicResidue:
    var depth = 4 if fixture < 2 else (3 if fixture == 2 else 2)
    return build_madic_residue(residue_fixture_images(fixture),depth)


def residue_refusal(control: Int) raises:
    """Replay one failed stronger construction; successful completion is error."""
    var refused = False
    try:
        if control == 0:
            _ = build_madic_residue([[0],[0],[0]],0)
        elif control == 1:
            _ = build_madic_residue([[0],[0],[0]],1)
        elif control == 2:
            _ = build_madic_residue(residue_fixture_images(3),3)
        elif control == 3:
            _ = build_madic_residue(named_substitution(),2,candidate_cap=11)
        elif control == 4:
            _ = build_madic_residue(named_substitution(),2,word_cap=2)
        elif control == 5:
            _ = build_madic_residue(named_substitution(),2,occurrence_cap=14)
        elif control == 6:
            _ = build_madic_residue(named_substitution(),7)
        elif control == 7:
            _ = build_madic_residue(named_substitution(),6,index_cap=63)
        else:
            raise Error("unknown matrix-adic refusal control")
    except:
        refused = True
    if control < 0 or control > 7 or not refused:
        raise Error("matrix-adic negative construction did not refuse")
