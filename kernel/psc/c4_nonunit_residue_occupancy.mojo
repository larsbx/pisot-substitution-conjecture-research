"""Bounded exact residue counts and the named 1/021/001 certificate.

The finite table records actual strict prefixes, not coordinate residues.  The
measure implication is the separate literature-gated argument in docs/.  This
module checks finite identities only; it does not certify a tiling theorem.
"""

from finite_exact.closed_interval import IQ
from finite_exact.rat_q import Q
from finite_linear_algebra.mat3 import Mat3, identity3
from finite_linear_algebra.qpoly import add, mul, remainder, scale, sub
from finite_linear_algebra.scalar import q_int
from substitution_dynamics.substitution import Substitution
from psc.exact import eval_int_poly_at_q, q_poly, require_iq, require_q

comptime MAX_DEPTH = 6
comptime MAX_IMAGE_LENGTH = 3
comptime DEFAULT_WORD_CAP = 100000
comptime DEFAULT_ROW_CAP = 2187


struct ResidueRow(Copyable, Movable):
    var letter: Int
    var key: List[Int]
    var counts: List[Int]

    def __init__(out self, letter: Int, key: List[Int]):
        self.letter = letter
        self.key = key.copy()
        self.counts = [0, 0, 0]


struct ResidueTable(Copyable, Movable):
    var depth: Int
    var index: Int
    var matrix: Mat3
    var adjugate: Mat3
    var words: List[List[Int]]
    var rows: List[ResidueRow]

    def __init__(out self, depth: Int, index: Int, matrix: Mat3, adjugate: Mat3, words: List[List[Int]], rows: List[ResidueRow]):
        self.depth = depth
        self.index = index
        self.matrix = matrix.copy()
        self.adjugate = adjugate.copy()
        self.words = words.copy()
        self.rows = rows.copy()


def named_substitution() -> List[List[Int]]:
    var result = List[List[Int]]()
    result.append([1])
    result.append([0, 2, 1])
    result.append([0, 0, 1])
    return result^


def checked_substitution(images: List[List[Int]]) raises -> Substitution:
    if len(images) != 3:
        raise Error("residue occupancy requires exactly three letters")
    for i in range(3):
        if len(images[i]) < 1 or len(images[i]) > MAX_IMAGE_LENGTH:
            raise Error("image length outside supported range 1..3")
    return Substitution.checked(images)


def same_vector(a: List[Int], b: List[Int]) -> Bool:
    if len(a) != len(b):
        return False
    for i in range(len(a)):
        if a[i] != b[i]:
            return False
    return True


def residue_key(adjugate: Mat3, index: Int, prefix: List[Int]) raises -> List[Int]:
    # Public primitive is bounded as well as the constructor.  Valid table
    # entries satisfy |adj| <= 2*729^2 and prefix coordinate <= 729.  Thus
    # each dot product is <= 6*729^3, far below the signed 64-bit bound.
    if index < 1 or index > 2324522934 or len(prefix) != 3 or len(adjugate.e) != 9:
        raise Error("invalid bounded residue-key input")
    for i in range(3):
        if prefix[i] < 0 or prefix[i] > 729:
            raise Error("prefix outside bounded residue-key domain")
    for i in range(3):
        for j in range(3):
            if adjugate.at(i, j) < -1062882 or adjugate.at(i, j) > 1062882:
                raise Error("adjugate outside bounded residue-key domain")
    var result = adjugate.apply(prefix)
    for i in range(3):
        result[i] = result[i] % index
        if result[i] < 0:
            result[i] += index
    return result^


def find_row(table: ResidueTable, letter: Int, key: List[Int]) -> Int:
    for i in range(len(table.rows)):
        if table.rows[i].letter == letter and same_vector(table.rows[i].key, key):
            return i
    return -1


def inflated_words(images: List[List[Int]], depth: Int, word_cap: Int = DEFAULT_WORD_CAP) raises -> List[List[Int]]:
    if depth < 0 or depth > MAX_DEPTH or word_cap < 1 or word_cap > DEFAULT_WORD_CAP:
        raise Error("inflation depth or word cap outside supported domain")
    var sigma = checked_substitution(images)
    var result = List[List[Int]]()
    for source in range(3):
        var word: List[Int] = [source]
        for _ in range(depth):
            var next_length = 0
            for k in range(len(word)):
                if len(sigma.images[word[k]]) > word_cap - next_length:
                    raise Error("word cap exceeded before inflation")
                next_length += len(sigma.images[word[k]])
            word = sigma.apply(word)
        result.append(word^)
    return result^


def verify_conservation(table: ResidueTable) raises:
    # Validate mutable record shapes and bounds before indexing or summation.
    if table.depth < 0 or table.depth > MAX_DEPTH or table.index < 1 or table.index > 2324522934:
        raise Error("invalid bounded residue table metadata")
    if len(table.matrix.e) != 9 or len(table.adjugate.e) != 9 or len(table.words) != 3 or len(table.rows) > DEFAULT_ROW_CAP:
        raise Error("invalid residue table shape")
    for source in range(3):
        if len(table.words[source]) < 1 or len(table.words[source]) > 729:
            raise Error("invalid bounded table word length")
    for i in range(len(table.rows)):
        var row = table.rows[i].copy()
        if row.letter < 0 or row.letter >= 3 or len(row.key) != 3 or len(row.counts) != 3:
            raise Error("invalid residue row shape")
        for source in range(3):
            if row.counts[source] < 0 or row.counts[source] > 729 or row.key[source] < 0 or row.key[source] >= table.index:
                raise Error("invalid bounded residue row")
    var totals: List[Int] = [0, 0, 0, 0, 0, 0, 0, 0, 0]
    for i in range(len(table.rows)):
        var row = table.rows[i].copy()
        for source in range(3):
            totals[3 * row.letter + source] += row.counts[source]
    for letter in range(3):
        for source in range(3):
            if totals[3 * letter + source] != table.matrix.at(letter, source):
                raise Error("residue counts fail incidence conservation")
    for source in range(3):
        var total = 0
        for letter in range(3):
            total += totals[3 * letter + source]
        if total != len(table.words[source]):
            raise Error("residue counts fail source length conservation")


def build_residue_table(images: List[List[Int]], depth: Int, word_cap: Int = DEFAULT_WORD_CAP, row_cap: Int = DEFAULT_ROW_CAP) raises -> ResidueTable:
    if depth < 0 or depth > MAX_DEPTH:
        raise Error("residue depth outside supported domain 0..6")
    if row_cap < 1 or row_cap > DEFAULT_ROW_CAP:
        raise Error("residue row cap outside supported domain")
    var sigma = checked_substitution(images)
    var matrix = Mat3(sigma.incidence())
    if matrix.det() == 0:
        raise Error("singular substitutions have no finite-index residue table")
    # All bounds precede matrix products.  With images <=3 and depth <=6,
    # matrix entries <=729, adjugate entries <=2*729^2, determinant <=6*729^3.
    var power = identity3()
    for _ in range(depth):
        power = power * matrix
    var index = power.det()
    if index < 0:
        index = -index
    var adjugate = power.adjugate()
    var words = inflated_words(images, depth, word_cap)
    var rows = List[ResidueRow]()
    for source in range(3):
        var prefix: List[Int] = [0, 0, 0]
        for position in range(len(words[source])):
            var letter = words[source][position]
            var key = residue_key(adjugate, index, prefix)
            var found = -1
            for i in range(len(rows)):
                if rows[i].letter == letter and same_vector(rows[i].key, key):
                    found = i
                    break
            if found < 0:
                if len(rows) >= row_cap:
                    raise Error("residue row cap exceeded before append")
                rows.append(ResidueRow(letter, key))
                found = len(rows) - 1
            rows[found].counts[source] += 1
            prefix[letter] += 1
    var table = ResidueTable(depth, index, power, adjugate, words, rows)
    verify_conservation(table)
    return table^


def require_zero_mod_chi(polynomial: List[Q]) raises:
    var reduced = remainder(polynomial, q_poly([-2, -2, -1, 1]))
    for i in range(len(reduced)):
        if reduced[i].rejected or not reduced[i].eq(Q.zero()):
            raise Error("named polynomial identity failed")


struct NamedCertificate(Copyable, Movable):
    var beta: IQ
    var interval_upper_bounds: List[Q]
    var exact_third_upper: Q

    def __init__(out self, beta: IQ, upper: List[Q]):
        self.beta = beta.copy()
        self.interval_upper_bounds = upper.copy()
        self.exact_third_upper = Q(1, 4)


def certify_named_depth_two(table: ResidueTable) raises -> NamedCertificate:
    var canonical = build_residue_table(named_substitution(), 2)
    verify_conservation(table)
    if table.depth != 2 or table.index != 4 or len(table.words) != 3:
        raise Error("named certificate requires depth two and index four")
    if not same_vector(table.matrix.e, canonical.matrix.e) or not same_vector(table.adjugate.e, canonical.adjugate.e) or len(table.rows) != len(canonical.rows):
        raise Error("named certificate requires the canonical matrix and full table")
    for i in range(3):
        if not same_vector(table.words[i], canonical.words[i]):
            raise Error("named certificate requires actual 1/021/001 words")
    for i in range(len(canonical.rows)):
        var row_index = find_row(table, canonical.rows[i].letter, canonical.rows[i].key)
        if row_index < 0 or not same_vector(table.rows[row_index].counts, canonical.rows[i].counts):
            raise Error("named certificate requires all actual residue rows")
    var keys = List[List[Int]]()
    keys.append([0, 0, 0])
    keys.append([2, 0, 2])
    keys.append([0, 2, 2])
    var selected = List[List[Int]]()
    selected.append([1, 1, 1])
    selected.append([1, 2, 2])
    selected.append([1, 1, 1])
    for letter in range(3):
        var row_index = find_row(table, letter, keys[letter])
        if row_index < 0 or not same_vector(table.rows[row_index].counts, selected[letter]):
            raise Error("named selected-residue count mismatch")
    var chi: List[Int] = [-2, -2, -1, 1]
    var lo = Q(226953, 100000)
    var hi = Q(113477, 50000)
    var left_sign = require_q(eval_int_poly_at_q(chi, lo), "beta lower evaluation")
    var right_sign = require_q(eval_int_poly_at_q(chi, hi), "beta upper evaluation")
    if not q_int(2).lt(lo) or not lo.lt(hi) or not left_sign.lt(Q.zero()) or not Q.zero().lt(right_sign):
        raise Error("named beta isolating interval failed")
    # chi'(x)=3*x*x-2*x-2 >6 for x>2: this bracket has one root.
    var beta = require_iq(IQ(lo, hi), "beta bracket")
    var f = List[IQ]()
    f.append(require_iq(beta.add(IQ.singleton(q_int(2))), "F0"))
    f.append(require_iq(beta.square(), "F1"))
    f.append(beta.copy())
    # Reconstruct MF-beta*F from the actual incidence matrix and the three
    # declared F polynomials, rather than checking an unattached identity.
    var matrix = Mat3(checked_substitution(named_substitution()).incidence())
    var f_polynomials = List[List[Q]]()
    f_polynomials.append(q_poly([2, 1]))
    f_polynomials.append(q_poly([0, 0, 1]))
    f_polynomials.append(q_poly([0, 1]))
    for letter in range(3):
        var image_weight = List[Q]()
        for source in range(3):
            image_weight = add(image_weight, scale(f_polynomials[source], q_int(matrix.at(letter, source))))
        require_zero_mod_chi(sub(image_weight, mul(q_poly([0, 1]), f_polynomials[letter])))
    # sum(F)=beta^3, beta^4=3beta^2+4beta+2.
    require_zero_mod_chi(sub(add(add(f_polynomials[0], f_polynomials[1]), f_polynomials[2]), q_poly([0, 0, 0, 1])))
    require_zero_mod_chi(q_poly([-2, -4, -3, 0, 1]))
    # 2*(2beta^2+3beta+2)-beta^4 = beta^3 >0.
    require_zero_mod_chi(q_poly([4, 6, 4, -1, -1]))
    var upper = List[Q]()
    for letter in range(3):
        var weight = IQ.singleton(Q.zero())
        for source in range(3):
            weight = require_iq(weight.add(f[source].mul(IQ.singleton(q_int(selected[letter][source])))), "selected weight")
        if not Q.zero().lt(weight.lo):
            raise Error("nonpositive selected residue weight")
        var numerator = require_q(hi.square().mul(f[letter].hi), "upper numerator")
        var bound = require_q(numerator.div(q_int(4).mul(weight.lo)), "occupancy upper")
        if not bound.lt(Q(1, 2)):
            raise Error("interval certificate does not prove strict half bound")
        upper.append(bound^)
    # Exact simplification beta^2*F2/(4*sumF)=1/4 is recorded separately
    # from an interval overestimate.  The other bounds are (beta+2)/(4beta)
    # and beta^4/[4*(2beta^2+3beta+2)].  No maximizer claim is needed.
    return NamedCertificate(beta, upper)


def check_strong_coincidence(images: List[List[Int]], first: Int, second: Int, depth: Int, position: Int, prefix: List[Int], next_letter: Int) raises -> Bool:
    if first < 0 or first >= 3 or second < 0 or second >= 3 or first == second or position < 0 or len(prefix) != 3 or next_letter < 0 or next_letter >= 3:
        raise Error("invalid strong-coincidence witness input")
    var words = inflated_words(images, depth)
    if position >= len(words[first]) or position >= len(words[second]):
        return False
    var a: List[Int] = [0, 0, 0]
    var b: List[Int] = [0, 0, 0]
    for i in range(position):
        a[words[first][i]] += 1
        b[words[second][i]] += 1
    return same_vector(a, prefix) and same_vector(b, prefix) and words[first][position] == next_letter and words[second][position] == next_letter


def verify_named_strong_coincidences() raises:
    var images = named_substitution()
    if not check_strong_coincidence(images, 1, 2, 1, 0, [0, 0, 0], 0):
        raise Error("strong coincidence 1,2 failed")
    if not check_strong_coincidence(images, 0, 1, 5, 31, [12, 13, 6], 1):
        raise Error("strong coincidence 0,1 failed")
    if not check_strong_coincidence(images, 0, 2, 6, 31, [12, 13, 6], 1):
        raise Error("strong coincidence 0,2 failed")
