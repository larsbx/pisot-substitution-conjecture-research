"""Independent literal-word identities for the one-track seam regression.

No overlap rows, seam saturation, periodic-state boxes or product counts are
used to construct these records. Expanded words supply all interior marks,
their exact prefix equations, endpoint ordinals and legal-bigram witnesses.
The result is a bounded full-box comparison, never a strict-sink verdict.
"""

from finite_exact.checked_int import checked_add, checked_neg, checked_sub
from finite_linear_algebra.integer_vector import matvec as integer_matvec
from finite_linear_algebra.mat3 import Mat3
from psc.c4_geometric_f import PrototileMap, PrototileState
from psc.overlap_seed_patch import OverlapState, SeedOverlapTables
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_scale_checked


# If B = 100001, every determinant and adjugate-times-prefix intermediate
# is bounded by 6 B^3 < Int.MAX. This bound also protects nonintegral misses.
comptime MAX_LITERAL_WORD_CAP = 100000


struct LiteralInteriorReturn(Copyable, Movable):
    var state: PrototileState
    var ordinal: Int
    var prefix: List[Int]

    def __init__(out self, state: PrototileState, ordinal: Int, prefix: List[Int]):
        self.state = state
        self.ordinal = ordinal
        self.prefix = prefix.copy()


struct LiteralBigramWitness(ImplicitlyCopyable, Copyable, Movable):
    var left: Int
    var right: Int
    var source: Int
    var level: Int
    var ordinal: Int

    def __init__(out self, left: Int, right: Int, source: Int, level: Int, ordinal: Int):
        self.left = left
        self.right = right
        self.source = source
        self.level = level
        self.ordinal = ordinal


struct LiteralEndpointReturn(ImplicitlyCopyable, Copyable, Movable):
    var cell: OverlapState
    var interior: Int
    var top_ordinal: Int

    def __init__(out self, cell: OverlapState, interior: Int, top_ordinal: Int):
        self.cell = cell
        self.interior = interior
        self.top_ordinal = top_ordinal


struct LiteralSeamReturn(ImplicitlyCopyable, Copyable, Movable):
    var left: OverlapState
    var right: OverlapState
    var interior: Int
    var bigram: Int

    def __init__(out self, left: OverlapState, right: OverlapState, interior: Int, bigram: Int):
        self.left = left
        self.right = right
        self.interior = interior
        self.bigram = bigram


struct LiteralSeamInventory(Copyable, Movable):
    var power: Int
    var images: List[List[Int]]
    var interiors: List[LiteralInteriorReturn]
    var bigrams: List[LiteralBigramWitness]
    var first: List[LiteralEndpointReturn]
    var last: List[LiteralEndpointReturn]
    var seams: List[LiteralSeamReturn]

    def __init__(out self, power: Int, var images: List[List[Int]], var bigrams: List[LiteralBigramWitness]):
        self.power = power
        self.images = images^
        self.bigrams = bigrams^
        self.interiors = List[LiteralInteriorReturn]()
        self.first = List[LiteralEndpointReturn]()
        self.last = List[LiteralEndpointReturn]()
        self.seams = List[LiteralSeamReturn]()

    def fixed_counts(self) -> List[Int]:
        return [len(self.first), len(self.last), len(self.seams)]


def _require_cap(word_cap: Int) raises:
    if word_cap <= 0 or word_cap > MAX_LITERAL_WORD_CAP:
        raise Error("literal seams: word cap must lie in 1..100000; arithmetic scope refused")


def _require_images(images: List[List[Int]]) raises:
    if len(images) != 3:
        raise Error("literal seams: expected three nonempty images")
    for word in images:
        if len(word) == 0 or len(word) > MAX_LITERAL_WORD_CAP:
            raise Error("literal seams: image outside the arithmetic word bound")
        for a in word:
            if a < 0 or a >= 3:
                raise Error("literal seams: letter outside 0..2")


def literal_images(sigma: List[List[Int]], power: Int, word_cap: Int = MAX_LITERAL_WORD_CAP) raises -> List[List[Int]]:
    """Expand original words, refusing before appending beyond the cap."""
    _require_cap(word_cap)
    _require_images(sigma)
    if power < 0:
        raise Error("literal seams: negative expansion power")
    var images: List[List[Int]] = [[0], [1], [2]]
    for _ in range(power):
        var next = List[List[Int]]()
        for word in images:
            var expanded = List[Int]()
            for a in word:
                for b in sigma[a]:
                    if len(expanded) >= word_cap:
                        raise Error("literal seams: image word cap reached; inconclusive")
                    expanded.append(b)
            next.append(expanded^)
        images = next^
    return images^


def _power_matrix(images: List[List[Int]]) raises -> Mat3:
    _require_images(images)
    var entries = List[Int](length=9, fill=0)
    for b in range(3):
        for a in images[b]:
            entries[3 * a + b] += 1
    return Mat3(entries)


def _rows(m: Mat3) -> List[List[Int]]:
    var rows = List[List[Int]]()
    for i in range(3):
        rows.append([m.at(i, 0), m.at(i, 1), m.at(i, 2)])
    return rows^


def _return_matrix(images: List[List[Int]]) raises -> Mat3:
    var m = _power_matrix(images)
    for a in range(3):
        m.e[4 * a] = checked_sub(m.e[4 * a], 1)
    return m^


def _prefix(word: List[Int], ordinal: Int) raises -> List[Int]:
    if ordinal < 0 or ordinal >= len(word):
        raise Error("literal seams: occurrence ordinal outside its original word")
    var p: List[Int] = [0, 0, 0]
    for k in range(ordinal):
        p[word[k]] += 1
    return p^


def _position(tables: SeedOverlapTables, vector: List[Int]) raises -> CubicElt:
    var out = CubicElt()
    for a in range(3):
        out = cubic_add_checked(out, cubic_scale_checked(tables.lengths.at(a), vector[a]))
    return out


def replay_interior_return(images: List[List[Int]], record: LiteralInteriorReturn) raises:
    """Replay a supplied occurrence against the caller's literal n-th images."""
    var a = _return_matrix(images)
    var b = record.state.letter
    if b < 0 or b >= 3:
        raise Error("literal seams: interior letter outside 0..2")
    ref word = images[b]
    var j = record.ordinal
    if j <= 0 or j >= len(word) - 1 or word[j] != b:
        raise Error("literal seams: interior occurrence is not an original interior self-mark")
    if record.prefix != _prefix(word, j):
        raise Error("literal seams: original occurrence prefix disagrees")
    if record.state.is_vertex() or integer_matvec(_rows(a), record.state.vector()) != record.prefix:
        raise Error("literal seams: interior return equation disagrees")


def _literal_bigrams(sigma: List[List[Int]], word_cap: Int) raises -> List[LiteralBigramWitness]:
    # The primitive gate is supplied by literal_one_track_returns. The
    # union of letters at every level is the whole alphabet. Stabilizing
    # adjacent pairs therefore closes the full language of length two.
    var seen = List[Bool](length=9, fill=False)
    var records = List[LiteralBigramWitness]()
    for level in range(1, 11):
        var images = literal_images(sigma, level, word_cap)
        var changed = False
        for source in range(3):
            ref word = images[source]
            for j in range(len(word) - 1):
                var key = 3 * word[j] + word[j + 1]
                if not seen[key]:
                    seen[key] = True
                    records.append(LiteralBigramWitness(word[j], word[j + 1], source, level, j))
                    changed = True
        if not changed:
            return records^
    raise Error("literal seams: legal bigrams did not stabilize; inconclusive")


def replay_bigram(sigma: List[List[Int]], record: LiteralBigramWitness, word_cap: Int = MAX_LITERAL_WORD_CAP) raises:
    if record.level <= 0 or record.level > 10 or record.source < 0 or record.source >= 3:
        raise Error("literal seams: invalid legal-bigram source")
    var images = literal_images(sigma, record.level, word_cap)
    ref word = images[record.source]
    var j = record.ordinal
    if j < 0 or j >= len(word) - 1 or word[j] != record.left or word[j + 1] != record.right:
        raise Error("literal seams: legal-bigram occurrence disagrees")


def _endpoint_vector(state: PrototileState, top: Int, right: Bool) raises -> List[Int]:
    var vector = state.vector()
    for a in range(3):
        vector[a] = checked_neg(vector[a])
    if right:
        vector[top] = checked_add(vector[top], 1)
    return vector^


def replay_endpoint_return(
    tables: SeedOverlapTables, images: List[List[Int]], interior: LiteralInteriorReturn,
    endpoint: LiteralEndpointReturn, right: Bool,
) raises:
    replay_interior_return(images, interior)
    var top = endpoint.cell.top
    if top < 0 or top >= 3 or endpoint.cell.bottom != interior.state.letter:
        raise Error("literal seams: endpoint labels disagree with its interior mark")
    var ordinal = len(images[top]) - 1 if right else 0
    if endpoint.top_ordinal != ordinal or images[top][ordinal] != top:
        raise Error("literal seams: endpoint is not its original first or last occurrence")
    var vector = _endpoint_vector(interior.state, top, right)
    if endpoint.cell.shift != _position(tables, vector):
        raise Error("literal seams: endpoint offset disagrees with its interior mark")
    var child = integer_matvec(_rows(_power_matrix(images)), vector)
    var top_prefix = _prefix(images[top], ordinal)
    for a in range(3):
        child[a] = checked_sub(checked_add(child[a], interior.prefix[a]), top_prefix[a])
    if child != vector:
        raise Error("literal seams: original endpoint occurrence does not return")


def replay_seam_return(
    tables: SeedOverlapTables, images: List[List[Int]], interiors: List[LiteralInteriorReturn],
    bigrams: List[LiteralBigramWitness], seam: LiteralSeamReturn,
) raises:
    if seam.interior < 0 or seam.interior >= len(interiors) or seam.bigram < 0 or seam.bigram >= len(bigrams):
        raise Error("literal seams: seam witness index outside its inventory")
    var bigram = bigrams[seam.bigram]
    replay_bigram(tables.sigma, bigram)
    if seam.left.top != bigram.left or seam.right.top != bigram.right:
        raise Error("literal seams: ordered seam disagrees with its legal bigram")
    if seam.left.top < 0 or seam.left.top >= 3:
        raise Error("literal seams: seam letter outside 0..2")
    var left = LiteralEndpointReturn(seam.left, seam.interior, len(images[seam.left.top]) - 1)
    var right = LiteralEndpointReturn(seam.right, seam.interior, 0)
    replay_endpoint_return(tables, images, interiors[seam.interior], left, True)
    replay_endpoint_return(tables, images, interiors[seam.interior], right, False)


def _require_room(count: Int, max_records: Int) raises:
    if count >= max_records:
        raise Error("literal seams: record cap reached; inconclusive")


def literal_one_track_returns(
    sigma: List[List[Int]], power: Int, word_cap: Int = MAX_LITERAL_WORD_CAP, max_records: Int = 100000,
) raises -> LiteralSeamInventory:
    """Full-box fixed identities at one power, with original occurrence witnesses.

    Each population has a separate record cap. No empty or partial inventory
    is returned on a cap or an arithmetic/screening refusal.
    PrototileMap retains its audited source-image-length bound of six.
    The replay helpers consume this constructor's actual expanded words;
    they are not an authenticator for arbitrary externally supplied images.
    """
    _require_cap(word_cap)
    if power <= 0 or max_records <= 0:
        raise Error("literal seams: power and record cap must be positive")
    # Reuse the source PIP3/positive-length gate, but never its cycle search.
    var m = PrototileMap(sigma)
    var det_source = m.incidence.det()
    if det_source != 1 and det_source != -1:
        raise Error("literal seams: source incidence must be unimodular")
    var images = literal_images(sigma, power, word_cap)
    var bigrams = _literal_bigrams(sigma, word_cap)
    var result = LiteralSeamInventory(power, images^, bigrams^)
    var a = _return_matrix(result.images)
    var det = a.det()
    if det == 0:
        raise Error("literal seams: singular return equation")
    var adjugate = _rows(a.adjugate())
    var states = Dict[PrototileState, Bool]()
    for b in range(3):
        ref word = result.images[b]
        var prefix: List[Int] = [0, 0, 0]
        for j in range(len(word)):
            if word[j] == b and j > 0 and j < len(word) - 1:
                var numerator = integer_matvec(adjugate, prefix)
                var integral = True
                for x in numerator:
                    integral = integral and x % det == 0
                if integral:
                    var state = PrototileState(b, numerator[0] // det, numerator[1] // det, numerator[2] // det)
                    var record = LiteralInteriorReturn(state, j, prefix)
                    replay_interior_return(result.images, record)
                    if not m.is_state(state) or m.sign(m.position(state)) <= 0:
                        raise Error("literal seams: self-mark is not strictly inside its bottom tile")
                    if state in states:
                        raise Error("literal seams: duplicate interior identity")
                    states[state] = True
                    _require_room(len(result.interiors), max_records)
                    result.interiors.append(record^)
            prefix[word[j]] += 1

    for i in range(len(result.interiors)):
        ref interior = result.interiors[i]
        for top in range(3):
            ref word = result.images[top]
            if word[0] == top:
                var cell = OverlapState(top, interior.state.letter, _position(m.tables, _endpoint_vector(interior.state, top, False)))
                var endpoint = LiteralEndpointReturn(cell, i, 0)
                replay_endpoint_return(m.tables, result.images, interior, endpoint, False)
                _require_room(len(result.first), max_records)
                result.first.append(endpoint)
            if word[len(word) - 1] == top:
                var cell = OverlapState(top, interior.state.letter, _position(m.tables, _endpoint_vector(interior.state, top, True)))
                var endpoint = LiteralEndpointReturn(cell, i, len(word) - 1)
                replay_endpoint_return(m.tables, result.images, interior, endpoint, True)
                _require_room(len(result.last), max_records)
                result.last.append(endpoint)
        for k in range(len(result.bigrams)):
            var pair = result.bigrams[k]
            if result.images[pair.left][len(result.images[pair.left]) - 1] != pair.left or result.images[pair.right][0] != pair.right:
                continue
            var left = OverlapState(pair.left, interior.state.letter, _position(m.tables, _endpoint_vector(interior.state, pair.left, True)))
            var right = OverlapState(pair.right, interior.state.letter, _position(m.tables, _endpoint_vector(interior.state, pair.right, False)))
            var seam = LiteralSeamReturn(left, right, i, k)
            replay_seam_return(m.tables, result.images, result.interiors, result.bigrams, seam)
            _require_room(len(result.seams), max_records)
            result.seams.append(seam)
    return result^
