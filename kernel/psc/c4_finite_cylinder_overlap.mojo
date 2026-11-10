"""Bounded exact finite-cylinder covers for two productive non-unit controls.

All occurrences, including repeated letters and equal residue keys, are retained.
The finite output certifies outer covers and overlap upper bounds only.  The IFS
and measure implications are separate written proofs; no strict-cut density or
strict component is inferred here.  See the literature gate and overlap note.
"""

from finite_exact.closed_interval import IQ
from finite_exact.rat_q import Q, q_abs, q_max, q_min
from finite_linear_algebra.mat3 import Mat3, identity3
from finite_linear_algebra.scalar import q_int
from psc.c4_nonunit_residue_occupancy import (
    checked_substitution, inflated_words, named_substitution, residue_key,
    same_vector,
)
from psc.exact import eval_int_poly_at_q, midpoint, require_iq, require_q
from psc.c4_cylinder_density import verify_named_chart_density
from psc.words import Pair

comptime GRID = 16
comptime GRID_CAP = 65536
comptime OCCURRENCE_CAP = 2187


struct CylinderChart(Copyable, Movable):
    var beta: IQ
    var a: IQ
    var b: IQ
    var kappa: IQ
    var radius: Int
    var block: Int

    def __init__(out self, beta: IQ, a: IQ, b: IQ, kappa: IQ):
        self.beta = beta.copy()
        self.a = a.copy()
        self.b = b.copy()
        self.kappa = kappa.copy()
        self.radius = 40
        self.block = 12


struct GridBox(Copyable, Movable):
    var xlo: Int
    var xhi: Int
    var ylo: Int
    var yhi: Int

    def __init__(out self, xlo: Int, xhi: Int, ylo: Int, yhi: Int):
        self.xlo = xlo
        self.xhi = xhi
        self.ylo = ylo
        self.yhi = yhi


struct CylinderOccurrence(Copyable, Movable):
    var source: Int
    var position: Int
    var letter: Int
    var prefix: List[Int]
    var key: List[Int]
    var parent: List[Int]
    var box: GridBox

    def __init__(out self, source: Int, position: Int, letter: Int, prefix: List[Int], key: List[Int], parent: List[Int], box: GridBox):
        self.source = source
        self.position = position
        self.letter = letter
        self.prefix = prefix.copy()
        self.key = key.copy()
        self.parent = parent.copy()
        self.box = box.copy()


struct CylinderSlice(Copyable, Movable):
    var letter: Int
    var key: List[Int]
    var box: GridBox

    def __init__(out self, letter: Int, key: List[Int], box: GridBox):
        self.letter = letter
        self.key = key.copy()
        self.box = box.copy()


struct CylinderCertificate(Copyable, Movable):
    var fixture: Int
    var depth: Int
    var period: Int
    var index: Int
    var occurrences: List[CylinderOccurrence]
    var slices: List[CylinderSlice]

    def __init__(out self, fixture: Int, depth: Int, index: Int, occurrences: List[CylinderOccurrence], slices: List[CylinderSlice]):
        self.fixture = fixture
        self.depth = depth
        self.period = 2
        self.index = index
        self.occurrences = occurrences.copy()
        self.slices = slices.copy()


struct StrongCoincidenceWitness(Copyable, Movable):
    var first: Int
    var second: Int
    var depth: Int
    var position: Int
    var prefix: List[Int]
    var letter: Int

    def __init__(out self, first: Int, second: Int, depth: Int, position: Int, prefix: List[Int], letter: Int):
        self.first = first
        self.second = second
        self.depth = depth
        self.position = position
        self.prefix = prefix.copy()
        self.letter = letter


def fixture_images(fixture: Int) raises -> List[List[Int]]:
    if fixture < 0 or fixture > 1:
        raise Error("only the two named productive controls are supported")
    var images = named_substitution()
    if fixture == 1:
        images[1] = [0, 1, 2]
    return images^


def named_matrix() -> Mat3:
    return Mat3([0, 1, 2, 1, 1, 1, 0, 1, 0])


def matrix_power(depth: Int) raises -> Mat3:
    if depth < 0 or depth > 12:
        raise Error("matrix power outside bounded range 0..12")
    var power = identity3()
    var matrix = named_matrix()
    for _ in range(depth):
        power = power * matrix
    return power^


def make_chart() raises -> CylinderChart:
    var lo = q_int(2)
    var hi = q_int(3)
    for _ in range(48):
        var mid = midpoint(lo, hi)
        var value = eval_int_poly_at_q([-2, -2, -1, 1], mid)
        if value.lt(Q.zero()):
            lo = mid^
        else:
            hi = mid^
    if not eval_int_poly_at_q([-2, -2, -1, 1], lo).lt(Q.zero()) or not Q.zero().lt(eval_int_poly_at_q([-2, -2, -1, 1], hi)):
        raise Error("root bracket must have strict opposite endpoint signs")
    var beta = require_iq(IQ(lo, hi), "beta bracket")
    # Polynomial reductions in Q[beta] avoid reciprocal wrapping for a/kappa.
    # a=(beta+2)/beta^2=(3beta-beta^2)/2; kappa=4beta-beta^2.
    var a = require_iq(beta.mul(IQ.singleton(q_int(3))).sub(beta.square()).mul(IQ.singleton(Q(1, 2))), "chart a")
    var b = require_iq(beta.reciprocal(), "chart b")
    var kappa = require_iq(beta.mul(IQ.singleton(q_int(4))).sub(beta.square()), "chart covolume")
    if not Q.zero().lt(kappa.lo):
        raise Error("chart covolume must be positive")
    return CylinderChart(beta, a, b, kappa)


def project_coordinate(chart: CylinderChart, vector: List[Int], coordinate: Int) raises -> IQ:
    if len(vector) != 3 or coordinate < 0 or coordinate > 1:
        raise Error("projection shape mismatch")
    # Native Int arithmetic stays below 3^12*729 in the bounded callers.
    for i in range(3):
        if vector[i] < -1000000000 or vector[i] > 1000000000:
            raise Error("projection vector exceeds bounded domain")
    var coefficient = chart.a.copy() if coordinate == 0 else chart.b.copy()
    var entry = vector[0] if coordinate == 0 else vector[2]
    return require_iq(IQ.singleton(q_int(entry)).sub(coefficient.mul(IQ.singleton(q_int(vector[1])))), "projected coordinate")


def interval_abs_upper(value: IQ) raises -> Q:
    _ = require_iq(value, "absolute interval bound")
    return require_q(q_max(q_abs(value.lo), q_abs(value.hi)), "absolute interval bound")


def row_norm(chart: CylinderChart, power: Mat3, coordinate: Int) raises -> Q:
    var left = project_coordinate(chart, [power.at(0, 0), power.at(1, 0), power.at(2, 0)], coordinate)
    var right = project_coordinate(chart, [power.at(0, 2), power.at(1, 2), power.at(2, 2)], coordinate)
    return require_q(interval_abs_upper(left).add(interval_abs_upper(right)), "row norm")


def interval_hull(first: IQ, second: IQ) raises -> IQ:
    _ = require_iq(first, "hull first interval")
    _ = require_iq(second, "hull second interval")
    return require_iq(IQ(q_min(first.lo, second.lo), q_max(first.hi, second.hi)), "interval hull")


def certify_radius(fixture: Int, chart: CylinderChart) raises:
    # Mutable caller-supplied charts cannot silently alter normalization.
    var canonical = make_chart()
    if chart.radius != 40 or chart.block != 12:
        raise Error("unsupported common enclosure radius or contraction block")
    var submitted: List[IQ] = [chart.beta.copy(), chart.a.copy(), chart.b.copy(), chart.kappa.copy()]
    var expected: List[IQ] = [canonical.beta.copy(), canonical.a.copy(), canonical.b.copy(), canonical.kappa.copy()]
    for i in range(4):
        if submitted[i].rejected or not submitted[i].lo.eq(expected[i].lo) or not submitted[i].hi.eq(expected[i].hi):
            raise Error("chart or covolume differs from the canonical normalization")
    var images = fixture_images(fixture)
    var sigma = checked_substitution(images)
    if not same_vector(sigma.incidence(), named_matrix().e):
        raise Error("named incidence identity failed")
    var words2 = inflated_words(images, 2)
    if words2[0][0] != 0 or len(words2[0]) <= 1:
        raise Error("productive fixed point period two was not witnessed")
    var block_power = matrix_power(12)
    for coordinate in range(2):
        if not row_norm(chart, block_power, coordinate).le(Q(7, 8)):
            raise Error("fixed block does not certify the contraction bound")
    # Complete proper-prefix hull recursion.  Decompose sigma^n(source) into
    # every sigma^(n-1)(child); translated child hulls include every position.
    var hulls = List[IQ]()
    for _ in range(6):
        hulls.append(IQ.singleton(Q.zero()))
    var power = identity3()
    for _ in range(12):
        var next_hulls = List[IQ]()
        for source in range(3):
            for coordinate in range(2):
                var prefix: List[Int] = [0, 0, 0]
                var aggregate = IQ.singleton(Q.zero())
                for position in range(len(images[source])):
                    var letter = images[source][position]
                    var projected = project_coordinate(chart, power.apply(prefix), coordinate)
                    var translated = require_iq(projected.add(hulls[2 * letter + coordinate]), "prefix hull translate")
                    if position == 0:
                        aggregate = translated^
                    else:
                        aggregate = interval_hull(aggregate, translated)
                    prefix[letter] += 1
                next_hulls.append(aggregate^)
        hulls = next_hulls^
        power = power * named_matrix()
    for i in range(6):
        if not q_int(-5).le(hulls[i].lo) or not hulls[i].hi.le(q_int(5)):
            raise Error("complete block digit hull exceeds the fixed bound five")
    if not Q(7, 8).mul(q_int(chart.radius)).add(q_int(5)).le(q_int(chart.radius)):
        raise Error("common outer radius invariance inequality failed")


def grid_floor(value: Q) raises -> Int:
    _ = require_q(value, "dyadic rounding")
    if not Q(-GRID_CAP, GRID).le(value) or not value.le(Q(GRID_CAP, GRID)):
        raise Error("dyadic enclosure exceeds coordinate cap")
    var lo = -GRID_CAP
    var hi = GRID_CAP
    while lo < hi:
        var mid = lo + (hi - lo + 1) // 2
        if Q(Int64(mid), GRID).le(value):
            lo = mid
        else:
            hi = mid - 1
    return lo


def grid_ceil(value: Q) raises -> Int:
    return -grid_floor(value.neg())


def occurrence_box(chart: CylinderChart, power: Mat3, prefix: List[Int]) raises -> GridBox:
    var endpoints = List[Int]()
    for coordinate in range(2):
        var center = project_coordinate(chart, prefix, coordinate)
        var extent = require_q(row_norm(chart, power, coordinate).mul(q_int(chart.radius)), "cylinder radius")
        endpoints.append(grid_floor(require_q(center.lo.sub(extent), "cylinder lower")))
        endpoints.append(grid_ceil(require_q(center.hi.add(extent), "cylinder upper")))
    return GridBox(endpoints[0], endpoints[1], endpoints[2], endpoints[3])


def valid_box(box: GridBox) -> Bool:
    return box.xlo >= -GRID_CAP and box.xhi <= GRID_CAP and box.ylo >= -GRID_CAP and box.yhi <= GRID_CAP and box.xlo <= box.xhi and box.ylo <= box.yhi


def same_box(first: GridBox, second: GridBox) -> Bool:
    return first.xlo == second.xlo and first.xhi == second.xhi and first.ylo == second.ylo and first.yhi == second.yhi


def hull_box(first: GridBox, second: GridBox) -> GridBox:
    var xlo = first.xlo if first.xlo < second.xlo else second.xlo
    var xhi = first.xhi if first.xhi > second.xhi else second.xhi
    var ylo = first.ylo if first.ylo < second.ylo else second.ylo
    var yhi = first.yhi if first.yhi > second.yhi else second.yhi
    return GridBox(xlo, xhi, ylo, yhi)


def build_certificate(fixture: Int, depth: Int, period: Int = 2, occurrence_cap: Int = OCCURRENCE_CAP, word_cap: Int = 100000) raises -> CylinderCertificate:
    if period != 2 or depth < 2 or depth > 6 or depth % 2 != 0:
        raise Error("cylinder depth must be 2, 4 or 6 with period two")
    if occurrence_cap < 1 or occurrence_cap > OCCURRENCE_CAP:
        raise Error("occurrence cap outside supported range")
    var images = fixture_images(fixture)
    var chart = make_chart()
    certify_radius(fixture, chart)
    var words = inflated_words(images, depth, word_cap)
    var power = matrix_power(depth)
    var parent_power = matrix_power(depth - 2)
    var index = power.det()
    var parent_index = parent_power.det()
    var adjugate = power.adjugate()
    var parent_adjugate = parent_power.adjugate()
    var occurrences = List[CylinderOccurrence]()
    var slices = List[CylinderSlice]()
    for source in range(3):
        var prefix: List[Int] = [0, 0, 0]
        for position in range(len(words[source])):
            if len(occurrences) >= occurrence_cap:
                raise Error("complete occurrence list exceeds its declared cap")
            var letter = words[source][position]
            var key = residue_key(adjugate, index, prefix)
            # Quotient refinement uses the actual prefix, not child-key mod.
            var parent = residue_key(parent_adjugate, parent_index, prefix)
            var box = occurrence_box(chart, power, prefix)
            occurrences.append(CylinderOccurrence(source, position, letter, prefix, key, parent, box))
            var found = -1
            for i in range(len(slices)):
                if slices[i].letter == letter and same_vector(slices[i].key, key):
                    found = i
                    break
            if found < 0:
                slices.append(CylinderSlice(letter, key, box))
            else:
                slices[found].box = hull_box(slices[found].box, box)
            prefix[letter] += 1
    return CylinderCertificate(fixture, depth, index, occurrences, slices)


def validate_certificate(certificate: CylinderCertificate) raises:
    var expected = build_certificate(certificate.fixture, certificate.depth, certificate.period)
    if certificate.index != expected.index or len(certificate.occurrences) != len(expected.occurrences) or len(certificate.slices) != len(expected.slices):
        raise Error("certificate metadata or complete record count differs")
    for i in range(len(expected.occurrences)):
        var got = certificate.occurrences[i].copy()
        var want = expected.occurrences[i].copy()
        if got.source != want.source or got.position != want.position or got.letter != want.letter or not same_vector(got.prefix, want.prefix) or not same_vector(got.key, want.key) or not same_vector(got.parent, want.parent):
            raise Error("occurrence identity, exact residue or refinement differs")
        if not valid_box(got.box) or not same_box(got.box, want.box):
            raise Error("occurrence outer enclosure is not the canonical certified box")
    for i in range(len(expected.slices)):
        var got = certificate.slices[i].copy()
        var want = expected.slices[i].copy()
        if got.letter != want.letter or not same_vector(got.key, want.key) or not valid_box(got.box) or not same_box(got.box, want.box):
            raise Error("slice hull does not match all occurrence-indexed boxes")


def intersection_area(first: GridBox, second: GridBox) raises -> Q:
    if not valid_box(first) or not valid_box(second):
        raise Error("invalid bounded rectangle in area computation")
    var xlo = first.xlo if first.xlo > second.xlo else second.xlo
    var xhi = first.xhi if first.xhi < second.xhi else second.xhi
    var ylo = first.ylo if first.ylo > second.ylo else second.ylo
    var yhi = first.yhi if first.yhi < second.yhi else second.yhi
    if xhi <= xlo or yhi <= ylo:
        return Q.zero()
    return Q(Int64((xhi - xlo) * (yhi - ylo)), GRID * GRID)


def pair_area_sum(certificate: CylinderCertificate, first: Int, second: Int) raises -> Q:
    if first < 0 or first > 2 or second <= first or second > 2:
        raise Error("letter pair must satisfy 0 <= first < second <= 2")
    validate_certificate(certificate)
    var total = Q.zero()
    for i in range(len(certificate.slices)):
        if certificate.slices[i].letter != first:
            continue
        for j in range(len(certificate.slices)):
            if certificate.slices[j].letter == second and same_vector(certificate.slices[i].key, certificate.slices[j].key):
                total = require_q(total.add(intersection_area(certificate.slices[i].box, certificate.slices[j].box)), "overlap area sum")
    return total^


def pair_upper(certificate: CylinderCertificate, first: Int, second: Int) raises -> Q:
    return require_q(pair_area_sum(certificate, first, second).div(q_int(certificate.index)), "Haar-normalized upper bound")


def strict_arithmetic_gap(upper: Q, kappa_lower: Q, density_lower: Q) raises -> Q:
    """Scalar comparison only; this helper establishes no density provenance."""
    var u = require_q(upper, "scalar overlap upper")
    var k = require_q(kappa_lower, "scalar covolume lower")
    var d = require_q(density_lower, "scalar cut density lower")
    if u.lt(Q.zero()) or not Q.zero().lt(k) or not Q.zero().lt(d):
        raise Error("scalar comparison needs a nonnegative area and positive lower inputs")
    var gap = require_q(k.mul(d).sub(u), "strict comparison gap")
    if not Q.zero().lt(gap):
        raise Error("equation eleven requires a strictly positive gap")
    return gap^


def certify_equation_11(
    certificate: CylinderCertificate, states: List[Pair],
    first: Int, second: Int, steps: Int,
    proposed_lower: Q, normalization: String,
) raises -> Q:
    """Conditional incompatibility only after complete upper and lower checks.

    This finite entry point still depends on the written measure implication.
    No valid strict component is supplied for either productive control. In
    particular a zero upper plus an arbitrary positive scalar cannot pass.
    """
    # pair_upper authenticates every occurrence, refinement, box and slice by
    # canonical reconstruction; no caller-supplied aggregate is trusted.
    var upper = pair_upper(certificate, first, second)
    var chart = make_chart()
    _ = verify_named_chart_density(
        fixture_images(certificate.fixture), states, first, second, steps,
        chart.beta.hi, proposed_lower, normalization,
    )
    return strict_arithmetic_gap(upper, chart.kappa.lo, proposed_lower)


def find_strong_coincidence(fixture: Int, first: Int, second: Int) raises -> StrongCoincidenceWitness:
    if first < 0 or first > 2 or second <= first or second > 2:
        raise Error("invalid strong coincidence letter pair")
    var images = fixture_images(fixture)
    for depth in range(1, 7):
        var words = inflated_words(images, depth)
        var prefix_first: List[Int] = [0, 0, 0]
        var prefix_second: List[Int] = [0, 0, 0]
        var length = len(words[first]) if len(words[first]) < len(words[second]) else len(words[second])
        for position in range(length):
            if words[first][position] == words[second][position] and same_vector(prefix_first, prefix_second):
                return StrongCoincidenceWitness(first, second, depth, position, prefix_first, words[first][position])
            prefix_first[words[first][position]] += 1
            prefix_second[words[second][position]] += 1
    raise Error("no strong coincidence witness within bounded search")
