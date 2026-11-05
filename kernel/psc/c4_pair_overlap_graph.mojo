"""Complete compact M-adic pair graphs for the two #495 controls.

Keep every paired prefix occurrence. A failed cap or subinvariant search
raises, never a negative conclusion. No SC witness is read. Measure scaling
and the finite-graph implication are written dependencies, not Lean proofs.
"""
from finite_exact.closed_interval import IQ
from finite_exact.rat_q import Q
from finite_linear_algebra.mat3 import identity3
from finite_linear_algebra.scalar import q_int
from psc.exact import require_iq
from psc.c4_nonunit_residue_occupancy import inflated_words
from psc.c4_finite_cylinder_overlap import (
    fixture_images, make_chart, certify_radius, matrix_power, named_matrix,
    project_coordinate, interval_abs_upper, interval_hull,
)

comptime SCALE = 1000000
comptime STATE_LIMIT = 16000
comptime COORD_LIMIT = 32
comptime WIDTH = 65


struct PairGraph(Copyable, Movable):
    var fixture: Int
    var states: List[List[Int]]
    var rows: List[List[Int]]
    var residue_rejections: Int
    var box_rejections: Int

    def __init__(out self, fixture: Int, states: List[List[Int]], rows: List[List[Int]], residue: Int, box: Int):
        self.fixture = fixture
        self.states = states.copy()
        self.rows = rows.copy()
        self.residue_rejections = residue
        self.box_rejections = box


def certify_pair_box(fixture: Int) raises:
    var chart = make_chart()
    certify_radius(fixture, chart)
    if not Q(828911,SCALE).le(chart.a.lo) or not chart.a.hi.le(Q(828912,SCALE)):
        raise Error("pair chart a interval")
    if not Q(440619,SCALE).le(chart.b.lo) or not chart.b.hi.le(Q(440620,SCALE)):
        raise Error("pair chart b interval")
    var square = require_iq(chart.beta.square(), "beta squared")
    if not Q(103,20).lt(square.lo):
        raise Error("insufficient certified spectral gap")
    var power12 = matrix_power(12)
    var entry_bounds: List[Q] = [Q(473,1000),Q(390,1000),Q(147,1000),Q(344,1000)]
    for coordinate in range(2):
        for j in range(2):
            var col = 0 if j == 0 else 2
            var value = project_coordinate(chart, [power12.at(0,col),power12.at(1,col),power12.at(2,col)], coordinate)
            if not interval_abs_upper(value).le(entry_bounds[2*coordinate+j]):
                raise Error("stable block entry exceeds certified bound")
    # Same complete proper-prefix recursion as #495, with coordinate bounds.
    var images = fixture_images(fixture)
    var hulls = List[IQ]()
    for _ in range(6):
        hulls.append(IQ.singleton(Q.zero()))
    var power = identity3()
    for _ in range(12):
        var next_hulls = List[IQ]()
        for source in range(3):
            for coordinate in range(2):
                var prefix: List[Int] = [0,0,0]
                var aggregate = IQ.singleton(Q.zero())
                for position in range(len(images[source])):
                    var letter = images[source][position]
                    var shift = project_coordinate(chart, power.apply(prefix), coordinate)
                    var translated = require_iq(shift.add(hulls[2*letter+coordinate]), "block digit")
                    if position == 0:
                        aggregate = translated^
                    else:
                        aggregate = interval_hull(aggregate,translated)
                    prefix[letter] += 1
                next_hulls.append(aggregate^)
        hulls = next_hulls^
        power = power * named_matrix()
    for source in range(3):
        if not interval_abs_upper(hulls[2*source]).le(Q(23,5)):
            raise Error("x digit bound missing an occurrence")
        if not interval_abs_upper(hulls[2*source+1]).le(Q(14,5)):
            raise Error("y digit bound missing an occurrence")
    var radii: List[Int] = [16,8]
    var digits: List[Q] = [Q(23,5),Q(14,5)]
    for i in range(2):
        var linear = entry_bounds[2*i].mul(q_int(radii[0])).add(entry_bounds[2*i+1].mul(q_int(radii[1])))
        if not linear.lt(q_int(radii[i])) or not linear.add(digits[i]).le(q_int(radii[i])):
            raise Error("anisotropic outer box invariance failed")


def canonical_pair(c: Int, d: Int, x: Int, y: Int, z: Int) -> List[Int]:
    var positive = x > 0 or (x == 0 and y > 0) or (x == 0 and y == 0 and z > 0)
    if c > d or (c == d and positive):
        return [d,c,-x,-y,-z]
    return [c,d,x,y,z]


def outside_pair_box(x: Int, y: Int, z: Int) -> Bool:
    var coordinates: List[Int] = [x,z]
    var lower: List[Int] = [828911,440619]
    var upper: List[Int] = [828912,440620]
    var limits: List[Int] = [32*SCALE,16*SCALE]
    for i in range(2):
        var first = SCALE*coordinates[i]-lower[i]*y
        var second = SCALE*coordinates[i]-upper[i]*y
        if (first > limits[i] and second > limits[i]) or (first < -limits[i] and second < -limits[i]):
            return True
    return False


def state_key(state: List[Int]) raises -> Int:
    if len(state) != 5 or state[0] < 0 or state[0] > 2 or state[1] < 0 or state[1] > 2:
        raise Error("pair state shape")
    var key = 3*state[0]+state[1]
    for i in range(2,5):
        if state[i] < -COORD_LIMIT or state[i] > COORD_LIMIT:
            raise Error("coordinate budget exhausted; inconclusive")
        key = WIDTH*key+state[i]+COORD_LIMIT
    return key


def build_pair_graph(fixture: Int, state_cap: Int = STATE_LIMIT) raises -> PairGraph:
    if fixture < 0 or fixture > 1 or state_cap < 3 or state_cap > STATE_LIMIT:
        raise Error("unsupported fixture or state budget")
    certify_pair_box(fixture)
    var images = fixture_images(fixture)
    var words = inflated_words(images,2)
    # Records are [following letter, source, literal position, p0,p1,p2].
    var digits = List[List[Int]]()
    for source in range(3):
        var p: List[Int] = [0,0,0]
        for position in range(len(words[source])):
            var letter = words[source][position]
            digits.append([letter,source,position,p[0],p[1],p[2]])
            p[letter] += 1
    var lookup = List[Int]()
    for _ in range(9*WIDTH*WIDTH*WIDTH):
        lookup.append(-1)
    var states: List[List[Int]] = [[0,1,0,0,0],[0,2,0,0,0],[1,2,0,0,0]]
    for i in range(3):
        lookup[state_key(states[i])] = i
    var rows = List[List[Int]]()
    var cursor = 0
    var residue_rejections = 0
    var box_rejections = 0
    var inverse_numerator = matrix_power(2).adjugate()
    if matrix_power(2).det() != 4:
        raise Error("wrong exact quotient index")
    while cursor < len(states):
        var state = states[cursor].copy()
        var targets = List[Int]()
        for i in range(len(digits)):
            if digits[i][0] != state[0]:
                continue
            for j in range(len(digits)):
                if digits[j][0] != state[1]:
                    continue
                var delta: List[Int] = [
                    state[2]+digits[j][3]-digits[i][3],
                    state[3]+digits[j][4]-digits[i][4],
                    state[4]+digits[j][5]-digits[i][5],
                ]
                var values = inverse_numerator.apply(delta)
                if values[0] % 4 != 0 or values[1] % 4 != 0 or values[2] % 4 != 0:
                    residue_rejections += 1
                    continue
                var x = values[0] // 4
                var y = values[1] // 4
                var z = values[2] // 4
                if outside_pair_box(x,y,z):
                    box_rejections += 1
                    continue
                var child = canonical_pair(digits[i][1],digits[j][1],x,y,z)
                var key = state_key(child)
                var target = lookup[key]
                if target < 0:
                    if len(states) >= state_cap:
                        raise Error("state budget exhausted; inconclusive")
                    target = len(states)
                    lookup[key] = target
                    states.append(child^)
                targets.append(target)  # NEVER deduplicate paired occurrences.
        rows.append(targets^)
        cursor += 1
    return PairGraph(fixture,states,rows,residue_rejections,box_rejections)


def verify_pair_weights(graph: PairGraph, weights: List[Int]) raises -> Int:
    # Arithmetic only unless graph was obtained from build_pair_graph.
    if graph.fixture < 0 or graph.fixture > 1 or len(weights) != len(graph.states) or len(graph.rows) != len(weights):
        raise Error("weight dimensions/fixture")
    for w in weights:
        if w < 1 or w > 1000000:
            raise Error("positive bounded integer weights required")
    var numerator = 99 if graph.fixture == 0 else 101
    var minimum_gap = 1000000000
    for i in range(len(weights)):
        var total = 0
        for j in graph.rows[i]:
            if j < 0 or j >= len(weights):
                raise Error("invalid graph target")
            total += weights[j]
        var gap = numerator*weights[i]-20*total
        if gap < 0:
            raise Error("false exact subinvariance")
        if gap < minimum_gap:
            minimum_gap = gap
    return minimum_gap


def construct_pair_weights(graph: PairGraph, iteration_cap: Int = 4000) raises -> Tuple[List[Int],Int]:
    if iteration_cap < 1 or iteration_cap > 4000:
        raise Error("weight iteration budget")
    var numerator = 99 if graph.fixture == 0 else 101
    var weights = List[Int]()
    for _ in range(len(graph.states)):
        weights.append(1)
    for iteration in range(1,iteration_cap+1):
        var following = List[Int]()
        var unchanged = True
        for i in range(len(weights)):
            var total = 0
            for j in graph.rows[i]:
                total += weights[j]
            var value = 1+(20*total+numerator-1)//numerator
            if value > 1000000:
                raise Error("weight budget exhausted; inconclusive")
            if value != weights[i]:
                unchanged = False
            following.append(value)
        if unchanged:
            _ = verify_pair_weights(graph,weights)
            return (weights^,iteration)
        weights = following^
    raise Error("iteration cap exhausted; inconclusive")
