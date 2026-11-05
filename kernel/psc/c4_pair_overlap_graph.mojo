"""Complete compact M-adic pair graphs for #495 and all 18 source orders.

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
    _certify_source_box(fixture_images(fixture), [16,8], [Q(23,5),Q(14,5)])


def _certify_source_box(images: List[List[Int]], radii: List[Int], digits: List[Q]) raises:
    if len(images) != 3 or len(radii) != 2 or len(digits) != 2:
        raise Error("source enclosure dimensions")
    for i in range(3):
        if len(images[i]) < 1 or len(images[i]) > 3:
            raise Error("unsupported source length")
        for c in images[i]:
            if c < 0 or c >= 3:
                raise Error("source letter before prefix indexing")
    var chart = make_chart()
    if not Q(828911,SCALE).le(chart.a.lo) or not chart.a.hi.le(Q(828912,SCALE)):
        raise Error("pair chart a interval")
    if not Q(440619,SCALE).le(chart.b.lo) or not chart.b.hi.le(Q(440620,SCALE)):
        raise Error("pair chart b interval")
    var square = require_iq(chart.beta.square(), "beta squared")
    if not Q(103,20).lt(square.lo):
        raise Error("insufficient certified spectral gap")
    var cube = require_iq(square.mul(chart.beta), "beta cubed")
    if not Q(292,25).lt(cube.lo):
        raise Error("insufficient three-step spectral gap")
    var power12 = matrix_power(12)
    var entry_bounds: List[Q] = [Q(473,1000),Q(390,1000),Q(147,1000),Q(344,1000)]
    for coordinate in range(2):
        for j in range(2):
            var col = 0 if j == 0 else 2
            var value = project_coordinate(chart, [power12.at(0,col),power12.at(1,col),power12.at(2,col)], coordinate)
            if not interval_abs_upper(value).le(entry_bounds[2*coordinate+j]):
                raise Error("stable block entry exceeds certified bound")
    # Same complete proper-prefix recursion as #495, with coordinate bounds.
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
        if not interval_abs_upper(hulls[2*source]).le(digits[0]):
            raise Error("x digit bound missing an occurrence")
        if not interval_abs_upper(hulls[2*source+1]).le(digits[1]):
            raise Error("y digit bound missing an occurrence")
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
    return outside_source_box(x,y,z,16,8)


def outside_source_box(x: Int, y: Int, z: Int, rx: Int, ry: Int) -> Bool:
    var coordinates: List[Int] = [x,z]
    var lower: List[Int] = [828911,440619]
    var upper: List[Int] = [828912,440620]
    var limits: List[Int] = [2*rx*SCALE,2*ry*SCALE]
    for i in range(2):
        var first = SCALE*coordinates[i]-lower[i]*y
        var second = SCALE*coordinates[i]-upper[i]*y
        if (first > limits[i] and second > limits[i]) or (first < -limits[i] and second < -limits[i]):
            return True
    return False


def state_key(state: List[Int]) raises -> Int:
    return bounded_state_key(state,COORD_LIMIT)


def bounded_state_key(state: List[Int], limit: Int) raises -> Int:
    if limit < 1 or limit > 64:
        raise Error("unsupported coordinate budget")
    if len(state) != 5 or state[0] < 0 or state[0] > 2 or state[1] < 0 or state[1] > 2:
        raise Error("pair state shape")
    var key = 3*state[0]+state[1]
    for i in range(2,5):
        if state[i] < -limit or state[i] > limit:
            raise Error("coordinate budget exhausted; inconclusive")
        key = (2*limit+1)*key+state[i]+limit
    return key


def build_pair_graph(fixture: Int, state_cap: Int = STATE_LIMIT) raises -> PairGraph:
    if fixture < 0 or fixture > 1 or state_cap < 3 or state_cap > STATE_LIMIT:
        raise Error("unsupported fixture or state budget")
    certify_pair_box(fixture)
    return _build_source_graph(fixture_images(fixture),fixture,2,[16,8],state_cap,32)


def _build_source_graph(
    images: List[List[Int]], label: Int, step: Int, radii: List[Int],
    state_cap: Int, coord_cap: Int,
) raises -> PairGraph:
    # Private theorem-facing callers authenticate source, box and period first.
    if step < 2 or step > 3 or state_cap < 3 or state_cap > 20000:
        raise Error("unsupported source graph budget")
    if len(radii) != 2 or radii[0] < 1 or radii[0] > 24 or radii[1] < 1 or radii[1] > 12:
        raise Error("unsupported source box")
    if coord_cap < 1 or coord_cap > 64:
        raise Error("coordinate cap domain")
    var words = inflated_words(images,step)
    # Records are [following letter, source, literal position, p0,p1,p2].
    var digits = List[List[Int]]()
    for source in range(3):
        var p: List[Int] = [0,0,0]
        for position in range(len(words[source])):
            var letter = words[source][position]
            digits.append([letter,source,position,p[0],p[1],p[2]])
            p[letter] += 1
    var lookup = List[Int]()
    for _ in range(9*(2*coord_cap+1)*(2*coord_cap+1)*(2*coord_cap+1)):
        lookup.append(-1)
    var states: List[List[Int]] = [[0,1,0,0,0],[0,2,0,0,0],[1,2,0,0,0]]
    for i in range(3):
        lookup[bounded_state_key(states[i],coord_cap)] = i
    var rows = List[List[Int]]()
    var cursor = 0
    var residue_rejections = 0
    var box_rejections = 0
    var inverse_numerator = matrix_power(step).adjugate()
    var quotient_index = 4 if step == 2 else 8
    if matrix_power(step).det() != quotient_index:
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
                if values[0] % quotient_index != 0 or values[1] % quotient_index != 0 or values[2] % quotient_index != 0:
                    residue_rejections += 1
                    continue
                var x = values[0] // quotient_index
                var y = values[1] // quotient_index
                var z = values[2] // quotient_index
                if outside_source_box(x,y,z,radii[0],radii[1]):
                    box_rejections += 1
                    continue
                var child = canonical_pair(digits[i][1],digits[j][1],x,y,z)
                var key = bounded_state_key(child,coord_cap)
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
    return PairGraph(label,states,rows,residue_rejections,box_rejections)


def verify_pair_weights(graph: PairGraph, weights: List[Int]) raises -> Int:
    if graph.fixture < 0 or graph.fixture > 1:
        raise Error("legacy fixture domain")
    var numerator = 99 if graph.fixture == 0 else 101
    return verify_weights_at_rate(graph,weights,numerator,2)


def verify_weights_at_rate(graph: PairGraph, weights: List[Int], numerator: Int, step: Int) raises -> Int:
    # Finite inequalities only; admission must reconstruct the complete graph.
    if len(weights) < 1 or len(weights) != len(graph.states) or len(graph.rows) != len(weights):
        raise Error("weight dimensions")
    if numerator < 1 or numerator > 1000 or (step != 2 and step != 3):
        raise Error("rate domain")
    if (step == 2 and numerator >= 103) or (step == 3 and 25*numerator >= 292*20):
        raise Error("rate lacks strict certified spectral separation")
    for w in weights:
        if w < 1 or w > 1000000:
            raise Error("positive bounded integer weights required")
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
    if graph.fixture < 0 or graph.fixture > 1:
        raise Error("legacy fixture domain")
    return construct_weights_at_rate(graph,99 if graph.fixture == 0 else 101,2,iteration_cap)


def construct_weights_at_rate(graph: PairGraph, numerator: Int, step: Int, iteration_cap: Int = 4000) raises -> Tuple[List[Int],Int]:
    if iteration_cap < 1 or iteration_cap > 4000:
        raise Error("weight iteration budget")
    _ = verify_rate_domain(numerator,step)
    if len(graph.states) < 1 or len(graph.states) > 20000 or len(graph.rows) != len(graph.states):
        raise Error("graph dimensions before weight iteration")
    for i in range(len(graph.rows)):
        if len(graph.rows[i]) > 1024:
            raise Error("row occurrence budget")
        for j in graph.rows[i]:
            if j < 0 or j >= len(graph.states):
                raise Error("invalid target before weight indexing")
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
            _ = verify_weights_at_rate(graph,weights,numerator,step)
            return (weights^,iteration)
        weights = following^
    raise Error("iteration cap exhausted; inconclusive")


def verify_rate_domain(numerator: Int, step: Int) raises -> Bool:
    if numerator < 1 or numerator > 1000 or (step != 2 and step != 3):
        raise Error("unsupported rate/step")
    if (step == 2 and numerator >= 103) or (step == 3 and 25*numerator >= 292*20):
        raise Error("missing strict spectral separation")
    return True


def source_class_images(index: Int) raises -> List[List[Int]]:
    if index < 0 or index >= 18:
        raise Error("source outside complete 18-element incidence class")
    var middle: List[List[Int]] = [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]
    var last: List[List[Int]] = [[0,0,1],[0,1,0],[1,0,0]]
    return [[1],middle[index // 3].copy(),last[index % 3].copy()]


def source_class_step(index: Int) raises -> Int:
    var images = source_class_images(index)
    var first_seen: List[Int] = [-1,-1,-1]
    var c = 0
    var length = 0
    while first_seen[c] < 0:
        first_seen[c] = length
        c = images[c][0]
        length += 1
    var period = length-first_seen[c]
    if period == 1 or period == 2:
        return 2
    if period == 3:
        return 3
    raise Error("unsupported prefix period")


def build_source_class_graph(index: Int, requested_step: Int = 0, state_cap: Int = 20000) raises -> PairGraph:
    var images = source_class_images(index)
    var step = source_class_step(index)
    if requested_step != 0 and requested_step != step:
        raise Error("unauthenticated fixed-point step")
    _certify_source_box(images,[24,12],[Q(13,2),Q(4,1)])
    return _build_source_graph(images,index,step,[24,12],state_cap,64)
