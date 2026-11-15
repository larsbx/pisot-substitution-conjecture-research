"""Authenticated paired graphs for the twelve orders of 11/012/01.

This incidence is x^3-x^2-3x-2, distinct from #496.  The physical-strip
invariant and compact-attractor/measure implications are written theorems.
Native acceptance checks their finite chart, enclosure, carrier and complete
occurrence obligations; it consumes no strong-coincidence witness.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from finite_exact.closed_interval import IQ
from finite_exact.rat_q import Q
from finite_linear_algebra.mat3 import Mat3, identity3
from finite_linear_algebra.qpoly import add, mul, remainder, scale, sub
from finite_linear_algebra.scalar import q_int
from psc.exact import eval_int_poly_at_q, midpoint, q_poly, require_iq, require_q
from psc.pisot import is_irreducible_cubic, is_pisot_charpoly, is_primitive
from psc.c4_nonunit_residue_occupancy import checked_substitution, inflated_words, same_vector
from psc.c4_finite_cylinder_overlap import interval_abs_upper, interval_hull
from psc.c4_pair_overlap_carrier import (
    CarrierBox, canonical_pair, canonical_pair_index, contains_offset, enclose_inverse_chart,
    hull_carriers, typed_offset_key, validate_carrier,
)

comptime NEW_SCALE = 1000000
comptime NEW_RADIUS_X = 8
comptime NEW_RADIUS_Y = 8
comptime NEW_RATE_NUMERATOR = 125
comptime NEW_RATE_DENOMINATOR = 20
comptime NEW_STATE_BUDGET = 20000
comptime NEW_WEIGHT_LIMIT = 1000000


struct NewChart(Copyable, Movable):
    var beta: IQ
    var a: IQ
    var b: IQ
    var ell: List[IQ]
    var inverse_phi: List[IQ]

    def __init__(out self, beta: IQ, a: IQ, b: IQ, ell: List[IQ], inverse_phi: List[IQ]):
        self.beta = beta.copy()
        self.a = a.copy()
        self.b = b.copy()
        self.ell = ell.copy()
        self.inverse_phi = inverse_phi.copy()


struct NewModel(Copyable, Movable):
    var chart: NewChart
    var rx: Int
    var ry: Int
    var carriers: List[CarrierBox]
    var global_box: CarrierBox
    var capacity: Int

    def __init__(out self, chart: NewChart, rx: Int, ry: Int, carriers: List[CarrierBox], global_box: CarrierBox, capacity: Int):
        self.chart = chart.copy()
        self.rx = rx
        self.ry = ry
        self.carriers = carriers.copy()
        self.global_box = global_box.copy()
        self.capacity = capacity


struct NewIncidenceGraph(Copyable, Movable):
    var source: Int
    var model: NewModel
    var states: List[List[Int]]
    var rows: List[List[Int]]
    var residue_rejections: Int
    var box_rejections: Int
    var carrier_rejections: Int

    def __init__(out self, source: Int, model: NewModel, states: List[List[Int]], rows: List[List[Int]], residue: Int, box: Int, carrier: Int):
        self.source = source
        self.model = model.copy()
        self.states = states.copy()
        self.rows = rows.copy()
        self.residue_rejections = residue
        self.box_rejections = box
        self.carrier_rejections = carrier


def new_source_images(index: Int) raises -> List[List[Int]]:
    if index < 0 or index >= 12:
        raise Error("source outside the complete twelve-order incidence class")
    var middle: List[List[Int]] = [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]]
    var last: List[List[Int]] = [[0,1],[1,0]]
    return [[1,1],middle[index // 2].copy(),last[index % 2].copy()]


def new_matrix() -> Mat3:
    return Mat3([0,1,1,2,1,1,0,1,0])


def new_matrix_power(depth: Int) raises -> Mat3:
    if depth < 0 or depth > 12:
        raise Error("new incidence matrix power outside 0..12")
    # Every column sum is <=3; entries of M^12 are <=3^12.  The
    # fixed-dimension products therefore fit comfortably in 64-bit Int.
    var value = identity3()
    for _ in range(depth):
        value = value * new_matrix()
    return value^


def _zero_mod_new_chi(polynomial: List[Q]) raises:
    var reduced = remainder(polynomial, q_poly([-2,-3,-1,1]))
    for coefficient in reduced:
        if coefficient.rejected or not coefficient.eq(Q.zero()):
            raise Error("false new-incidence polynomial identity")


def _certify_new_chart_algebra() raises:
    var matrix = new_matrix()
    if not same_vector(matrix.charpoly(), [-2,-3,-1,1]) or matrix.det() != 2:
        raise Error("wrong authenticated incidence polynomial")
    if not is_primitive(matrix) or not is_irreducible_cubic(matrix.charpoly()) or not is_pisot_charpoly(matrix.charpoly()):
        raise Error("new incidence did not pass the exact PIP screen")
    var beta = q_poly([0,1])
    var a = scale(q_poly([1,3,-1]), Q(1,4))
    var b = scale(q_poly([-3,-1,1]), Q(1,2))
    var ell = List[List[Q]]()
    ell.append(q_poly([1]))
    ell.append(scale(beta,Q(1,2)))
    ell.append(scale(q_poly([-2,-1,1]),Q(1,2)))
    var f = List[List[Q]]()
    f.append(q_poly([1,1]))
    f.append(q_poly([0,0,1]))
    f.append(beta.copy())
    for i in range(3):
        var image = List[Q]()
        var left_image = List[Q]()
        for j in range(3):
            image = add(image,scale(f[j],q_int(matrix.at(i,j))))
            left_image = add(left_image,scale(ell[j],q_int(matrix.at(j,i))))
        _zero_mod_new_chi(sub(image,mul(beta,f[i])))
        _zero_mod_new_chi(sub(left_image,mul(beta,ell[i])))
    _zero_mod_new_chi(sub(f[0],mul(a,f[1])))
    _zero_mod_new_chi(sub(f[2],mul(b,f[1])))
    _zero_mod_new_chi(sub(mul(beta,b),q_poly([1])))
    # WM=BW for B=[[-2a,1-a],[-2b,-b]].  Its only nontrivial
    # column identities are displayed here, using the actual chart.
    _zero_mod_new_chi(sub(add(sub(scale(mul(a,a),q_int(2)),b),mul(a,b)),sub(q_poly([1]),a)))
    _zero_mod_new_chi(sub(add(scale(mul(a,b),q_int(2)),mul(b,b)),sub(q_poly([1]),b)))
    var d = add(scale(a,q_int(3)),q_poly([0]))
    d = add(d,scale(q_poly([1]),Q(1,2)))
    _zero_mod_new_chi(sub(add(add(a,ell[1]),mul(ell[2],b)),d))
    _zero_mod_new_chi(sub(mul(a,ell[2]),scale(q_poly([1]),Q(1,2))))


def make_new_chart() raises -> NewChart:
    _certify_new_chart_algebra()
    var lo = q_int(2)
    var hi = q_int(3)
    for _ in range(48):
        var mid = midpoint(lo,hi)
        var value = eval_int_poly_at_q([-2,-3,-1,1],mid)
        if value.lt(Q.zero()):
            lo = mid^
        else:
            hi = mid^
    if not eval_int_poly_at_q([-2,-3,-1,1],lo).lt(Q.zero()) or not Q.zero().lt(eval_int_poly_at_q([-2,-3,-1,1],hi)):
        raise Error("new Perron bracket must have strict endpoint signs")
    var beta = require_iq(IQ(lo,hi),"new Perron bracket")
    var a = require_iq(IQ.singleton(q_int(1)).add(beta.mul(IQ.singleton(q_int(3)))).sub(beta.square()).mul(IQ.singleton(Q(1,4))),"new chart a")
    var b = require_iq(beta.square().sub(beta).sub(IQ.singleton(q_int(3))).mul(IQ.singleton(Q(1,2))),"new chart b")
    if not Q(556693,NEW_SCALE).le(a.lo) or not a.hi.le(Q(556694,NEW_SCALE)):
        raise Error("new a interval outside the authenticated integer pruning bounds")
    if not Q(398160,NEW_SCALE).le(b.lo) or not b.hi.le(Q(398161,NEW_SCALE)):
        raise Error("new b interval outside the authenticated integer pruning bounds")
    if not Q(63,10).lt(require_iq(beta.square(),"new beta squared").lo):
        raise Error("new exact spectral threshold did not separate")
    var ell = List[IQ]()
    ell.append(IQ.singleton(Q.one()))
    ell.append(require_iq(beta.mul(IQ.singleton(Q(1,2))),"new ell1"))
    ell.append(require_iq(b.add(IQ.singleton(Q(1,2))),"new ell2"))
    for entry in ell:
        if not Q.zero().lt(entry.lo):
            raise Error("positive Perron lengths required")
    var d = require_iq(a.mul(IQ.singleton(q_int(3))).add(IQ.singleton(Q(1,2))),"inverse chart determinant")
    if not Q.zero().lt(d.lo):
        raise Error("inverse chart determinant must exclude zero")
    var inverse_d = require_iq(d.reciprocal(),"inverse chart reciprocal")
    var a_over_d = require_iq(a.mul(inverse_d),"inverse a/d")
    var b_over_d = require_iq(b.mul(inverse_d),"inverse b/d")
    var ell2_over_d = require_iq(ell[2].mul(inverse_d),"inverse ell2/d")
    var inverse_phi = List[IQ]()
    inverse_phi.append(a_over_d.copy())
    inverse_phi.append(require_iq(IQ.singleton(Q.one()).sub(a_over_d),"inverse 00 stable coefficient"))
    # a*ell2=1/2 is authenticated above; avoid dependency overestimation.
    inverse_phi.append(require_iq(inverse_d.mul(IQ.singleton(Q(-1,2))),"inverse 02"))
    inverse_phi.append(inverse_d.copy())
    inverse_phi.append(require_iq(inverse_d.neg(),"inverse 11"))
    inverse_phi.append(require_iq(ell2_over_d.neg(),"inverse 12"))
    inverse_phi.append(b_over_d.copy())
    inverse_phi.append(require_iq(b_over_d.neg(),"inverse 21"))
    inverse_phi.append(require_iq(IQ.singleton(Q.one()).sub(b.mul(ell2_over_d)),"inverse 22"))
    return NewChart(beta,a,b,ell,inverse_phi)


def make_new_model(rx: Int = NEW_RADIUS_X, ry: Int = NEW_RADIUS_Y) raises -> NewModel:
    if rx < 1 or rx > 32 or ry < 1 or ry > 32:
        raise Error("new model radius outside bounded domain 1..32")
    var chart = make_new_chart()
    var carriers = List[CarrierBox]()
    var capacity = 0
    for first in range(3):
        for second in range(first,3):
            var axes = List[IQ]()
            # The strict strip is relaxed to these closed interval endpoints.
            axes.append(require_iq(IQ(chart.ell[first].hi.neg(),chart.ell[second].hi),"typed physical strip"))
            axes.append(IQ(q_int(-2*rx),q_int(2*rx)))
            axes.append(IQ(q_int(-2*ry),q_int(2*ry)))
            var box = enclose_inverse_chart(chart.inverse_phi,axes)
            capacity = checked_add(capacity,box.capacity)
            carriers.append(box^)
    var global_box = hull_carriers(carriers)
    return NewModel(chart,rx,ry,carriers,global_box,capacity)


def new_project(chart: NewChart, vector: List[Int], coordinate: Int) raises -> IQ:
    if len(vector) != 3 or coordinate < 0 or coordinate > 1:
        raise Error("new projection dimensions")
    for entry in vector:
        if entry < -1000000000 or entry > 1000000000:
            raise Error("new projection coordinate budget")
    var coefficient = chart.a.copy() if coordinate == 0 else chart.b.copy()
    var entry = vector[0] if coordinate == 0 else vector[2]
    return require_iq(IQ.singleton(q_int(entry)).sub(coefficient.mul(IQ.singleton(q_int(vector[1])))),"new projected coordinate")


def _certify_new_source_box(index: Int, model: NewModel) raises:
    # Internal caller has just constructed the chart; no serialized chart is
    # admitted.  Every source is reconstructed and its incidence authenticated.
    var images = new_source_images(index)
    var sigma = checked_substitution(images)
    if not same_vector(sigma.incidence(),new_matrix().e):
        raise Error("source incidence differs from the new authenticated matrix")
    for start in range(3):
        var seen: List[Int] = [-1,-1,-1]
        var letter = start
        var length = 0
        while seen[letter] < 0:
            seen[letter] = length
            length += 1
            letter = images[letter][0]
        var period = length-seen[letter]
        if period < 1 or 12 % period != 0:
            raise Error("prefix period is incompatible with the common block")
    var entry_bounds: List[Q] = [Q(313,1000),Q(103,1000),Q(184,1000),Q(148,1000)]
    var power12 = new_matrix_power(12)
    for coordinate in range(2):
        for j in range(2):
            var column = 0 if j == 0 else 2
            var projected = new_project(model.chart,[power12.at(0,column),power12.at(1,column),power12.at(2,column)],coordinate)
            if not interval_abs_upper(projected).le(entry_bounds[2*coordinate+j]):
                raise Error("new stable block entry exceeds its exact rational bound")
    # Complete prefix-hull recursion, independently compared with direct
    # literal prefix enumeration by the Python oracle.
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
                    var shift = new_project(model.chart,power.apply(prefix),coordinate)
                    var translated = require_iq(shift.add(hulls[2*letter+coordinate]),"new block digit")
                    if position == 0:
                        aggregate = translated^
                    else:
                        aggregate = interval_hull(aggregate,translated)
                    prefix[letter] += 1
                next_hulls.append(aggregate^)
        hulls = next_hulls^
        power = power*new_matrix()
    var digits: List[Q] = [Q(41,10),Q(24,5)]
    for source in range(3):
        for coordinate in range(2):
            if not interval_abs_upper(hulls[2*source+coordinate]).le(digits[coordinate]):
                raise Error("complete new prefix hull exceeds the common digit bound")
    var radii: List[Int] = [model.rx,model.ry]
    for i in range(2):
        var linear = require_q(entry_bounds[2*i].mul(q_int(model.rx)).add(entry_bounds[2*i+1].mul(q_int(model.ry))),"new weighted block bound")
        if not linear.lt(q_int(radii[i])) or not linear.add(digits[i]).le(q_int(radii[i])):
            raise Error("new box invariance or strict contraction failed")


def outside_new_box(offset: List[Int], rx: Int = NEW_RADIUS_X, ry: Int = NEW_RADIUS_Y) raises -> Bool:
    if len(offset) != 3 or rx < 1 or rx > 32 or ry < 1 or ry > 32:
        raise Error("new box exclusion input shape")
    var entries: List[Int] = [offset[0],offset[2]]
    var lower: List[Int] = [556693,398160]
    var upper: List[Int] = [556694,398161]
    var limits: List[Int] = [2*rx*NEW_SCALE,2*ry*NEW_SCALE]
    for i in range(2):
        var first = checked_sub(checked_mul(NEW_SCALE,entries[i]),checked_mul(lower[i],offset[1]))
        var second = checked_sub(checked_mul(NEW_SCALE,entries[i]),checked_mul(upper[i],offset[1]))
        if (first > limits[i] and second > limits[i]) or (first < -limits[i] and second < -limits[i]):
            return True
    return False


def _check_new_state(state: List[Int], model: NewModel) raises:
    if len(state) != 5:
        raise Error("new paired state must have five entries")
    var pair = canonical_pair_index(state[0],state[1])
    if not contains_offset(model.carriers[pair],[state[2],state[3],state[4]]):
        raise Error("state is outside its typed proved carrier")
    if not same_vector(state,canonical_pair(state[0],state[1],state[2],state[3],state[4])):
        raise Error("noncanonical new paired state")


def build_new_incidence_graph(index: Int, state_cap: Int = NEW_STATE_BUDGET, rx: Int = NEW_RADIUS_X, ry: Int = NEW_RADIUS_Y) raises -> NewIncidenceGraph:
    var images = new_source_images(index)
    var model = make_new_model(rx,ry)
    if state_cap < 3 or state_cap > 200000 or state_cap > model.capacity:
        raise Error("new graph operational budget outside its admitted domain")
    _certify_new_source_box(index,model)
    var words = inflated_words(images,2)
    var digits = List[List[Int]]()
    for source in range(3):
        var prefix: List[Int] = [0,0,0]
        for position in range(len(words[source])):
            digits.append([words[source][position],source,position,prefix[0],prefix[1],prefix[2]])
            prefix[words[source][position]] += 1
    if len(digits) != 18:
        raise Error("wrong complete new two-step occurrence count")
    var square = new_matrix_power(2)
    if square.det() != 4:
        raise Error("new two-step quotient index is not four")
    var inverse_numerator = square.adjugate()
    var states: List[List[Int]] = [[0,1,0,0,0],[0,2,0,0,0],[1,2,0,0,0]]
    var lookup = Dict[Int,Int]()
    for i in range(3):
        _check_new_state(states[i],model)
        lookup[typed_offset_key(model.global_box,states[i][0],states[i][1],[0,0,0])] = i
    var rows = List[List[Int]]()
    var residue_rejections = 0
    var box_rejections = 0
    var carrier_rejections = 0
    var cursor = 0
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
                    checked_sub(checked_add(state[2],digits[j][3]),digits[i][3]),
                    checked_sub(checked_add(state[3],digits[j][4]),digits[i][4]),
                    checked_sub(checked_add(state[4],digits[j][5]),digits[i][5]),
                ]
                var values = List[Int]()
                for coordinate in range(3):
                    var total = 0
                    for k in range(3):
                        total = checked_add(total,checked_mul(inverse_numerator.at(coordinate,k),delta[k]))
                    values.append(total)
                if values[0] % 4 != 0 or values[1] % 4 != 0 or values[2] % 4 != 0:
                    residue_rejections = checked_add(residue_rejections,1)
                    continue
                var raw: List[Int] = [values[0]//4,values[1]//4,values[2]//4]
                # Required order: exact integrality, certified stable exclusion,
                # then the proved reachable carrier.  Contact stays in the graph.
                if outside_new_box(raw,rx,ry):
                    box_rejections = checked_add(box_rejections,1)
                    continue
                var child = canonical_pair(digits[i][1],digits[j][1],raw[0],raw[1],raw[2])
                var offset: List[Int] = [child[2],child[3],child[4]]
                var pair = canonical_pair_index(child[0],child[1])
                if not contains_offset(model.carriers[pair],offset):
                    carrier_rejections = checked_add(carrier_rejections,1)
                    continue
                var key = typed_offset_key(model.global_box,child[0],child[1],offset)
                var target = len(states)
                if key in lookup:
                    target = lookup[key]
                else:
                    if len(states) >= state_cap:
                        raise Error("new graph operational state budget exhausted; inconclusive")
                    lookup[key] = target
                    states.append(child^)
                targets.append(target)  # Every actual paired occurrence counts.
        if len(targets) > 81:
            raise Error("new paired-occurrence row exceeded its literal maximum")
        rows.append(targets^)
        cursor += 1
    return NewIncidenceGraph(index,model,states,rows,residue_rejections,box_rejections,carrier_rejections)


def _validate_graph_structure(graph: NewIncidenceGraph) raises:
    if graph.source < 0 or graph.source >= 12 or len(graph.states) < 3 or len(graph.states) > 200000 or len(graph.rows) != len(graph.states):
        raise Error("new graph shape or source domain")
    if graph.model.rx < 1 or graph.model.rx > 32 or graph.model.ry < 1 or graph.model.ry > 32 or len(graph.model.carriers) != 6:
        raise Error("new graph model dimensions")
    if len(graph.model.chart.ell) != 3 or len(graph.model.chart.inverse_phi) != 9:
        raise Error("new graph chart dimensions")
    var capacity = 0
    for box in graph.model.carriers:
        validate_carrier(box)
        capacity = checked_add(capacity,box.capacity)
    if capacity != graph.model.capacity:
        raise Error("new graph carrier capacity metadata")
    validate_carrier(graph.model.global_box)
    for state in graph.states:
        _check_new_state(state,graph.model)
    for row in graph.rows:
        if len(row) > 81:
            raise Error("new graph row exceeds the literal occurrence bound")
        for target in row:
            if target < 0 or target >= len(graph.states):
                raise Error("new graph target outside its state inventory")


def authenticate_new_graph(graph: NewIncidenceGraph) raises:
    _validate_graph_structure(graph)
    var canonical = build_new_incidence_graph(graph.source,200000 if graph.model.capacity >= 200000 else graph.model.capacity,graph.model.rx,graph.model.ry)
    if graph.model.capacity != canonical.model.capacity or not same_vector(graph.model.global_box.lower,canonical.model.global_box.lower) or not same_vector(graph.model.global_box.upper,canonical.model.global_box.upper):
        raise Error("new graph global carrier metadata differs from canonical arithmetic")
    var submitted: List[IQ] = [graph.model.chart.beta.copy(),graph.model.chart.a.copy(),graph.model.chart.b.copy()]
    var expected: List[IQ] = [canonical.model.chart.beta.copy(),canonical.model.chart.a.copy(),canonical.model.chart.b.copy()]
    for i in range(3):
        submitted.append(graph.model.chart.ell[i].copy())
        expected.append(canonical.model.chart.ell[i].copy())
    for i in range(9):
        submitted.append(graph.model.chart.inverse_phi[i].copy())
        expected.append(canonical.model.chart.inverse_phi[i].copy())
    for i in range(len(submitted)):
        if submitted[i].rejected or not submitted[i].lo.eq(expected[i].lo) or not submitted[i].hi.eq(expected[i].hi):
            raise Error("new graph chart differs from authenticated normalization")
    for i in range(6):
        if not same_vector(graph.model.carriers[i].lower,canonical.model.carriers[i].lower) or not same_vector(graph.model.carriers[i].upper,canonical.model.carriers[i].upper):
            raise Error("new typed carrier differs from canonical arithmetic")
    if len(graph.states) != len(canonical.states) or graph.residue_rejections != canonical.residue_rejections or graph.box_rejections != canonical.box_rejections or graph.carrier_rejections != canonical.carrier_rejections:
        raise Error("new graph does not reproduce the complete canonical closure")
    for i in range(len(graph.states)):
        if not same_vector(graph.states[i],canonical.states[i]) or not same_vector(graph.rows[i],canonical.rows[i]):
            raise Error("new graph state or occurrence row differs from canonical reconstruction")


def verify_new_rate(numerator: Int, denominator: Int) raises:
    if numerator < 1 or numerator > 10000 or denominator < 1 or denominator > 1000:
        raise Error("new graph rate outside the bounded positive rational domain")
    # The authenticated chart proves beta^2>63/10.  Equality with that
    # rational lower bound is conservatively refused by this certificate.
    if not Q(Int64(numerator),Int64(denominator)).lt(Q(63,10)):
        raise Error("new rate lacks strict certified spectral separation")


def verify_new_weights(graph: NewIncidenceGraph, weights: List[Int], numerator: Int = NEW_RATE_NUMERATOR, denominator: Int = NEW_RATE_DENOMINATOR) raises -> Int:
    # This checks finite inequalities; authenticate_new_graph is the separate
    # entry point for a submitted graph's complete-occurrence semantics.
    verify_new_rate(numerator,denominator)
    _validate_graph_structure(graph)
    if len(weights) != len(graph.states):
        raise Error("new positive weight dimensions")
    for weight in weights:
        if weight < 1 or weight > NEW_WEIGHT_LIMIT:
            raise Error("new weights must be positive bounded integers")
    var minimum_gap = Int.MAX
    for i in range(len(weights)):
        var total = 0
        for target in graph.rows[i]:
            total = checked_add(total,weights[target])
        var gap = checked_sub(checked_mul(numerator,weights[i]),checked_mul(denominator,total))
        if gap < 0:
            raise Error("false new exact subinvariant inequality")
        if gap < minimum_gap:
            minimum_gap = gap
    return minimum_gap


def construct_new_weights(graph: NewIncidenceGraph, numerator: Int = NEW_RATE_NUMERATOR, denominator: Int = NEW_RATE_DENOMINATOR, iteration_cap: Int = 4000) raises -> Tuple[List[Int],Int]:
    verify_new_rate(numerator,denominator)
    _validate_graph_structure(graph)
    if iteration_cap < 1 or iteration_cap > 10000:
        raise Error("new ordered weight sweep budget")
    var weights = List[Int]()
    for _ in range(len(graph.states)):
        weights.append(1)
    for sweep in range(1,iteration_cap+1):
        var unchanged = True
        for i in range(len(weights)):
            var total = 0
            for target in graph.rows[i]:
                total = checked_add(total,weights[target])
            var rounded = checked_add(checked_mul(denominator,total),numerator-1)//numerator
            var value = checked_add(1,rounded)
            if value > NEW_WEIGHT_LIMIT:
                raise Error("new weight budget exhausted; inconclusive")
            if value < weights[i]:
                raise Error("impossible nonmonotone new weight iteration")
            if value != weights[i]:
                unchanged = False
                weights[i] = value
        if unchanged:
            _ = verify_new_weights(graph,weights,numerator,denominator)
            return (weights^,sweep)
    raise Error("new iteration budget exhausted; inconclusive")


def _rational_power(base: Q, exponent: Int) raises -> Q:
    _ = require_q(base,"finite overlap bound base")
    if exponent < 0 or exponent > 126:
        raise Error("finite overlap power outside its small checked budget")
    var result = Q.one()
    var factor = base.copy()
    var remaining = exponent
    while remaining > 0:
        if remaining % 2 == 1:
            result = require_q(result.mul(factor),"finite overlap power product")
        remaining //= 2
        if remaining > 0:
            factor = require_q(factor.square(),"finite overlap power square")
    return result^


def certify_uniform_upper_tenth() raises:
    # With Q=[-8,8]^2, w<=10^6 and beta^2>126/20, every root
    # is bounded by 256*10^6*(125/126)^3072.  This small exact
    # certificate avoids constructing powers with thousands of digits:
    # (125/126)^126<3/8 and 3072>=24*126, with 0<125/126<1.
    if not _rational_power(Q(125,126),126).lt(Q(3,8)):
        raise Error("finite overlap block contraction failed")
    var bound = require_q(q_int(256).mul(q_int(NEW_WEIGHT_LIMIT)).mul(_rational_power(Q(3,8),24)),"uniform finite overlap upper")
    if not bound.lt(Q(1,10)):
        raise Error("finite overlap upper bound is not below one tenth")
