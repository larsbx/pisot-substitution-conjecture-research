"""Literal occurrence identities for the archived twelve-source inverse graphs.

The canonical constructor remains unchanged.  This adapter reconstructs the
complete *internal* incoming inventory from actual sigma^2 words, without using
the constructor's stable-box or carrier filters.  It retains normalization
orientation and independently checks the ordered forward inventory.

This is a finite source binding.  It does not certify compact overlap cover,
the geometric emptiness of excluded pieces, or positive compact measure.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_mul, checked_neg, checked_sub
from finite_linear_algebra.mat3 import Mat3
from psc.c4_nonunit_residue_occupancy import inflated_words, same_vector
from psc.c4_pair_overlap_carrier import canonical_pair
from psc.c4_pair_overlap_new_incidence import (
    NEW_STATE_BUDGET, NewIncidenceGraph, authenticate_new_graph,
    build_new_incidence_graph, new_matrix_power, new_source_images,
)

comptime BINDING_COORDINATE_BOUND = 64
comptime BINDING_DIGIT_COUNT = 18


struct LiteralInverseBinding(Copyable, Movable):
    var graph: NewIncidenceGraph
    var images: List[List[Int]]
    var words: List[List[Int]]
    var digits: List[List[Int]]
    # Per source row, each slot is [target, topDigit, bottomDigit, swapped].
    var slots: List[List[List[Int]]]
    # Roots have [-1,-1]; other entries are [earlier row, exact row slot].
    var births: List[List[Int]]
    var edges: Int
    var swapped: Int
    var repeated: Int

    def __init__(out self, graph: NewIncidenceGraph, images: List[List[Int]], words: List[List[Int]], digits: List[List[Int]], slots: List[List[List[Int]]], births: List[List[Int]], edges: Int, swapped: Int, repeated: Int):
        self.graph = graph.copy()
        self.images = images.copy()
        self.words = words.copy()
        self.digits = digits.copy()
        self.slots = slots.copy()
        self.births = births.copy()
        self.edges = edges
        self.swapped = swapped
        self.repeated = repeated


def swap_packet(packet: List[Int]) raises -> List[Int]:
    if len(packet) != 5:
        raise Error("literal packet must contain two letters and three coordinates")
    return [packet[1],packet[0],checked_neg(packet[2]),checked_neg(packet[3]),checked_neg(packet[4])]


def _inside_key_box(packet: List[Int]) raises -> Bool:
    if len(packet) != 5 or packet[0] < 0 or packet[0] > 2 or packet[1] < 0 or packet[1] > 2:
        raise Error("literal packet labels or shape")
    for k in range(2,5):
        if packet[k] < -BINDING_COORDINATE_BOUND or packet[k] > BINDING_COORDINATE_BOUND:
            return False
    return True


def packet_key(packet: List[Int]) raises -> Int:
    if not _inside_key_box(packet):
        raise Error("literal packet coordinate budget exhausted; inconclusive")
    var key = checked_add(checked_mul(packet[0],3),packet[1])
    for k in range(2,5):
        key = checked_add(checked_mul(key,2*BINDING_COORDINATE_BOUND+1),checked_add(packet[k],BINDING_COORDINATE_BOUND))
    return key


def literal_digits(words: List[List[Int]]) raises -> List[List[Int]]:
    if len(words) != 3:
        raise Error("literal word inventory must have three source letters")
    var digits = List[List[Int]]()
    var square = new_matrix_power(2)
    for parent in range(3):
        var prefix: List[Int] = [0,0,0]
        if len(words[parent]) < 1 or len(words[parent]) > BINDING_DIGIT_COUNT:
            raise Error("literal word outside its nonempty bounded domain")
        for position in range(len(words[parent])):
            var selected = words[parent][position]
            if selected < 0 or selected > 2:
                raise Error("literal word contains a nonletter")
            digits.append([selected,parent,position,prefix[0],prefix[1],prefix[2]])
            prefix[selected] = checked_add(prefix[selected],1)
        for letter in range(3):
            if prefix[letter] != square.at(letter,parent):
                raise Error("literal iterate incidence differs from M squared")
    if len(digits) != BINDING_DIGIT_COUNT or square.det() != 4:
        raise Error("literal two-step digits or determinant mismatch")
    return digits^


def exact_inverse_ancestor(packet: List[Int], top: List[Int], bottom: List[Int], square: Mat3, inverse_numerator: Mat3) raises -> List[Int]:
    """Empty means no integral preimage; never a rounded candidate.

    The caller supplies authenticated literal marks, M^2 and adj(M^2). Their
    provenance is rechecked by the public binding verifier.
    """
    if len(packet) != 5 or len(top) != 6 or len(bottom) != 6:
        raise Error("literal inverse candidate shape")
    if top[0] != packet[0] or bottom[0] != packet[1]:
        raise Error("incoming marks do not select the current packet letters")
    var rhs = List[Int]()
    for k in range(3):
        rhs.append(checked_sub(checked_add(packet[k+2],bottom[k+3]),top[k+3]))
    var raw: List[Int] = [top[1],bottom[1]]
    for row in range(3):
        var numerator = 0
        for k in range(3):
            numerator = checked_add(numerator,checked_mul(inverse_numerator.at(row,k),rhs[k]))
        if numerator % 4 != 0:
            return List[Int]()
        raw.append(numerator//4)
    # Verify the original integral equation, not merely the adjugate division.
    for row in range(3):
        var value = 0
        for k in range(3):
            value = checked_add(value,checked_mul(square.at(row,k),raw[k+2]))
        if value != rhs[row]:
            raise Error("literal inverse candidate violates the original equation")
    return raw^


def _edge_key(start: Int, top: Int, bottom: Int, target: Int, size: Int) raises -> Int:
    if size < 3 or size > NEW_STATE_BUDGET or start < 0 or start >= 2*size or target < 0 or target >= 2*size:
        raise Error("ordered literal edge endpoint budget")
    if top < 0 or top >= BINDING_DIGIT_COUNT or bottom < 0 or bottom >= BINDING_DIGIT_COUNT:
        raise Error("ordered literal edge position budget")
    return checked_add(checked_mul(checked_add(checked_mul(checked_add(checked_mul(start,BINDING_DIGIT_COUNT),top),BINDING_DIGIT_COUNT),bottom),2*size),target)


def _increment(mut counts: Dict[Int,Int], key: Int) raises:
    if key in counts:
        counts[key] = checked_add(counts[key],1)
    else:
        counts[key] = 1


def verify_ordered_forward_inventory(graph: NewIncidenceGraph, words: List[List[Int]], digits: List[List[Int]], slots: List[List[List[Int]]]) raises:
    """Compare every lifted inverse slot with direct forward word positions.

    The direct scan uses M^2*y+prefix(top)-prefix(bottom), with no inverse
    calculation and no stable-box/carrier predicate.  It also compares the
    canonical incoming matrix with the transpose of canonical forward counts.
    """
    var size = len(graph.states)
    var ordered = Dict[Int,Int]()
    for index in range(size):
        var key = packet_key(graph.states[index])
        var other_key = packet_key(swap_packet(graph.states[index]))
        if key == other_key or key in ordered or other_key in ordered:
            raise Error("ordered domain has fixed swaps or duplicate orbits")
        ordered[key] = 2*index
        ordered[other_key] = 2*index+1
    var inverse_edges = Dict[Int,Int]()
    var transposed_counts = Dict[Int,Int]()
    for row in range(size):
        for slot in slots[row]:
            var target = slot[0]
            var top = digits[slot[1]][2]
            var bottom = digits[slot[2]][2]
            var orientation = slot[3]
            var key = _edge_key(2*target+orientation,top,bottom,2*row,size)
            var mate = _edge_key(2*target+1-orientation,bottom,top,2*row+1,size)
            if key in inverse_edges or mate in inverse_edges or key == mate:
                raise Error("duplicate actual occurrence in ordered inverse lift")
            inverse_edges[key] = 1
            inverse_edges[mate] = 1
            _increment(transposed_counts,checked_add(checked_mul(target,size),row))
    var digit_start: List[Int] = [0,len(words[0]),len(words[0])+len(words[1])]
    var square = new_matrix_power(2)
    var forward_counts = Dict[Int,Int]()
    var seen = 0
    for index in range(size):
        for orientation in range(2):
            var parent = graph.states[index].copy() if orientation == 0 else swap_packet(graph.states[index])
            var base: List[Int] = [0,0,0]
            for row in range(3):
                for k in range(3):
                    base[row] = checked_add(base[row],checked_mul(square.at(row,k),parent[k+2]))
            for i in range(len(words[parent[0]])):
                var top = digits[digit_start[parent[0]]+i].copy()
                for j in range(len(words[parent[1]])):
                    var bottom = digits[digit_start[parent[1]]+j].copy()
                    var child: List[Int] = [top[0],bottom[0]]
                    for k in range(3):
                        child.append(checked_sub(checked_add(base[k],top[k+3]),bottom[k+3]))
                    if not _inside_key_box(child):
                        continue  # All represented packets are inside this box.
                    var key = packet_key(child)
                    if key not in ordered:
                        continue
                    var target = ordered[key]
                    var occurrence = _edge_key(2*index+orientation,i,j,target,size)
                    if occurrence not in inverse_edges:
                        raise Error("direct forward occurrence missing from inverse lift")
                    seen = checked_add(seen,1)
                    if orientation == 0:
                        _increment(forward_counts,checked_add(checked_mul(index,size),target//2))
    if seen != len(inverse_edges) or len(forward_counts) != len(transposed_counts):
        raise Error("ordered occurrence inventories or transpose supports differ")
    for key in transposed_counts:
        if key not in forward_counts or forward_counts[key] != transposed_counts[key]:
            raise Error("literal incoming counts are not the forward transpose")


def bind_literal_graph(graph: NewIncidenceGraph) raises -> LiteralInverseBinding:
    """Bind a supplied finite domain; historical constructor identity is separate."""
    var size = len(graph.states)
    if size < 3 or size > NEW_STATE_BUDGET or len(graph.rows) != size:
        raise Error("literal graph state/row budget or dimension")
    var images = new_source_images(graph.source)
    var words = inflated_words(images,2)
    var digits = literal_digits(words)
    var lookup = Dict[Int,Int]()
    for i in range(size):
        var state = graph.states[i].copy()
        var key = packet_key(state)
        if not same_vector(state,canonical_pair(state[0],state[1],state[2],state[3],state[4])):
            raise Error("literal domain state is not its exact canonical representative")
        if same_vector(state,swap_packet(state)) or key in lookup:
            raise Error("literal domain has a fixed swap or duplicate representative")
        lookup[key] = i
    var roots: List[List[Int]] = [[0,1,0,0,0],[0,2,0,0,0],[1,2,0,0,0]]
    for i in range(3):
        if not same_vector(graph.states[i],roots[i]):
            raise Error("literal domain roots differ from the three exact cut pairs")
    var births = List[List[Int]]()
    for _ in range(size):
        births.append([-1,-1])
    var slots = List[List[List[Int]]]()
    var square = new_matrix_power(2)
    var inverse_numerator = square.adjugate()
    var edges = 0
    var swapped = 0
    var repeated = 0
    for row in range(size):
        var state = graph.states[row].copy()
        var expected = List[List[Int]]()
        var seen_targets = Dict[Int,Int]()
        for i in range(len(digits)):
            if digits[i][0] != state[0]:
                continue
            for j in range(len(digits)):
                if digits[j][0] != state[1]:
                    continue
                var raw = exact_inverse_ancestor(state,digits[i],digits[j],square,inverse_numerator)
                if len(raw) == 0:
                    continue
                var target_state = canonical_pair(raw[0],raw[1],raw[2],raw[3],raw[4])
                if not _inside_key_box(target_state):
                    continue
                var key = packet_key(target_state)
                if key not in lookup:
                    continue
                var target = lookup[key]
                var orientation = 0 if same_vector(raw,target_state) else 1
                if orientation == 1 and not same_vector(swap_packet(raw),target_state):
                    raise Error("literal normalization does not recover raw target")
                var ordinal = len(expected)
                expected.append([target,i,j,orientation])
                swapped = checked_add(swapped,orientation)
                edges = checked_add(edges,1)
                if target in seen_targets:
                    repeated = checked_add(repeated,1)
                else:
                    seen_targets[target] = 1
                if target >= 3 and births[target][0] < 0:
                    if row >= target:
                        raise Error("literal discovery witness is not well founded")
                    births[target] = [row,ordinal]
        if len(expected) != len(graph.rows[row]):
            raise Error("legacy row omits or duplicates an internal literal occurrence")
        for ordinal in range(len(expected)):
            if graph.rows[row][ordinal] != expected[ordinal][0]:
                raise Error("legacy row order does not bind to literal incoming positions")
        slots.append(expected^)
    for i in range(3,size):
        if births[i][0] < 0 or births[i][0] >= i:
            raise Error("nonroot literal packet has no earlier discovery witness")
        if slots[births[i][0]][births[i][1]][0] != i:
            raise Error("literal discovery slot does not reach its state")
    verify_ordered_forward_inventory(graph,words,digits,slots)
    return LiteralInverseBinding(graph,images,words,digits,slots,births,edges,swapped,repeated)


def _same_rows(left: List[List[Int]], right: List[List[Int]]) -> Bool:
    if len(left) != len(right):
        return False
    for i in range(len(left)):
        if not same_vector(left[i],right[i]):
            return False
    return True


def verify_literal_binding(binding: LiteralInverseBinding) raises:
    """Reconstruct all marks, slots and births; never trust submitted metadata."""
    var expected = bind_literal_graph(binding.graph)
    if not _same_rows(binding.images,expected.images) or not _same_rows(binding.words,expected.words) or not _same_rows(binding.digits,expected.digits):
        raise Error("submitted literal words, positions or prefixes were altered")
    if not _same_rows(binding.births,expected.births) or len(binding.slots) != len(expected.slots):
        raise Error("submitted literal birth inventory was altered")
    for i in range(len(binding.slots)):
        if not _same_rows(binding.slots[i],expected.slots[i]):
            raise Error("submitted literal occurrence identity or orientation was altered")
    if binding.edges != expected.edges or binding.swapped != expected.swapped or binding.repeated != expected.repeated:
        raise Error("submitted literal summary differs from complete replay")


def authenticate_literal_binding(binding: LiteralInverseBinding) raises:
    """Public source acceptance also reconstructs the historical finite domain."""
    authenticate_new_graph(binding.graph)
    verify_literal_binding(binding)


def build_literal_binding(source: Int, state_cap: Int = NEW_STATE_BUDGET) raises -> LiteralInverseBinding:
    var graph = build_new_incidence_graph(source,state_cap)
    return bind_literal_graph(graph)
