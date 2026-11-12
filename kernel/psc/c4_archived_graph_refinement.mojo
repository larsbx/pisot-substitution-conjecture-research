"""Source-bound positional refinement of the two archived sharp-box graphs.

Every row is reconstructed from the original sigma squared, with all parent,
flat position, nested outer/local position, prefix and swap data retained.
The old exact residue and strict interval exclusion predicates are reused;
resource limits never become geometric exclusions.  Complete inverse rows
are also compared with direct forward positions on the two-sheet lift.

This finite decoder does not deserialize a Lean proof, establish the sharp
box for the actual prefix tiles, or represent every noncomputable strict
packet.  Those are separate mathematical obligations.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from psc.c4_nonunit_residue_occupancy import inflated_words, same_vector
from psc.c4_finite_cylinder_overlap import fixture_images, matrix_power
from psc.c4_pair_overlap_graph import (
    PairGraph, build_pair_graph, certify_pair_box, canonical_pair,
    outside_pair_box, state_key, verify_pair_weights,
)
from psc.c4_literal_inverse_binding import exact_inverse_ancestor, swap_packet

comptime ARCHIVED_DIGITS = 15
comptime ARCHIVED_STATE_CAP = 16000


struct ArchivedRefinement(Copyable, Movable):
    var graph: PairGraph
    var images: List[List[Int]]
    var words: List[List[Int]]
    # [selected,parent,flatPosition,p0,p1,p2,outerPosition,localPosition].
    var digits: List[List[Int]]
    # Per current child: [ancestorID,topDigit,bottomDigit,swapped].
    var slots: List[List[List[Int]]]
    # Every nonroot has an earlier row and its exact positional slot.
    var births: List[List[Int]]
    var depths: List[Int]
    var period: Int
    var radii: List[Int]
    var direction: Int
    var edges: Int
    var swapped: Int
    var repeated: Int

    def __init__(out self, graph: PairGraph, images: List[List[Int]], words: List[List[Int]], digits: List[List[Int]], slots: List[List[List[Int]]], births: List[List[Int]], depths: List[Int], edges: Int, swapped: Int, repeated: Int):
        self.graph = graph.copy()
        self.images = images.copy()
        self.words = words.copy()
        self.digits = digits.copy()
        self.slots = slots.copy()
        self.births = births.copy()
        self.depths = depths.copy()
        self.period = 2
        self.radii = [16,8]
        self.direction = 0  # current child -> integral inverse ancestor
        self.edges = edges
        self.swapped = swapped
        self.repeated = repeated


def _same_rows(left: List[List[Int]], right: List[List[Int]]) -> Bool:
    if len(left) != len(right):
        return False
    for i in range(len(left)):
        if not same_vector(left[i],right[i]):
            return False
    return True


def archived_digits(images: List[List[Int]]) raises -> List[List[Int]]:
    """Literal two-level addresses, including the complete block prefix."""
    var digits = List[List[Int]]()
    var words = inflated_words(images,2)
    var square = matrix_power(2)
    for parent in range(3):
        var prefix: List[Int] = [0,0,0]
        var position = 0
        for outer in range(len(images[parent])):
            var intermediate = images[parent][outer]
            for local in range(len(images[intermediate])):
                var letter = images[intermediate][local]
                if position >= len(words[parent]) or words[parent][position] != letter:
                    raise Error("nested local address differs from literal block position")
                digits.append([letter,parent,position,prefix[0],prefix[1],prefix[2],outer,local])
                prefix[letter] = checked_add(prefix[letter],1)
                position += 1
        if position != len(words[parent]):
            raise Error("incomplete block occurrence inventory")
        for letter in range(3):
            if prefix[letter] != square.at(letter,parent):
                raise Error("original source incidence does not equal the named square")
    if len(digits) != ARCHIVED_DIGITS or square.det() != 4:
        raise Error("named complete literal inventory or residue index mismatch")
    return digits^


def _six(digit: List[Int]) -> List[Int]:
    return [digit[0],digit[1],digit[2],digit[3],digit[4],digit[5]]


def _edge_key(start: Int, top: Int, bottom: Int, target: Int, size: Int) raises -> Int:
    if size < 3 or size > ARCHIVED_STATE_CAP or start < 0 or start >= 2*size or target < 0 or target >= 2*size:
        raise Error("ordered edge endpoint outside bounded domain")
    if top < 0 or top >= ARCHIVED_DIGITS or bottom < 0 or bottom >= ARCHIVED_DIGITS:
        raise Error("ordered edge position outside complete literal inventory")
    return checked_add(checked_mul(checked_add(checked_mul(checked_add(checked_mul(start,ARCHIVED_DIGITS),top),ARCHIVED_DIGITS),bottom),2*size),target)


def _increment(mut counts: Dict[Int,Int], key: Int) raises:
    if key in counts:
        counts[key] = checked_add(counts[key],1)
    else:
        counts[key] = 1


def verify_archived_ordered_inventory(binding: ArchivedRefinement) raises:
    """Both ordered sheets; direct forward arithmetic, no inverse solver."""
    var size = len(binding.graph.states)
    var ordered = Dict[Int,Int]()
    for i in range(size):
        var key = state_key(binding.graph.states[i])
        var other = state_key(swap_packet(binding.graph.states[i]))
        if key == other or key in ordered or other in ordered:
            raise Error("ordered lift has a fixed swap or duplicate orbit")
        ordered[key] = 2*i
        ordered[other] = 2*i+1
    var inverse_edges = Dict[Int,Int]()
    var transpose_counts = Dict[Int,Int]()
    for row in range(size):
        for slot in binding.slots[row]:
            var target = slot[0]
            var top = binding.digits[slot[1]][2]
            var bottom = binding.digits[slot[2]][2]
            var orientation = slot[3]
            var key = _edge_key(2*target+orientation,top,bottom,2*row,size)
            var mate = _edge_key(2*target+1-orientation,bottom,top,2*row+1,size)
            if key in inverse_edges or mate in inverse_edges or key == mate:
                raise Error("ordered lift duplicated an actual positional occurrence")
            inverse_edges[key] = 1
            inverse_edges[mate] = 1
            _increment(transpose_counts,target*size+row)
    var start: List[Int] = [0,len(binding.words[0]),len(binding.words[0])+len(binding.words[1])]
    var square = matrix_power(2)
    var forward_counts = Dict[Int,Int]()
    var seen = 0
    for ancestor in range(size):
        for orientation in range(2):
            var parent = binding.graph.states[ancestor].copy() if orientation == 0 else swap_packet(binding.graph.states[ancestor])
            var base = square.apply([parent[2],parent[3],parent[4]])
            for i in range(len(binding.words[parent[0]])):
                var top = binding.digits[start[parent[0]]+i].copy()
                for j in range(len(binding.words[parent[1]])):
                    var bottom = binding.digits[start[parent[1]]+j].copy()
                    var child: List[Int] = [top[0],bottom[0]]
                    var in_key_box = True
                    for k in range(3):
                        var value = checked_sub(checked_add(base[k],top[k+3]),bottom[k+3])
                        child.append(value)
                        if value < -32 or value > 32:
                            in_key_box = False
                    if not in_key_box:
                        continue  # Membership test only: represented states are bounded.
                    var key = state_key(child)
                    if key not in ordered:
                        continue
                    var target = ordered[key]
                    var occurrence = _edge_key(2*ancestor+orientation,i,j,target,size)
                    if occurrence not in inverse_edges:
                        raise Error("direct forward occurrence missing from inverse rows")
                    seen += 1
                    if orientation == 0:
                        _increment(forward_counts,ancestor*size+target//2)
    if seen != len(inverse_edges) or len(forward_counts) != len(transpose_counts):
        raise Error("ordered row refinement has the wrong direction or multiplicity")
    for key in transpose_counts:
        if key not in forward_counts or forward_counts[key] != transpose_counts[key]:
            raise Error("incoming matrix is not the complete forward transpose")


def bind_archived_graph(graph: PairGraph) raises -> ArchivedRefinement:
    """Reconstruct full admitted rows; missing admitted targets are errors."""
    var size = len(graph.states)
    if graph.fixture < 0 or graph.fixture > 1 or size < 3 or size > ARCHIVED_STATE_CAP or len(graph.rows) != size:
        raise Error("original fixture or finite graph dimensions")
    certify_pair_box(graph.fixture)
    var images = fixture_images(graph.fixture)
    var words = inflated_words(images,2)
    var digits = archived_digits(images)
    var lookup = Dict[Int,Int]()
    for i in range(size):
        var state = graph.states[i].copy()
        var key = state_key(state)
        if not same_vector(state,canonical_pair(state[0],state[1],state[2],state[3],state[4])):
            raise Error("domain state differs from its track-swap normalization")
        if same_vector(state,swap_packet(state)) or key in lookup:
            raise Error("domain has fixed swaps or duplicate canonical packets")
        if outside_pair_box(state[2],state[3],state[4]):
            raise Error("domain state fails the authenticated sharp-box filter")
        if len(graph.rows[i]) > ARCHIVED_DIGITS*ARCHIVED_DIGITS:
            raise Error("row exceeds the complete positional inventory")
        lookup[key] = i
    var roots: List[List[Int]] = [[0,1,0,0,0],[0,2,0,0,0],[1,2,0,0,0]]
    for i in range(3):
        if not same_vector(graph.states[i],roots[i]):
            raise Error("graph roots differ from the original three overlaps")
    var births = List[List[Int]]()
    var depths = List[Int]()
    for _ in range(size):
        births.append([-1,-1])
        depths.append(0)
    var slots = List[List[List[Int]]]()
    var square = matrix_power(2)
    var adj = square.adjugate()
    var residue = 0
    var box = 0
    var edges = 0
    var swapped = 0
    var repeated = 0
    var next_discovery = 3
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
                var raw = exact_inverse_ancestor(state,_six(digits[i]),_six(digits[j]),square,adj)
                if len(raw) == 0:
                    residue += 1
                    continue
                if outside_pair_box(raw[2],raw[3],raw[4]):
                    box += 1
                    continue
                var canonical = canonical_pair(raw[0],raw[1],raw[2],raw[3],raw[4])
                var key = state_key(canonical)  # Cap failure refuses; never prunes.
                if key not in lookup:
                    raise Error("admitted integral inverse ancestor missing from graph domain")
                var target = lookup[key]
                var orientation = 0 if same_vector(raw,canonical) else 1
                if orientation == 1 and not same_vector(swap_packet(raw),canonical):
                    raise Error("track-swap normalization changed the inverse packet")
                var ordinal = len(expected)
                expected.append([target,i,j,orientation])
                if target >= 3 and births[target][0] < 0:
                    if row >= target or target != next_discovery:
                        raise Error("incomplete or reordered rooted inverse ancestry")
                    births[target] = [row,ordinal]
                    depths[target] = depths[row]+1
                    next_discovery += 1
                edges += 1
                swapped += orientation
                if target in seen_targets:
                    repeated += 1
                else:
                    seen_targets[target] = 1
        if len(expected) != len(graph.rows[row]):
            raise Error("archived row omitted or duplicated a positional edge")
        for ordinal in range(len(expected)):
            if graph.rows[row][ordinal] != expected[ordinal][0]:
                raise Error("archived row direction or literal position order mismatch")
        slots.append(expected^)
    if next_discovery != size or residue != graph.residue_rejections or box != graph.box_rejections:
        raise Error("inverse ancestry or exhaustive exclusion inventory mismatch")
    var result = ArchivedRefinement(graph,images,words,digits,slots,births,depths,edges,swapped,repeated)
    verify_archived_ordered_inventory(result)
    return result^


def verify_archived_refinement(binding: ArchivedRefinement) raises:
    """Recheck every supplied address, slot, exclusion and ancestry witness."""
    if binding.period != 2 or binding.direction != 0 or not same_vector(binding.radii,[16,8]):
        raise Error("wrong block, direction or historical sharp box")
    var expected = bind_archived_graph(binding.graph)
    if not _same_rows(binding.images,expected.images) or not _same_rows(binding.words,expected.words) or not _same_rows(binding.digits,expected.digits):
        raise Error("original substitution or complete literal addresses changed")
    if not _same_rows(binding.births,expected.births) or not same_vector(binding.depths,expected.depths):
        raise Error("incomplete or altered inverse ancestry certificate")
    if len(binding.slots) != len(expected.slots):
        raise Error("missing literal rows")
    for i in range(len(expected.slots)):
        if not _same_rows(binding.slots[i],expected.slots[i]):
            raise Error("positional edge, parent address or normalization mismatch")
    if binding.edges != expected.edges or binding.swapped != expected.swapped or binding.repeated != expected.repeated:
        raise Error("summary disagrees with every-slot replay")


def verify_archived_contraction(binding: ArchivedRefinement, weights: List[Int]) raises -> Int:
    verify_archived_refinement(binding)
    return verify_pair_weights(binding.graph,weights)


def build_archived_refinement(fixture: Int) raises -> ArchivedRefinement:
    return bind_archived_graph(build_pair_graph(fixture))
