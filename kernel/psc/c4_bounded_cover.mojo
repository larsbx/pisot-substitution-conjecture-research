"""Complete bounded inverse histories with literal occurrence addresses.

This constructor does not prune geometric pieces.  It expands every actual
incoming mark pair with an integral ancestor, including ancestors outside a
supplied finite domain.  Domain membership is diagnostic.  Nonintegrality is
an arithmetic fact only: its geometric use needs integral-range reflection.
All resource exhaustion raises, and singular incidence is explicitly refused.

The pre-code gate is docs/c4-compact-cover-literature-2026-11-11.md.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_sub
from finite_linear_algebra.integer_matrix import matmul
from finite_linear_algebra.integer_vector import add, sub, matvec
from finite_linear_algebra.mat3 import Mat3, identity3
from substitution_dynamics.substitution import Substitution
from psc.affine_ancestry_trace import build_affine_trace_tables, _prefix_parikh
from psc.c4_literal_inverse_binding import packet_key
from psc.c4_nonunit_residue_occupancy import inflated_words
from psc.c4_pair_overlap_new_incidence import new_source_images

comptime COVER_MAX_DEPTH = 6
comptime COVER_MAX_IMAGE_LENGTH = 27
comptime COVER_COORDINATE_BOUND = 64  # packet_key's operational domain
comptime COVER_STATE_CAP = 4096
comptime COVER_HISTORY_CAP = 20000
comptime COVER_CANDIDATE_CAP = 200000
comptime COVER_WORD_CAP = 100000


struct BoundedCover(Copyable, Movable):
    var images: List[List[Int]]
    var roots: List[List[Int]]
    var domain: List[List[Int]]
    var depth: Int
    var determinant: Int
    # [selected letter, parent letter, position, prefix0, prefix1, prefix2]
    var digits: List[List[Int]]
    # [root,parent,depth,topDigit,bottomDigit,top,bottom,delta3,T3,B3,inside,retained]
    # T/B are the proper-prefix Parikh vectors in the ACTUAL depth iterate.
    var nodes: List[List[Int]]
    # [node,topDigit,bottomDigit,status,targetNode]
    # status 0: no integral preimage; 1: inside domain; 2: outside domain.
    var candidates: List[List[Int]]
    var unique_states: Int

    def __init__(out self, images: List[List[Int]], roots: List[List[Int]], domain: List[List[Int]], depth: Int, determinant: Int, digits: List[List[Int]], nodes: List[List[Int]], candidates: List[List[Int]], unique_states: Int):
        self.images = images.copy()
        self.roots = roots.copy()
        self.domain = domain.copy()
        self.depth = depth
        self.determinant = determinant
        self.digits = digits.copy()
        self.nodes = nodes.copy()
        self.candidates = candidates.copy()
        self.unique_states = unique_states


def _rows3(entries: List[Int]) raises -> List[List[Int]]:
    if len(entries) != 9:
        raise Error("bounded cover matrix shape")
    return [[entries[0],entries[1],entries[2]],
            [entries[3],entries[4],entries[5]],
            [entries[6],entries[7],entries[8]]]


def _triple(entries: List[Int], start: Int) -> List[Int]:
    return [entries[start],entries[start+1],entries[start+2]]


def node_packet(node: List[Int]) raises -> List[Int]:
    if len(node) != 18:
        raise Error("bounded history record must have eighteen fields")
    return [node[5],node[6],node[7],node[8],node[9]]


def _packet_inventory(packets: List[List[Int]], limit: Int) raises -> Dict[Int,Int]:
    if len(packets) > limit:
        raise Error("bounded cover state budget exhausted; inconclusive")
    var result = Dict[Int,Int]()
    for i in range(len(packets)):
        var key = packet_key(packets[i])
        if key in result:
            raise Error("bounded cover repeated packet in supplied inventory")
        result[key] = i
    return result^


def _validate_images(images: List[List[Int]]) raises:
    if len(images) != 3:
        raise Error("bounded cover requires three source letters")
    for word in images:
        if len(word) < 1 or len(word) > COVER_MAX_IMAGE_LENGTH:
            raise Error("bounded cover image length outside 1..27")
    _ = Substitution.checked(images)


def _literal_levels(images: List[List[Int]], depth: Int, word_cap: Int) raises -> List[List[List[Int]]]:
    # Precompute actual words, so address authentication is not just an
    # incidence-vector check.  The word cap never silently clips an image.
    var sigma = Substitution.checked(images)
    var levels = List[List[List[Int]]]()
    levels.append([[0],[1],[2]])
    for n in range(depth):
        var next_words = List[List[Int]]()
        for letter in range(3):
            var next_size = 0
            for selected in levels[n][letter]:
                next_size = checked_add(next_size,len(images[selected]))
                if next_size > word_cap:
                    raise Error("bounded cover literal word budget exhausted; inconclusive")
            next_words.append(sigma.apply(levels[n][letter]))
        levels.append(next_words^)
    return levels^


def _check_literal_address(word: List[Int], prefix: List[Int], selected: Int) raises:
    var position = checked_add(checked_add(prefix[0],prefix[1]),prefix[2])
    if position < 0 or position >= len(word) or word[position] != selected:
        raise Error("bounded cover address fails actual iterated word lookup")
    var actual: List[Int] = [0,0,0]
    for i in range(position):
        actual[word[i]] += 1  # word size is already at most COVER_WORD_CAP
    if actual != prefix:
        raise Error("bounded cover address prefix differs from actual iterated word")


def build_bounded_cover(images: List[List[Int]], roots: List[List[Int]], domain: List[List[Int]], depth: Int,
        state_cap: Int = COVER_STATE_CAP, history_cap: Int = COVER_HISTORY_CAP,
        candidate_cap: Int = COVER_CANDIDATE_CAP, word_cap: Int = COVER_WORD_CAP) raises -> BoundedCover:
    """Expand the complete depth-bounded integral tree, with no domain pruning.

    A successful result is finite arithmetic evidence.  Compact coverage is
    the separately proved conditional Lean theorem, never a returned flag.
    """
    _validate_images(images)
    if depth < 0 or depth > COVER_MAX_DEPTH:
        raise Error("bounded cover depth outside 0..6")
    if state_cap < 1 or state_cap > COVER_STATE_CAP or history_cap < 1 or history_cap > COVER_HISTORY_CAP:
        raise Error("bounded cover state/history budget outside supported range")
    if candidate_cap < 1 or candidate_cap > COVER_CANDIDATE_CAP or word_cap < 1 or word_cap > COVER_WORD_CAP:
        raise Error("bounded cover candidate/word budget outside supported range")
    if len(roots) == 0 or len(roots) > history_cap:
        raise Error("bounded cover root/history budget exhausted; inconclusive")
    var seen = _packet_inventory(roots,state_cap)
    var represented = _packet_inventory(domain,state_cap)
    var tables = build_affine_trace_tables(images)
    var matrix = Mat3(tables.incidence)
    # Each entry is <=27, so the vendored determinant/adjugate products are
    # bounded by 6*27^3 and 2*27^2.  All later products use checked kernels.
    var determinant = matrix.det()
    if determinant == 0:
        raise Error("bounded cover requires injective incidence; singular is inconclusive")
    var adjugate = _rows3(matrix.adjugate().e)
    var matrix_rows = _rows3(matrix.e)
    var digits = List[List[Int]]()
    for parent in range(3):
        for position in range(len(images[parent])):
            var prefix = _prefix_parikh(tables,parent,position)
            digits.append([images[parent][position],parent,position,prefix.x,prefix.y,prefix.z])
    var powers = List[List[Int]]()
    powers.append(identity3().e.copy())
    for n in range(depth):
        powers.append(matmul(powers[n],matrix.e,3))
    var levels = _literal_levels(images,depth,word_cap)
    var nodes = List[List[Int]]()
    for root in range(len(roots)):
        var p = roots[root].copy()
        var inside = 1 if packet_key(p) in represented else 0
        nodes.append([root,-1,0,-1,-1,p[0],p[1],p[2],p[3],p[4],0,0,0,0,0,0,inside,inside])
    var candidates = List[List[Int]]()
    var cursor = 0
    while cursor < len(nodes):
        var current = nodes[cursor].copy()
        var level = current[2]
        if level == depth:
            cursor += 1
            continue
        var power_rows = _rows3(powers[level])
        var next_power_rows = _rows3(powers[level+1])
        var root = roots[current[0]].copy()
        for i in range(len(digits)):
            var top = digits[i].copy()
            if top[0] != current[5]:
                continue
            for j in range(len(digits)):
                var bottom = digits[j].copy()
                if bottom[0] != current[6]:
                    continue
                if len(candidates) >= candidate_cap:
                    raise Error("bounded cover candidate budget exhausted; inconclusive")
                var rhs = sub(add(_triple(current,7),_triple(bottom,3)),_triple(top,3))
                var numerator = matvec(adjugate,rhs)
                if numerator[0]%determinant != 0 or numerator[1]%determinant != 0 or numerator[2]%determinant != 0:
                    candidates.append([cursor,i,j,0,-1])
                    continue
                var delta: List[Int] = [numerator[0]//determinant,numerator[1]//determinant,numerator[2]//determinant]
                if matvec(matrix_rows,delta) != rhs:
                    raise Error("bounded cover inverse fails original integral equation")
                var target: List[Int] = [top[1],bottom[1],delta[0],delta[1],delta[2]]
                var key = packet_key(target)  # refusal, never a deletion
                if key not in seen:
                    if len(seen) >= state_cap:
                        raise Error("bounded cover distinct state budget exhausted; inconclusive")
                    seen[key] = len(seen)
                if len(nodes) >= history_cap:
                    raise Error("bounded cover history budget exhausted; inconclusive")
                var top_prefix = add(_triple(current,10),matvec(power_rows,_triple(top,3)))
                var bottom_prefix = add(_triple(current,13),matvec(power_rows,_triple(bottom,3)))
                if matvec(next_power_rows,delta) != sub(add(_triple(root,2),bottom_prefix),top_prefix):
                    raise Error("bounded cover composed integral equation failed")
                _check_literal_address(levels[level+1][top[1]],top_prefix,root[0])
                _check_literal_address(levels[level+1][bottom[1]],bottom_prefix,root[1])
                var inside = 1 if key in represented else 0
                var retained = 1 if inside == 1 and current[17] == 1 else 0
                var next_id = len(nodes)
                nodes.append([current[0],cursor,level+1,i,j,top[1],bottom[1],delta[0],delta[1],delta[2],
                    top_prefix[0],top_prefix[1],top_prefix[2],bottom_prefix[0],bottom_prefix[1],bottom_prefix[2],inside,retained])
                candidates.append([cursor,i,j,1 if inside == 1 else 2,next_id])
        cursor += 1
    return BoundedCover(images,roots,domain,depth,determinant,digits,nodes,candidates,len(seen))


def verify_bounded_cover(cover: BoundedCover) raises:
    """Authenticate every path record and candidate against the literal source."""
    var canonical = build_bounded_cover(cover.images,cover.roots,cover.domain,cover.depth)
    if cover.determinant != canonical.determinant or cover.unique_states != canonical.unique_states:
        raise Error("bounded cover arithmetic metadata differs")
    if cover.digits != canonical.digits or cover.nodes != canonical.nodes or cover.candidates != canonical.candidates:
        raise Error("bounded cover omitted, duplicated or altered actual occurrence history")


def cover_summary(cover: BoundedCover) raises -> List[Int]:
    var residues = 0
    var outside = 0
    var leaves = 0
    var retained = 0
    var leaf_endpoints = Dict[Int,Int]()
    for c in cover.candidates:
        if c[3] == 0:
            residues += 1
    for node in cover.nodes:
        if node[16] == 0:
            outside += 1
        if node[2] == cover.depth:
            leaves += 1
            retained += node[17]
            leaf_endpoints[packet_key(node_packet(node))] = 1
    return [len(cover.nodes),len(cover.candidates),residues,outside,leaves,retained,leaves-len(leaf_endpoints),cover.unique_states]


def fixture_cover(index: Int) raises -> BoundedCover:
    var roots: List[List[Int]] = [[0,1,0,0,0],[1,0,0,0,0]]
    if index == 0:
        return build_bounded_cover([[0,0],[1,1],[2,2]],roots,roots,3)
    if index == 1:
        roots = [[0,0,0,0,0]]
        return build_bounded_cover([[0,0],[1,1],[2,2]],roots,roots,3)
    if index == 2:
        return build_bounded_cover([[0,1],[1],[2]],roots,roots,2)
    if index == 3:
        # Actual sigma^2 words for the final member 11/210/10 of #497's class.
        return build_bounded_cover(inflated_words(new_source_images(11),2),roots,roots,2)
    raise Error("bounded cover fixture outside 0..3")


def z3_affine_image(mask: Int, multiplier: Int, translation: Int) raises -> Int:
    """Exact finite-group set image; no physical interval or Haar assertion."""
    if mask < 0 or mask > 7 or multiplier < 0 or multiplier > 2 or translation < 0 or translation > 2:
        raise Error("finite Z3 set input outside its exact domain")
    var result = 0
    for x in range(3):
        if (mask & (1<<x)) != 0:
            result |= 1<<((multiplier*x+translation)%3)
    return result


def z3_overlap(top: Int, bottom: Int, translation: Int) raises -> Int:
    if top < 0 or top > 7:
        raise Error("finite Z3 top set outside 0..7")
    return top & z3_affine_image(bottom,1,translation)


def z3_tile_equation(images: List[List[Int]], multiplier: Int, tiles: List[Int], star_scale: Int = 1) raises -> Bool:
    _validate_images(images)
    if len(tiles) != 3 or star_scale < 0 or star_scale > 2:
        raise Error("finite Z3 tile shape")
    for child in range(3):
        var image_union = 0
        for parent in range(3):
            for position in range(len(images[parent])):
                if images[parent][position] == child:
                    image_union |= z3_affine_image(tiles[parent],multiplier,(star_scale*position)%3)
        if image_union != tiles[child]:
            return False
    return True


def closed_integer_intersection(lo1: Int, hi1: Int, lo2: Int, hi2: Int) raises -> Int:
    # Exact finite set count for a tiny enclosure countercontrol, not a
    # continuum measure or a compact-prefix tile constructor.
    if lo1 < -16 or hi1 > 16 or lo2 < -16 or hi2 > 16 or lo1 > hi1 or lo2 > hi2:
        raise Error("finite enclosure control outside -16..16")
    return max(0,min(hi1,hi2)-max(lo1,lo2)+1)


def _z3_cardinality(mask: Int) raises -> Int:
    if mask < 0 or mask > 7:
        raise Error("finite Z3 set outside 0..7")
    var count = 0
    for x in range(3):
        if (mask & (1<<x)) != 0:
            count += 1
    return count


def cover_countercontrols() raises -> List[List[Int]]:
    """Exact finite controls: rows correspond to the names in the driver.

    Z3 carries its finite discrete compact topology. Set cardinalities below
    are exact finite-set facts, not claims about a Pisot representation space.
    """
    var doubled: List[List[Int]] = [[0,0],[1,1],[2,2]]
    var identity: List[List[Int]] = [[0],[1],[2]]
    var full: List[Int] = [7,7,7]
    if not z3_tile_equation(doubled,2,full) or not z3_tile_equation(identity,1,full):
        raise Error("finite Z3 original tile equation failed")
    # Multiplication by two is an automorphism of Z3. For doubled images,
    # star(z)=sum(z) mod3 commutes with 2I. At p.delta=e2, every one of the
    # four candidate rhs has odd third coordinate, hence no integral inverse.
    var missing: List[List[Int]] = [[0,1,0,0,1]]
    var empty_incoming = build_bounded_cover(doubled,missing,missing,1)
    var residue = cover_summary(empty_incoming)
    var controls = List[List[Int]]()
    controls.append([_z3_cardinality(z3_overlap(7,7,1)),residue[4],residue[2]])
    # A bijective Z3 action and permutation incidence have genuine range
    # reflection. The root and its swap are represented, but their only
    # integral ancestors are not. Internal completeness misses the whole set.
    var cycle: List[List[Int]] = [[1],[2],[0]]
    if not z3_tile_equation(cycle,1,full):
        raise Error("finite cyclic tile equation failed")
    var root: List[List[Int]] = [[0,1,0,0,0]]
    var omitted = build_bounded_cover(cycle,root,[[0,1,0,0,0],[1,0,0,0,0]],1)
    var omit_summary = cover_summary(omitted)
    var physical_interval = max(0,min(1,1-2)-max(0,-2))
    controls.append([physical_interval,_z3_cardinality(z3_overlap(7,7,2))])
    # Under the identity tile equation K=Z3, the false enclosure B={0}
    # appears separated from B+1, although K intersect (K+1)=Z3.
    controls.append([_z3_cardinality(z3_overlap(1,1,1)),_z3_cardinality(z3_overlap(7,7,1))])
    controls.append([closed_integer_intersection(0,1,1,2)])
    # This is actual occurrence redundancy: unimodular s=01/1/2,
    # A=id, star=0, K=Z3. The two integral ancestors are p itself and
    # (0,0,(1,-1,0)); both affine pieces are Z3. Keeping p loses an
    # occurrence without losing a set point. Range reflection holds since M
    # is unimodular, even though star is zero.
    var redundant_images: List[List[Int]] = [[0,1],[1],[2]]
    if not z3_tile_equation(redundant_images,1,full,star_scale=0):
        raise Error("finite redundant tile equation failed")
    var redundant = build_bounded_cover(redundant_images,root,root,1)
    if redundant.determinant != 1:
        raise Error("finite redundant control must have unimodular incidence")
    var redundant_summary = cover_summary(redundant)
    controls.append([redundant_summary[4],redundant_summary[5]])
    # Two distinct singleton pieces: omitting {1} changes coverage.
    controls.append([_z3_cardinality(1|2),_z3_cardinality(1)])
    controls.append([_z3_cardinality(z3_overlap(7,7,1)),omit_summary[4],omit_summary[5]])
    controls.append(forward_leak_control())
    return controls^


def forward_leak_control() raises -> List[Int]:
    """The mandatory two-root inverse-closed yet forward-leaking control.

    The returned lengths are explicitly physical interval diagnostics.
    They are never used as compact-overlap measure or a geometric exclusion.
    """
    var cover = fixture_cover(0)
    var tables = build_affine_trace_tables(cover.images)
    var matrix_rows = _rows3(tables.incidence)
    var total = 0
    var retained = 0
    var positive_exits = 0
    for root in cover.roots:
        for i in range(len(cover.images[root[0]])):
            for j in range(len(cover.images[root[1]])):
                var top = _prefix_parikh(tables,root[0],i)
                var bottom = _prefix_parikh(tables,root[1],j)
                var delta = sub(add(matvec(matrix_rows,_triple(root,2)),[top.x,top.y,top.z]),[bottom.x,bottom.y,bottom.z])
                var target: List[Int] = [cover.images[root[0]][i],cover.images[root[1]][j],delta[0],delta[1],delta[2]]
                var displacement = delta[0]+delta[1]+delta[2]
                var length = max(0,min(1,1-displacement)-max(0,-displacement))
                total += length
                if target in cover.domain:
                    retained += length
                elif length > 0:
                    positive_exits += 1
    return [total,retained,positive_exits]
