"""Exact local incoming controls in supplied finite cyclic-group models.

The complete raw paired-mark inventory includes nonintegral pairs.  Integer
lifts and literal addresses come from the existing one-step bounded cover;
equal sets never identify occurrences.  Local lifting, representation of all
nonempty pairs, and retained SET coverage are separate outputs.

These finite discrete compact models are abstract interface controls.  They
do not authenticate Pisot compact tiles, a full-field finite residue map,
product-Haar scaling, or any governed C4 claim.  The pre-code gate is
docs/c4-local-admissibility-literature-2026-11-11.md.  Every cap refuses the
whole construction; no arithmetic or budget failure deletes a piece.
"""

from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_mul
from finite_linear_algebra.integer_vector import add, sub, matvec
from finite_linear_algebra.mat3 import Mat3
from psc.affine_ancestry_trace import build_affine_trace_tables, _prefix_parikh
from psc.c4_bounded_cover import (
    build_bounded_cover, node_packet, _packet_inventory, _validate_images,
    _rows3, _triple, COVER_CANDIDATE_CAP,
)
from psc.c4_literal_inverse_binding import packet_key

comptime LOCAL_MODULUS_CAP = 15
comptime LOCAL_PACKET_CAP = 64


struct CyclicModel(Copyable, Movable):
    var images: List[List[Int]]
    var sources: List[List[Int]]
    var domain: List[List[Int]]
    var modulus: Int
    var action: Int
    var star: List[Int]
    var tiles: List[Int]
    var profile_modulus: Int
    var profiles: List[Int]

    def __init__(out self, images: List[List[Int]], sources: List[List[Int]], domain: List[List[Int]],
            modulus: Int, action: Int, star: List[Int], tiles: List[Int],
            profile_modulus: Int, profiles: List[Int]):
        self.images = images.copy()
        self.sources = sources.copy()
        self.domain = domain.copy()
        self.modulus = modulus
        self.action = action
        self.star = star.copy()
        self.tiles = tiles.copy()
        self.profile_modulus = profile_modulus
        self.profiles = profiles.copy()


struct LocalAdmissibility(Copyable, Movable):
    var model: CyclicModel
    var determinant: Int
    # [selected,parent,position,prefix0,prefix1,prefix2]
    var digits: List[List[Int]]
    # [source,topDigit,bottomDigit,rhs3,integral,parentTop,parentBottom,y3,
    #  inside,topMask,bottomMask,pairMask,ancestorMask,inverseMask,retainedMask,
    #  projectedTopMask,projectedBottomMask,projectedPairMask]
    var pairs: List[List[Int]]
    # Twenty fields, documented by row_record below and the v1 driver.
    var rows: List[List[Int]]
    # [unitVector3,ambientPreimage,starValue,integral,integerSolution3]
    var basis: List[List[Int]]

    def __init__(out self, model: CyclicModel, determinant: Int, digits: List[List[Int]],
            pairs: List[List[Int]], rows: List[List[Int]], basis: List[List[Int]]):
        self.model = model.copy()
        self.determinant = determinant
        self.digits = digits.copy()
        self.pairs = pairs.copy()
        self.rows = rows.copy()
        self.basis = basis.copy()


def _residue(value: Int, modulus: Int) -> Int:
    # Only called with a validated positive modulus <=15.  The first
    # remainder is bounded even if the supplied integer was negative.
    return ((value % modulus)+modulus)%modulus


def cyclic_image(mask: Int, modulus: Int, action: Int, translation: Int) raises -> Int:
    """Exact image of a finite set, including modulus-one profile sets."""
    if modulus < 1 or modulus > LOCAL_MODULUS_CAP:
        raise Error("cyclic set modulus outside 1..15")
    if mask < 0 or mask >= (1<<modulus):
        raise Error("cyclic set mask outside declared group")
    if action < 0 or action >= modulus or translation < 0 or translation >= modulus:
        raise Error("cyclic affine map is not normalized")
    var result = 0
    for x in range(modulus):
        if (mask & (1<<x)) != 0:
            # Bounds above give action*x+translation <=210.
            result |= 1<<((action*x+translation)%modulus)
    return result


def project_mask(mask: Int, modulus: Int, profile_modulus: Int) raises -> Int:
    if modulus < 2 or modulus > LOCAL_MODULUS_CAP or profile_modulus < 1 or profile_modulus > modulus:
        raise Error("cyclic projection modulus outside supported range")
    if modulus%profile_modulus != 0:
        raise Error("cyclic projection is not a quotient homomorphism")
    if mask < 0 or mask >= (1<<modulus):
        raise Error("cyclic projection mask outside source group")
    var result = 0
    for x in range(modulus):
        if (mask & (1<<x)) != 0:
            result |= 1<<(x%profile_modulus)
    return result


def star_value(model: CyclicModel, vector: List[Int]) raises -> Int:
    if len(vector) != 3 or len(model.star) != 3 or model.modulus < 2 or model.modulus > LOCAL_MODULUS_CAP:
        raise Error("cyclic star dimensions or modulus")
    var value = 0
    for i in range(3):
        if model.star[i] < 0 or model.star[i] >= model.modulus:
            raise Error("cyclic star coefficients are not normalized")
        value = checked_add(value,checked_mul(model.star[i],vector[i]))
    return _residue(value,model.modulus)


def overlap_mask(model: CyclicModel, packet: List[Int]) raises -> Int:
    _ = packet_key(packet)
    if len(model.tiles) != 3:
        raise Error("cyclic tile inventory must have three sets")
    return model.tiles[packet[0]] & cyclic_image(model.tiles[packet[1]],model.modulus,1,
        star_value(model,_triple(packet,2)))


def validate_cyclic_model(model: CyclicModel) raises:
    """Authenticate every finite model premise, including full tile unions.

    Incidence need not be injective here, so the separate singular witness
    can use this same premise checker.  The nonsingular record constructor
    additionally requires it through build_bounded_cover.
    """
    _validate_images(model.images)
    if model.modulus < 2 or model.modulus > LOCAL_MODULUS_CAP:
        raise Error("local finite group modulus outside 2..15")
    if model.action < 0 or model.action >= model.modulus:
        raise Error("local finite group action is not normalized")
    if len(model.star) != 3 or len(model.tiles) != 3 or len(model.profiles) != 3:
        raise Error("local finite model needs three star coefficients, tiles and profiles")
    if model.profile_modulus < 1 or model.profile_modulus > model.modulus or model.modulus%model.profile_modulus != 0:
        raise Error("local profile projection must be a cyclic quotient")
    for letter in range(3):
        if model.star[letter] < 0 or model.star[letter] >= model.modulus:
            raise Error("local star coefficient is not normalized")
        if model.tiles[letter] < 0 or model.tiles[letter] >= (1<<model.modulus):
            raise Error("local tile mask outside group")
        if model.profiles[letter] < 0 or model.profiles[letter] >= (1<<model.profile_modulus):
            raise Error("local profile mask outside quotient group")
        var projected = project_mask(model.tiles[letter],model.modulus,model.profile_modulus)
        if (projected & model.profiles[letter]) != projected:
            raise Error("local profile fails actual tile enclosure")
    if len(model.sources) == 0:
        raise Error("local source inventory is empty")
    var sources = _packet_inventory(model.sources,LOCAL_PACKET_CAP)
    var domain = _packet_inventory(model.domain,LOCAL_PACKET_CAP)
    for packet in model.domain:
        if packet_key(packet) not in sources:
            raise Error("local domain packet lacks a checked source row")
    var seen = 0
    for x in range(model.modulus):
        var bit = 1<<((model.action*x)%model.modulus)
        if (seen & bit) != 0:
            raise Error("local ambient action is not injective")
        seen |= bit
        if ((model.action*x)%model.modulus)%model.profile_modulus != ((model.action%model.profile_modulus)*(x%model.profile_modulus))%model.profile_modulus:
            raise Error("local quotient action fails commutation")
    var tables = build_affine_trace_tables(model.images)
    var rows = _rows3(tables.incidence)
    for axis in range(3):
        var unit: List[Int] = [0,0,0]
        unit[axis] = 1
        if star_value(model,matvec(rows,unit)) != (model.action*model.star[axis])%model.modulus:
            raise Error("local star and incidence fail action commutation")
    for selected in range(3):
        var union_mask = 0
        for parent in range(3):
            for position in range(len(model.images[parent])):
                if model.images[parent][position] == selected:
                    var prefix = _prefix_parikh(tables,parent,position)
                    union_mask |= cyclic_image(model.tiles[parent],model.modulus,model.action,
                        star_value(model,[prefix.x,prefix.y,prefix.z]))
        if union_mask != model.tiles[selected]:
            raise Error("local model fails original complete tile equation")


def _basis_records(model: CyclicModel) raises -> List[List[Int]]:
    """Reuse the exact bounded solver at the zero-prefix pair for each e_i.

    A missing integral basis lift and the explicit ambient preimage give a
    counterexample to global range reflection.  No finite sample is used to
    infer that reflection holds for all integer vectors.
    """
    var result = List[List[Int]]()
    for axis in range(3):
        var unit: List[Int] = [0,0,0]
        unit[axis] = 1
        var child = model.images[0][0]
        var roots: List[List[Int]] = [[child,child,unit[0],unit[1],unit[2]]]
        var empty = List[List[Int]]()
        var probe = build_bounded_cover(model.images,roots,empty,1)
        if len(probe.candidates) == 0 or probe.candidates[0][1] != 0 or probe.candidates[0][2] != 0:
            raise Error("local basis probe lost its first actual zero-prefix pair")
        if probe.digits[0] != [child,0,0,0,0,0]:
            raise Error("local basis probe first digit is not the actual zero prefix")
        var integral = 0
        var solution: List[Int] = [0,0,0]
        if probe.candidates[0][3] != 0:
            integral = 1
            solution = _triple(node_packet(probe.nodes[probe.candidates[0][4]]),2)
        var value = star_value(model,unit)
        var preimage = -1
        for x in range(model.modulus):
            if (model.action*x)%model.modulus == value:
                if preimage != -1:
                    raise Error("local basis ambient preimage was not unique")
                preimage = x
        if preimage == -1:
            raise Error("local finite injective ambient action lacked a preimage")
        result.append([unit[0],unit[1],unit[2],preimage,value,integral,solution[0],solution[1],solution[2]])
    return result^


def row_record(model: CyclicModel, source: Int, pairs: List[List[Int]]) raises -> List[Int]:
    """Aggregate sets separately from all literal occurrence counts.

    Fields: inside, overlap, raw/integral/retained unions, total/nonempty/
    integral/integral-nonempty/retained/retained-nonempty counts,
    nonintegral-nonempty/outside-nonempty counts, local/represented/set-cover/
    all-paired-contained flags, duplicate nonempty retained image count,
    omitted nonempty contained count, and profile-excluded pair count.
    """
    var inside = 0
    for packet in model.domain:
        if packet == model.sources[source]:
            inside = 1
    var overlap = overlap_mask(model,model.sources[source])
    var raw_union = 0
    var integral_union = 0
    var retained_union = 0
    var count = 0
    var nonempty = 0
    var integral = 0
    var integral_nonempty = 0
    var retained = 0
    var retained_nonempty = 0
    var nonintegral_nonempty = 0
    var outside_nonempty = 0
    var profile_excluded = 0
    var distinct_retained = Dict[Int,Int]()
    for pair in pairs:
        if pair[0] != source:
            continue
        count += 1
        raw_union |= pair[15]
        integral_union |= pair[17]
        retained_union |= pair[18]
        integral += pair[6]
        retained += pair[12]
        if pair[21] == 0:
            profile_excluded += 1
        if pair[15] != 0:
            nonempty += 1
            if pair[6] == 1:
                integral_nonempty += 1
                if pair[12] == 1:
                    retained_nonempty += 1
                    distinct_retained[pair[18]] = 1
                else:
                    outside_nonempty += 1
            else:
                nonintegral_nonempty += 1
    var all_contained = 1
    var omitted_contained = 0
    for pair in pairs:
        if pair[0] != source:
            continue
        var contained = (pair[15] & retained_union) == pair[15]
        if not contained:
            all_contained = 0
        if pair[15] != 0 and pair[12] == 0 and contained:
            omitted_contained += 1
    if raw_union != overlap:
        raise Error("local unconditional raw paired union failed")
    if (integral_union & overlap) != integral_union or (retained_union & integral_union) != retained_union:
        raise Error("local retained or integral union escaped its parent overlap")
    var local = 1 if nonintegral_nonempty == 0 else 0
    var represented = 1 if nonintegral_nonempty == 0 and outside_nonempty == 0 else 0
    var covered = 1 if retained_union == overlap else 0
    if local == 1 and integral_union != overlap:
        raise Error("local lifting failed its integral set cover consequence")
    if represented == 1 and covered == 0:
        raise Error("local representation failed its retained set cover consequence")
    if all_contained != covered:
        raise Error("local exact raw-pair containment criterion failed")
    return [inside,overlap,raw_union,integral_union,retained_union,count,nonempty,integral,
        integral_nonempty,retained,retained_nonempty,nonintegral_nonempty,outside_nonempty,
        local,represented,covered,all_contained,retained_nonempty-len(distinct_retained),
        omitted_contained,profile_excluded]


def build_local_admissibility(model: CyclicModel, candidate_cap: Int = COVER_CANDIDATE_CAP) raises -> LocalAdmissibility:
    validate_cyclic_model(model)
    var cover = build_bounded_cover(model.images,model.sources,model.domain,1,candidate_cap=candidate_cap)
    var pairs = List[List[Int]]()
    for candidate in cover.candidates:
        var source = candidate[0]
        if source < 0 or source >= len(model.sources):
            raise Error("local one-step candidate was not attached to a source")
        var packet = model.sources[source].copy()
        var top = cover.digits[candidate[1]].copy()
        var bottom = cover.digits[candidate[2]].copy()
        var rhs = sub(add(_triple(packet,2),_triple(bottom,3)),_triple(top,3))
        var top_translation = star_value(model,_triple(top,3))
        var bottom_translation = star_value(model,add(_triple(packet,2),_triple(bottom,3)))
        var top_mask = cyclic_image(model.tiles[top[1]],model.modulus,model.action,top_translation)
        var bottom_mask = cyclic_image(model.tiles[bottom[1]],model.modulus,model.action,bottom_translation)
        var pair_mask = top_mask & bottom_mask
        var projected_top = cyclic_image(model.profiles[top[1]],model.profile_modulus,
            model.action%model.profile_modulus,top_translation%model.profile_modulus)
        var projected_bottom = cyclic_image(model.profiles[bottom[1]],model.profile_modulus,
            model.action%model.profile_modulus,bottom_translation%model.profile_modulus)
        var projected_pair = projected_top & projected_bottom
        var actual_projection = project_mask(pair_mask,model.modulus,model.profile_modulus)
        if (actual_projection & projected_pair) != actual_projection:
            raise Error("local projected profiles failed paired-piece enclosure")
        if projected_pair == 0 and pair_mask != 0:
            raise Error("local projected exclusion erased a nonempty actual piece")
        var integral = 0
        var solution: List[Int] = [0,0,0]
        var inside = 0
        var ancestor_mask = 0
        var inverse_mask = 0
        var retained_mask = 0
        if candidate[3] != 0:
            integral = 1
            var ancestor = node_packet(cover.nodes[candidate[4]])
            solution = _triple(ancestor,2)
            inside = 1 if candidate[3] == 1 else 0
            if ancestor[0] != top[1] or ancestor[1] != bottom[1]:
                raise Error("local inverse ancestor lost literal parent letters")
            ancestor_mask = overlap_mask(model,ancestor)
            inverse_mask = cyclic_image(ancestor_mask,model.modulus,model.action,top_translation)
            if inverse_mask != pair_mask:
                raise Error("local actual inverse occurrence did not match its paired piece")
            if inside == 1:
                retained_mask = inverse_mask
        pairs.append([source,candidate[1],candidate[2],rhs[0],rhs[1],rhs[2],integral,top[1],bottom[1],
            solution[0],solution[1],solution[2],inside,top_mask,bottom_mask,pair_mask,ancestor_mask,
            inverse_mask,retained_mask,projected_top,projected_bottom,projected_pair])
    var rows = List[List[Int]]()
    for source in range(len(model.sources)):
        rows.append(row_record(model,source,pairs))
    var basis = _basis_records(model)
    return LocalAdmissibility(model,cover.determinant,cover.digits,pairs,rows,basis)


def verify_local_admissibility(inventory: LocalAdmissibility) raises:
    """Reject missing, repeated or altered addresses, sets and verdicts."""
    var canonical = build_local_admissibility(inventory.model)
    if inventory.determinant != canonical.determinant:
        raise Error("local determinant metadata differs")
    if inventory.digits != canonical.digits or inventory.pairs != canonical.pairs:
        raise Error("local literal paired inventory was omitted, repeated or altered")
    if inventory.rows != canonical.rows or inventory.basis != canonical.basis:
        raise Error("local row or basis evidence differs from its full reconstruction")


def local_summary(inventory: LocalAdmissibility) -> List[Int]:
    var nonempty = 0
    var integral = 0
    var retained_nonempty = 0
    var nonintegral_nonempty = 0
    var outside_nonempty = 0
    var domain_local = 1
    var domain_represented = 1
    var domain_covered = 1
    var basis_integral = 0
    var profile_excluded = 0
    for row in inventory.rows:
        nonempty += row[6]
        integral += row[7]
        retained_nonempty += row[10]
        nonintegral_nonempty += row[11]
        outside_nonempty += row[12]
        profile_excluded += row[19]
        if row[0] == 1:
            domain_local &= row[13]
            domain_represented &= row[14]
            domain_covered &= row[15]
    for basis in inventory.basis:
        basis_integral += basis[5]
    return [len(inventory.rows),len(inventory.pairs),nonempty,integral,retained_nonempty,
        nonintegral_nonempty,outside_nonempty,domain_local,domain_represented,domain_covered,
        basis_integral,profile_excluded]


def local_fixture_model(index: Int) raises -> CyclicModel:
    var sources: List[List[Int]] = [[0,1,0,0,0],[1,0,0,0,0]]
    if index == 0:
        sources = [[1,2,0,0,0],[2,1,0,0,0]]
        return CyclicModel([[0,0],[1],[2]],sources,sources,3,1,[0,1,1],[7,7,7],1,[1,1,1])
    if index == 1:
        return CyclicModel([[0,0],[1,1],[2,2]],sources,sources,3,2,[1,1,1],[7,7,7],1,[1,1,1])
    if index == 2:
        sources = [[0,1,0,0,1],[1,0,0,0,-1]]
        return CyclicModel([[0,0],[1,1],[2,2]],sources,sources,3,2,[1,1,1],[7,7,7],1,[1,1,1])
    if index == 3:
        return CyclicModel([[1],[2],[0]],sources,sources,3,1,[1,1,1],[7,7,7],1,[1,1,1])
    if index == 4:
        return CyclicModel([[0,1],[1],[2]],sources,sources,3,1,[0,0,0],[7,7,7],1,[1,1,1])
    if index == 5:
        sources = [[1,2,1,0,0],[2,1,-1,0,0],[1,2,0,-1,0],[2,1,0,1,0],
            [1,2,1,-1,0],[2,1,-1,1,0]]
        var domain: List[List[Int]] = [[1,2,1,0,0],[2,1,-1,0,0],[1,2,0,-1,0],[2,1,0,1,0]]
        return CyclicModel([[0,0],[1],[2]],sources,domain,6,1,[0,1,1],[9,18,36],3,[1,2,4])
    raise Error("local fixture outside 0..5")


def local_fixture(index: Int) raises -> LocalAdmissibility:
    return build_local_admissibility(local_fixture_model(index))


def singular_fixture_model() -> CyclicModel:
    var roots: List[List[Int]] = [[0,0,0,0,0]]
    return CyclicModel([[0],[0],[0]],roots,roots,3,1,[0,0,0],[7,0,0],1,[1,0,0])


def singular_lift_control() raises -> List[List[Int]]:
    """Two explicit lifts refute all-lift representation without injection.

    This is a finite witness, not an enumeration of the singular incoming
    type.  The generic bounded constructor correctly refuses that type.
    """
    var model = singular_fixture_model()
    validate_cyclic_model(model)
    var tables = build_affine_trace_tables(model.images)
    if Mat3(tables.incidence).det() != 0:
        raise Error("local singular control ceased to be singular")
    var nonempty = 0
    for top in range(3):
        for bottom in range(3):
            # Every word is the literal one-letter word [0], so both marks
            # have position zero and empty prefix.  Keep all nine choices.
            if model.images[top] != [0] or model.images[bottom] != [0]:
                raise Error("local singular control lost a literal zero-prefix mark")
            var pair_mask = cyclic_image(model.tiles[top],3,1,0) & cyclic_image(model.tiles[bottom],3,1,0)
            if pair_mask != 0:
                nonempty += 1
                if top != 0 or bottom != 0 or pair_mask != 7:
                    raise Error("local singular control has an unexpected nonempty pair")
    if nonempty != 1:
        raise Error("local singular control nonempty pair count changed")
    var lifts: List[List[Int]] = [[0,0,0,0,0],[0,0,1,-1,0]]
    var result = List[List[Int]]()
    for ancestor in lifts:
        var delta = _triple(ancestor,2)
        var mapped = matvec(_rows3(tables.incidence),delta)
        var mask = overlap_mask(model,ancestor)
        var inside = 1 if ancestor == model.domain[0] else 0
        if mapped != [0,0,0] or mask != 7:
            raise Error("local singular lift fails its exact equation or nonempty overlap")
        result.append([ancestor[0],ancestor[1],delta[0],delta[1],delta[2],mapped[0],mapped[1],mapped[2],mask,inside])
    return result^
