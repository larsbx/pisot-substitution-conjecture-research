"""Literal finite witnesses for the cut-to-prefix embedding theorem.

The original named period-two prefix words are kept separate. Every output
position retains its source parent ordinal and complete local before/after
mark. The reference occurrence is in the authentic sigma^2(0) prefix; even
inflation therefore remains a prefix of that same word. No finite output
claims compact overlap membership, limiting proximity, or positive measure.

All matrix and vector arithmetic uses checked vendored primitives. Resource
limits refuse construction; they are not geometric exclusions.
"""

from finite_exact.checked_int import checked_add
from finite_linear_algebra.integer_matrix import matmul
from finite_linear_algebra.integer_vector import matvec, sub
from substitution_dynamics.substitution import Substitution, validate_word
from psc.words import parikh
from psc.c4_nonunit_residue_occupancy import same_vector
from psc.c4_finite_cylinder_overlap import fixture_images

comptime EMBEDDING_POWER_CAP = 6
comptime EMBEDDING_SOURCE_CAP = 8
comptime EMBEDDING_WORD_CAP = 100000


def literal_slice(word: List[Int], start: Int, end: Int) raises -> List[Int]:
    if start < 0 or start > end or end > len(word):
        raise Error("cut-prefix literal slice outside actual word")
    var result = List[Int]()
    for i in range(start,end):
        result.append(word[i])
    return result^


def bounded_inflate(images: List[List[Int]], source: List[Int], depth: Int,
        word_cap: Int = EMBEDDING_WORD_CAP) raises -> List[Int]:
    if depth < 0 or depth > EMBEDDING_POWER_CAP+2 or word_cap < 1 or word_cap > EMBEDDING_WORD_CAP:
        raise Error("cut-prefix inflation exceeds declared depth or word budget")
    if len(images) != 3 or len(source) > word_cap:
        raise Error("cut-prefix source shape or budget")
    var sigma = Substitution.checked(images)
    validate_word(source,3)
    var word = source.copy()
    for _ in range(depth):
        var length = 0
        for letter in word:
            if len(sigma.images[letter]) > word_cap-length:
                raise Error("cut-prefix complete inflation exceeds word budget")
            length += len(sigma.images[letter])
        word = sigma.apply(word)
    return word^


def incidence_power(images: List[List[Int]], depth: Int) raises -> List[List[Int]]:
    if depth < 0 or depth > EMBEDDING_POWER_CAP:
        raise Error("cut-prefix matrix depth exceeds declared budget")
    if len(images) != 3:
        raise Error("cut-prefix incidence needs three source letters")
    var sigma = Substitution.checked(images)
    var matrix = sigma.incidence()
    var power: List[Int] = [1,0,0,0,1,0,0,0,1]
    for _ in range(depth):
        power = matmul(power,matrix,3)
    return [[power[0],power[1],power[2]],
            [power[3],power[4],power[5]],
            [power[6],power[7],power[8]]]


struct CutPrefixWitness(Copyable, Movable):
    # fixture,k,output position,parent ordinal,local index,parent letter,
    # following letter,reference parent ordinal,reference output position.
    var address: List[Int]
    var source: List[Int]
    var reference: List[Int]
    var parent_before: List[Int]
    var parent_after: List[Int]
    var local_before: List[Int]
    var local_after: List[Int]
    var point: List[Int]
    var reference_point: List[Int]
    var correction: List[Int]
    # At q=0..k, explicit integer w_q with x-y=M^q w_q.
    var residue_witnesses: List[List[Int]]

    def __init__(out self):
        self.address = List[Int]()
        self.source = List[Int]()
        self.reference = List[Int]()
        self.parent_before = List[Int]()
        self.parent_after = List[Int]()
        self.local_before = List[Int]()
        self.local_after = List[Int]()
        self.point = List[Int]()
        self.reference_point = List[Int]()
        self.correction = List[Int]()
        self.residue_witnesses = List[List[Int]]()


def build_cut_prefix_witness(fixture: Int, source: List[Int], depth: Int,
        position: Int, word_cap: Int = EMBEDDING_WORD_CAP) raises -> CutPrefixWitness:
    if depth < 0 or depth > EMBEDDING_POWER_CAP or depth % 2 != 0:
        raise Error("named cut-prefix word only supports declared even powers")
    if len(source) < 1 or len(source) > EMBEDDING_SOURCE_CAP:
        raise Error("cut-prefix source outside fixed finite source budget")
    validate_word(source,3)
    var images = fixture_images(fixture)
    var output = bounded_inflate(images,source,depth,word_cap)
    if position < 0 or position >= len(output):
        raise Error("terminal or outside cut has no following occurrence")
    var blocks = List[List[Int]]()
    for a in range(3):
        blocks.append(bounded_inflate(images,[a],depth,word_cap))
    var parent = 0
    var start = 0
    while parent < len(source) and position >= start+len(blocks[source[parent]]):
        start = checked_add(start,len(blocks[source[parent]]))
        parent += 1
    if parent >= len(source):
        raise Error("complete output address has no parent")
    var local = position-start
    var letter = source[parent]
    var reference = bounded_inflate(images,[0],2,word_cap)
    var reference_parent = -1
    for j in range(len(reference)):
        if reference[j] == letter and reference_parent == -1:
            reference_parent = j
    if reference_parent < 0:
        raise Error("parent letter missing from authenticated reference prefix")
    var ref_start = 0
    for j in range(reference_parent):
        ref_start = checked_add(ref_start,len(blocks[reference[j]]))
    var ref_position = checked_add(ref_start,local)
    var ref_output = bounded_inflate(images,reference,depth,word_cap)
    var authentic_output = bounded_inflate(images,[0],depth+2,word_cap)
    if not same_vector(ref_output,authentic_output) or ref_position >= len(ref_output):
        raise Error("reference output differs from original fixed-word prefix")
    if output[position] != ref_output[ref_position] or output[position] != blocks[letter][local]:
        raise Error("embedding changed the following literal letter")
    var result = CutPrefixWitness()
    result.address = [fixture,depth,position,parent,local,letter,output[position],reference_parent,ref_position]
    result.source = source.copy()
    result.reference = reference.copy()
    result.parent_before = literal_slice(source,0,parent)
    result.parent_after = literal_slice(source,parent+1,len(source))
    result.local_before = literal_slice(blocks[letter],0,local)
    result.local_after = literal_slice(blocks[letter],local+1,len(blocks[letter]))
    result.point = parikh(literal_slice(output,0,position))
    result.reference_point = parikh(literal_slice(ref_output,0,ref_position))
    result.correction = sub(parikh(result.parent_before),parikh(literal_slice(reference,0,reference_parent)))
    var difference = sub(result.point,result.reference_point)
    if not same_vector(difference,matvec(incidence_power(images,depth),result.correction)):
        raise Error("literal cut-prefix correction identity failed")
    for q in range(depth+1):
        var witness = matvec(incidence_power(images,depth-q),result.correction)
        if not same_vector(difference,matvec(incidence_power(images,q),witness)):
            raise Error("cut-prefix residue witness failed exact multiplication")
        result.residue_witnesses.append(witness^)
    return result^


def verify_cut_prefix_witness(packet: CutPrefixWitness) raises:
    """Reconstruct all source-bound fields; never trust mutable packet metadata."""
    if len(packet.address) != 9:
        raise Error("cut-prefix address shape")
    var expected = build_cut_prefix_witness(packet.address[0],packet.source,
        packet.address[1],packet.address[2])
    if not same_vector(packet.address,expected.address) or not same_vector(packet.reference,expected.reference):
        raise Error("cut-prefix source/reference/full-address mismatch")
    if not same_vector(packet.parent_before,expected.parent_before) or not same_vector(packet.parent_after,expected.parent_after):
        raise Error("cut-prefix parent word split mismatch")
    if not same_vector(packet.local_before,expected.local_before) or not same_vector(packet.local_after,expected.local_after):
        raise Error("cut-prefix local occurrence split mismatch")
    if not same_vector(packet.point,expected.point) or not same_vector(packet.reference_point,expected.reference_point):
        raise Error("cut-prefix literal prefix vector mismatch")
    if not same_vector(packet.correction,expected.correction):
        raise Error("cut-prefix signed correction mismatch")
    if len(packet.residue_witnesses) != len(expected.residue_witnesses):
        raise Error("cut-prefix incomplete residue witness inventory")
    for q in range(len(packet.residue_witnesses)):
        if not same_vector(packet.residue_witnesses[q],expected.residue_witnesses[q]):
            raise Error("cut-prefix altered residue witness")


def verify_balanced_cut(top: CutPrefixWitness, bottom: CutPrefixWitness) raises:
    verify_cut_prefix_witness(top)
    verify_cut_prefix_witness(bottom)
    if top.address[0] != bottom.address[0] or top.address[1] != bottom.address[1]:
        raise Error("two-track cut uses different original source or depth")
    if not same_vector(top.point,bottom.point):
        raise Error("two-track cut has unequal literal Parikh prefixes")


def integer_array(values: List[Int]) -> String:
    var result = String("[")
    for i in range(len(values)):
        if i > 0:
            result += String(",")
        result += String(values[i])
    result += String("]")
    return result^


def witness_json(packet: CutPrefixWitness) -> String:
    var result = String('{"address":')+integer_array(packet.address)
    result += String(',"source":')+integer_array(packet.source)
    result += String(',"reference":')+integer_array(packet.reference)
    result += String(',"parent_before":')+integer_array(packet.parent_before)
    result += String(',"parent_after":')+integer_array(packet.parent_after)
    result += String(',"local_before":')+integer_array(packet.local_before)
    result += String(',"local_after":')+integer_array(packet.local_after)
    result += String(',"point":')+integer_array(packet.point)
    result += String(',"reference_point":')+integer_array(packet.reference_point)
    result += String(',"correction":')+integer_array(packet.correction)
    result += String(',"residue_witnesses":[')
    for q in range(len(packet.residue_witnesses)):
        if q > 0:
            result += String(",")
        result += integer_array(packet.residue_witnesses[q])
    result += String("]}")
    return result^
