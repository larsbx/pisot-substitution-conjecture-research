"""Canonical bounded serialization of the original archived C4 tables.

The native source-bound refinement is checked before serialization.  Packed
rows retain the original state IDs, weights, ordered positional slots and
first-discovery witnesses.  A separate balanced lookup authenticates a left
inverse of the exact track-swap key; it never renumbers the archived graph.

The resulting data require the independent Lean checker.  Native acceptance,
including these field checks, is not a Lean proof term.
"""

from std.collections import Dict
from finite_exact.bigint_z import (
    BigZ, bigz_from_i64, bigz_add, bigz_mul,
    bigz_abs_mod_small, bigz_abs_div_small,
)
from finite_exact.exact_decimal import bigz_decimal
from psc.c4_archived_graph_refinement import ArchivedRefinement, verify_archived_contraction
from psc.c4_literal_inverse_binding import swap_packet

comptime WEIGHT_RADIX = 1048576
comptime DEGREE_RADIX = 256
comptime STATE_RADIX = 33554432
comptime PARENT_RADIX = 16384
comptime BIRTH_SLOT_RADIX = 256
comptime DEPTH_RADIX = 32
comptime SLOT_RADIX = 8388608


def state_code(state: List[Int]) raises -> Int:
    if len(state) != 5 or state[0] < 0 or state[0] > 2 or state[1] < 0 or state[1] > 2:
        raise Error("archived payload state letter domain")
    for k in range(2,5):
        if state[k] < -32 or state[k] > 32:
            raise Error("archived payload coordinate budget; no truncation")
    return state[0]+4*state[1]+16*(state[2]+64)+2048*(state[3]+64)+262144*(state[4]+64)


def orbit_key(state: List[Int]) raises -> Int:
    var code = state_code(state)
    var other = state_code(swap_packet(state))
    return code if code < other else other


def slot_code(slot: List[Int], count: Int) raises -> Int:
    if count < 3 or count > 16000 or len(slot) != 4:
        raise Error("archived payload slot or graph dimensions")
    if slot[0] < 0 or slot[0] >= count:
        raise Error("archived payload target outside original domain")
    if slot[1] < 0 or slot[1] >= 15 or slot[2] < 0 or slot[2] >= 15:
        raise Error("archived payload literal digit outside complete inventory")
    if slot[3] < 0 or slot[3] > 1:
        raise Error("archived payload track-swap bit")
    return slot[0]+16384*slot[1]+262144*slot[2]+4194304*slot[3]


def _append(bits: BigZ, radix: Int, value: Int) raises -> BigZ:
    if value < 0 or value >= radix:
        raise Error("archived payload radix overflow; no truncation")
    return bigz_add(bigz_mul(bits,bigz_from_i64(Int64(radix))),bigz_from_i64(Int64(value)))


def pack_archived_row(state: List[Int], weight: Int, birth: List[Int], depth: Int,
                      slots: List[List[Int]], count: Int, row: Int) raises -> BigZ:
    """Low-to-high fields: 20,8,25,14,8,5 bits, then 23 bits per slot."""
    if count < 3 or count > 16000 or row < 0 or row >= count:
        raise Error("archived payload original row bounds")
    if weight < 1 or weight > 1000000 or len(slots) > 225 or len(birth) != 2:
        raise Error("archived payload weight, degree or birth shape")
    if row < 3:
        if birth[0] != -1 or birth[1] != -1 or depth != 0:
            raise Error("archived payload original root discovery")
    elif birth[0] < 0 or birth[0] >= row or birth[1] < 0 or birth[1] >= 225 or depth < 1:
        raise Error("archived payload incomplete earlier inverse ancestry")
    var code = state_code(state)
    var bits = BigZ()
    for k in range(len(slots)-1,-1,-1):
        bits = _append(bits,SLOT_RADIX,slot_code(slots[k],count))
    bits = _append(bits,DEPTH_RADIX,depth)
    bits = _append(bits,BIRTH_SLOT_RADIX,birth[1]+1)
    bits = _append(bits,PARENT_RADIX,birth[0]+1)
    bits = _append(bits,STATE_RADIX,code)
    bits = _append(bits,DEGREE_RADIX,len(slots))
    return _append(bits,WEIGHT_RADIX,weight)


def unpack_archived_fields(value: BigZ) raises -> List[List[Int]]:
    """Native round-trip control; independent Python also decodes the bytes.

    The first record contains weight, degree, state code, birth parent+1,
    birth slot+1 and depth.  Subsequent records are the original four slot
    fields.  Hidden high payloads are refused rather than ignored.
    """
    if value.sign < 0:
        raise Error("negative archived payload")
    var bits = value.copy()
    var radices: List[Int] = [WEIGHT_RADIX,DEGREE_RADIX,STATE_RADIX,PARENT_RADIX,BIRTH_SLOT_RADIX,DEPTH_RADIX]
    var header = List[Int]()
    for radix in radices:
        header.append(Int(bigz_abs_mod_small(bits,UInt64(radix))))
        bits = bigz_abs_div_small(bits,UInt64(radix))
    var result = List[List[Int]]()
    var degree = header[1]
    result.append(header^)
    for _ in range(degree):
        var code = Int(bigz_abs_mod_small(bits,UInt64(SLOT_RADIX)))
        bits = bigz_abs_div_small(bits,UInt64(SLOT_RADIX))
        result.append([code%16384,(code//16384)%16,(code//262144)%16,code//4194304])
    if not bits.is_zero():
        raise Error("hidden archived payload above the last positional slot")
    return result^


def packed_rows(binding: ArchivedRefinement, weights: List[Int]) raises -> List[BigZ]:
    var count = len(binding.graph.states)
    if len(weights) != count or len(binding.slots) != count or len(binding.births) != count or len(binding.depths) != count:
        raise Error("archived payload missing state, weight, row or ancestry record")
    var result = List[BigZ](capacity=count)
    for row in range(count):
        result.append(pack_archived_row(binding.graph.states[row],weights[row],binding.births[row],binding.depths[row],binding.slots[row],count,row))
    return result^


def lookup_order(binding: ArchivedRefinement) raises -> List[Int]:
    """Sort an auxiliary exact orbit-key index; preserve every original ID."""
    var keys = List[Int]()
    var ids = Dict[Int,Int]()
    for row in range(len(binding.graph.states)):
        var key = orbit_key(binding.graph.states[row])
        if key in ids:
            raise Error("archived payload repeated track-swap orbit")
        ids[key] = row
        keys.append(key)
    sort(keys)
    var result = List[Int](capacity=len(keys))
    for key in keys:
        result.append(ids[key])
    return result^


def _emit_lookup_records(binding: ArchivedRefinement, order: List[Int], start: Int, count: Int, path: Int) raises:
    if count == 0:
        return
    var left = count//2
    var row = order[start+left]
    print("lookup",binding.graph.fixture,path,orbit_key(binding.graph.states[row]),row)
    _emit_lookup_records(binding,order,start,left,2*path)
    _emit_lookup_records(binding,order,start+left+1,count-left-1,2*path+1)


def emit_archived_payload(binding: ArchivedRefinement, weights: List[Int], sweeps: Int) raises:
    """Every decoded source record and every raw payload/index record."""
    var gap = verify_archived_contraction(binding,weights)
    var rows = packed_rows(binding,weights)
    var order = lookup_order(binding)
    var fixture = binding.graph.fixture
    var maximum_depth = 0
    for depth in binding.depths:
        if depth > maximum_depth:
            maximum_depth = depth
    print("graph",fixture,binding.period,binding.radii[0],binding.radii[1],binding.direction,len(binding.graph.states),binding.edges,binding.graph.residue_rejections,binding.graph.box_rejections,binding.swapped,binding.repeated,maximum_depth,sweeps,gap)
    for parent in range(3):
        var line = String("image ")+String(fixture)+String(" ")+String(parent)+String(" ")+String(len(binding.images[parent]))
        for letter in binding.images[parent]:
            line += String(" ")+String(letter)
        print(line)
    for i in range(len(binding.digits)):
        var line = String("digit ")+String(fixture)+String(" ")+String(i)
        for value in binding.digits[i]:
            line += String(" ")+String(value)
        print(line)
    for i in range(len(binding.graph.states)):
        var state = binding.graph.states[i].copy()
        print("node",fixture,i,state[0],state[1],state[2],state[3],state[4],weights[i],binding.births[i][0],binding.births[i][1],binding.depths[i])
        print("row",fixture,i,len(binding.slots[i]))
        for ordinal in range(len(binding.slots[i])):
            var slot = binding.slots[i][ordinal].copy()
            print("slot",fixture,i,ordinal,slot[0],slot[1],slot[2],slot[3])
    for i in range(len(rows)):
        print("packed",fixture,i,bigz_decimal(rows[i]))
    _emit_lookup_records(binding,order,0,len(order),1)
