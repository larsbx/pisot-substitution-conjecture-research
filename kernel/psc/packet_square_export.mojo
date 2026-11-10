"""Packet-square export (schema packet-square-v1) of the target-aware packet graph.

`psc.target_packets.build_packets` interns every actual occurrence pair of the
complete balanced-pair automaton, roots at all position pairs of every
noncoincident normalised state, and expands each packet over the full product
of its two image digits. It counts a digit pair whose descendants fall into
different blocks of the literal ordered factorisation (a *split*) and keeps no
record of it. This module adds, without changing `target_packets.mojo` or
`target_packet_report.mojo` (so the archived `target-aware-bpa-v1` bytes stay
reproducible):

* the full digit star of every packet, row-major in (top digit, bottom digit),
  with each split carrying the ordinals of the two blocks that hold the two
  descendants, recomputed from the graph's own expansions and refused unless
  the number of splits equals `split_count` and every packet edge occurs once;
* the birth of every non-root packet (source, top digit, bottom digit of its
  first incoming edge; the source always has a smaller id);
* a key order: the packet ids sorted by (state, sign, top, bottom,
  factor_edge + 1), which is the numeric order of the Lean `Table.keyCode`;
* ordered hub rows (`factor_hub_residual` for every factor of every
  noncoincident state and every hub letter; undefined bits stay -1 and are
  printed as `null` / `none`, never coerced);
* the PIP status of the incidence matrix, recorded and never used as a filter;
* `verify_packet_square`, a second computation of every row, star, birth, key
  and hub bit from literal words (`apply_substitution`,
  `coincidence_boundaries`, prefix counts). Its own checks read none of the
  packet graph's caches (`child_at`, `adj`, `expansions`). It is not
  independent of everything: it reuses the `psc.bpa` primitives, calls
  `target_packets.verify_packet` (a literal replay) and `replay_edge` (which
  recomputes each child through `descendant`, so through the expansions), and
  compares keys with the producer's own key tuple `_key_parts` (the
  regression test checks the order again with a Lean key code of its own).
  Any mismatch raises with the layer it belongs to;
* JSONL emission (schema `packet-square-v1`) and Lean emission of the record
  `Psc.PacketCertificate.Table (Fin 3)`, which the Lean checker `Table.check`
  decides: it re-derives every factor row, every packet row except its birth,
  every digit star and every listed hub row from `Psc.Reduction.red`, and checks
  that each birth names an incoming edge from an earlier row.

`emit_packet_square_lean` and `packet_square_lean` take a `command` argument
(the regeneration command, printed in the module's leading comment), and
`PacketSquare` carries the ordered hub rows `hubs`. On refusal the driver prints
the `budget` row and nothing after it, except that an exhausted automaton
budget (states or length) is followed by one `inconclusive` row naming that
budget, as `target_aware_bpa.mojo` does; a packet or edge cap prints only the
`budget` row. The record and its checker are documented in
`proof/PscVerif/PscVerif/PacketCertificate.lean`; the stop/go note is
`docs/packet-square-stop-go-2026-11-10.md`.

What is established here is executable and finite: for the given substitution
and caps, the exported table is the graph `build_packets` produced, and its
rows agree with a second literal computation. What is *not* established here:
that the table is accepted by the Lean checker (the Lean side decides that),
anything about states outside the table, any statement about absolute
occurrences in the iterates, and nothing about C4, G1, #84, #138, #139 or PSC.
`--target sync-right` (stop-at-success at a noncoincident state) is outside
this schema and refuses. A capped automaton, packet cap or edge cap refuses
and produces no table: an exhausted budget is not a verdict.

Every refusal names the first layer whose check fails: L0 input and
configuration, L1 PIP record, L2 complete automaton and states, L3 literal
ordered factorisation, L4 literal packet rows, L5 full digit stars, L6 roots,
keys and births, L7 hub bits. These are the layers of the Lean checker's
clauses (`statesOK`, `factorsOK`, `packetOK`, `starOK`, `rootsOK`/`keysOK`/
`birthOK`, `hubsOK`); the Mojo checks are a second computation, not that one.
"""

from psc.target_packets import (
    PacketGraph, PacketKey, OccurrenceAddress, build_packets, replay_edge, verify_packet,
)
from psc.target_packet_report import ints_json
from psc.packet_hub_analysis import factor_hub_residual
from psc.bpa import apply_substitution, coincidence_boundaries, normalise, seed_states, substitution_incidence
from psc.words import Pair, is_balanced
from psc.pisot import is_pip
from finite_linear_algebra.mat3 import Mat3
from substitution_dynamics.automaton import Automaton


comptime PACKET_SQUARE_SCHEMA = "packet-square-v1"
comptime SYNC_RIGHT_REFUSAL = "synchronize_right is outside packet-square-v1"


struct StarEntry(ImplicitlyCopyable, Copyable, Movable, Equatable):
    """One digit pair of a packet's full star.

    A child entry has `destination >= 0` and both ordinals `-1`; a split entry
    has `destination == -1` and the ordinals of the blocks (in the literal
    ordered factorisation of the inflated parent) holding the top and the
    bottom descendant.
    """

    var top_digit: Int
    var bottom_digit: Int
    var destination: Int
    var top_ordinal: Int
    var bottom_ordinal: Int

    def __init__(out self, top_digit: Int, bottom_digit: Int, destination: Int, top_ordinal: Int, bottom_ordinal: Int):
        self.top_digit = top_digit
        self.bottom_digit = bottom_digit
        self.destination = destination
        self.top_ordinal = top_ordinal
        self.bottom_ordinal = bottom_ordinal

    def __eq__(self, o: StarEntry) -> Bool:
        return (self.top_digit == o.top_digit and self.bottom_digit == o.bottom_digit
                and self.destination == o.destination and self.top_ordinal == o.top_ordinal
                and self.bottom_ordinal == o.bottom_ordinal)

    def __ne__(self, o: StarEntry) -> Bool:
        return not (self == o)

    def is_split(self) -> Bool:
        return self.destination == -1


struct HubRow(Copyable, Movable):
    """Ordered hub bits of one noncoincident state for one hub letter.

    `factors` are the state's factor ids in ordinal order; `bits[j]` is
    `factor_hub_residual` of `factors[j]`, `-1` where it is undefined.
    """

    var state: Int
    var hub: Int
    var factors: List[Int]
    var bits: List[Int]

    def __init__(out self, state: Int, hub: Int, var factors: List[Int], var bits: List[Int]):
        self.state = state
        self.hub = hub
        self.factors = factors^
        self.bits = bits^


struct PacketSquare(Copyable, Movable):
    """The packet graph together with the data the Lean record needs."""

    var graph: PacketGraph
    var stars: List[List[StarEntry]]
    var births: List[List[Int]]
    var key_order: List[Int]
    var hubs: List[HubRow]
    var pip: Bool

    def __init__(out self, var graph: PacketGraph, var stars: List[List[StarEntry]], var births: List[List[Int]], var key_order: List[Int], var hubs: List[HubRow], pip: Bool):
        self.graph = graph^
        self.stars = stars^
        self.births = births^
        self.key_order = key_order^
        self.hubs = hubs^
        self.pip = pip


def _msg(layer: String, what: String) -> String:
    return String("packet-square ") + layer + ": " + what


def parse_packet_square_target(text: String) raises -> Int:
    """`any` is -1, a letter is itself; `sync-right` and anything else refuse."""
    if text == "any":
        return -1
    if text == "0":
        return 0
    if text == "1":
        return 1
    if text == "2":
        return 2
    if text == "sync-right":
        raise Error(SYNC_RIGHT_REFUSAL)
    raise Error("target must be any, 0, 1 or 2 (sync-right is outside packet-square-v1)")


# ---------------------------------------------------------------------------
# Producer: stars, births, key order and hub rows from the packet graph.
# ---------------------------------------------------------------------------


def packet_stars(g: PacketGraph) raises -> List[List[StarEntry]]:
    """Full digit star of every packet, from the graph's expansions.

    Empty at a coincidence packet (Mojo does not expand those). A success
    packet in a noncoincident state is refused: it can only arise in
    synchronize mode. Every edge of `g.adj[p]` must appear exactly once, in
    row-major digit order, and the number of split entries must equal
    `g.split_count`.
    """
    if g.synchronize:
        raise Error(SYNC_RIGHT_REFUSAL)
    var out = List[List[StarEntry]]()
    var splits = 0
    var used = 0
    for i in range(len(g.packets)):
        ref p = g.packets[i]
        if p.key.state_id < 0 or p.key.state_id >= g.bpa.size():
            raise Error(_msg("L5", "packet state outside the automaton"))
        var coincident = g.bpa.states[p.key.state_id].is_coincidence()
        if p.success and not coincident:
            raise Error(_msg("L5", "success at a noncoincident state is synchronize semantics"))
        var row = List[StarEntry]()
        if coincident:
            if len(g.adj[i]) != 0:
                raise Error(_msg("L5", "a coincidence packet has out-edges"))
        else:
            ref ex = g.expansions[2 * p.key.state_id + Int(p.key.sign == -1)]
            ref adj = g.adj[i]
            var cursor = 0
            for td in range(len(g.tables.sigma[p.top_letter])):
                for bd in range(len(g.tables.sigma[p.bottom_letter])):
                    var ti = ex.top_starts[p.key.top] + td
                    var bi = ex.bottom_starts[p.key.bottom] + bd
                    var ft = ex.child_at[ti]
                    var fb = ex.child_at[bi]
                    if ft < 0 or fb < 0:
                        raise Error(_msg("L5", "inflated position outside every factor"))
                    if ft != fb:
                        row.append(StarEntry(td, bd, -1, g.factors[ft].ordinal, g.factors[fb].ordinal))
                        splits += 1
                    else:
                        if cursor >= len(adj):
                            raise Error(_msg("L5", "a one-block digit pair has no packet edge"))
                        ref e = g.edges[adj[cursor]]
                        if e.source != i or e.top_digit != td or e.bottom_digit != bd:
                            raise Error(_msg("L5", "packet edges are not the row-major one-block digit pairs"))
                        row.append(StarEntry(td, bd, e.destination, -1, -1))
                        cursor += 1
            if cursor != len(adj):
                raise Error(_msg("L5", "a packet edge is not a star entry"))
            used += cursor
        out.append(row^)
    if splits != g.split_count:
        raise Error(_msg("L5", "recomputed split entries differ from split_count"))
    if used != len(g.edges):
        raise Error(_msg("L5", "star child entries differ from the edge count"))
    return out^


def packet_births(g: PacketGraph) raises -> List[List[Int]]:
    """`[source, top digit, bottom digit]` of the first incoming edge; `[]` at a root."""
    var out = List[List[Int]]()
    for i in range(len(g.packets)):
        var b = g.birth[i]
        if b == -1:
            if g.packets[i].key.factor_edge != -1:
                raise Error(_msg("L6", "a non-root packet has no birth edge"))
            out.append(List[Int]())
            continue
        if b < 0 or b >= len(g.edges) or g.packets[i].key.factor_edge == -1:
            raise Error(_msg("L6", "invalid birth edge"))
        ref e = g.edges[b]
        if e.destination != i or e.source < 0 or e.source >= i:
            raise Error(_msg("L6", "a birth does not come from an earlier packet"))
        out.append([e.source, e.top_digit, e.bottom_digit])
    return out^


def _key_parts(g: PacketGraph, id: Int) -> List[Int]:
    ref k = g.packets[id].key
    return [k.state_id, 1 if k.sign == 1 else 0, k.top, k.bottom, k.factor_edge + 1]


def _stable_counting_sort(order: List[Int], keys: List[Int], bound: Int) raises -> List[Int]:
    """Stable sort of `order` by `keys[order[k]]` in `[0, bound)`."""
    var counts = List[Int](length=bound + 1, fill=0)
    for k in range(len(order)):
        var key = keys[order[k]]
        if key < 0 or key >= bound:
            raise Error(_msg("L6", "key component outside its bound"))
        counts[key + 1] += 1
    for b in range(bound):
        counts[b + 1] += counts[b]
    var out = List[Int](length=len(order), fill=-1)
    for k in range(len(order)):
        var key = keys[order[k]]
        out[counts[key]] = order[k]
        counts[key] += 1
    return out^


def _max_state_length(g: PacketGraph) -> Int:
    var longest = 0
    for s in range(g.bpa.size()):
        longest = max(longest, g.bpa.states[s].length())
    return longest


def packet_key_order(g: PacketGraph) raises -> List[Int]:
    """Packet ids sorted by (state, sign, top, bottom, factor_edge + 1); a tie raises.

    Least-significant-digit counting sort, so no comparison callback. With
    `B = longest state + 1` and `F = factors + 1`, every component is below
    its bound, so this lexicographic order is the numeric order of the Lean
    key code `(((state*2 + sign)*B + top)*B + bottom)*F + (factor_edge + 1)`.
    """
    var n = len(g.packets)
    var bounds: List[Int] = [g.bpa.size(), 2, _max_state_length(g) + 1, _max_state_length(g) + 1, len(g.factors) + 1]
    var parts = List[List[Int]]()
    for _ in range(5):
        parts.append(List[Int]())
    for i in range(n):
        var kp = _key_parts(g, i)
        for c in range(5):
            parts[c].append(kp[c])
    var order = List[Int]()
    for i in range(n):
        order.append(i)
    for c in range(4, -1, -1):
        order = _stable_counting_sort(order, parts[c], bounds[c])
    for k in range(1, n):
        if _key_parts(g, order[k - 1]) == _key_parts(g, order[k]):
            raise Error(_msg("L6", "two packets share one key"))
    return order^


def packet_hub_rows(g: PacketGraph) raises -> List[HubRow]:
    """One row per noncoincident state (ascending) and hub letter 0, 1, 2."""
    var out = List[HubRow]()
    for s in range(g.bpa.size()):
        if g.bpa.states[s].is_coincidence():
            continue
        var ids = g.expansions[2 * s].factors.copy()
        for hub in range(3):
            var bits = List[Int]()
            for j in range(len(ids)):
                bits.append(factor_hub_residual(g, ids[j], hub))
            out.append(HubRow(s, hub, ids.copy(), bits^))
    return out^


def build_packet_square(sigma: List[List[Int]], a: Automaton, packet_cap: Int = 200000, edge_cap: Int = 2000000, target: Int = -1) raises -> PacketSquare:
    """`build_packets` (never in synchronize mode) plus the export data.

    `a` must be a complete automaton (`build_packets` refuses a capped one);
    packet and edge caps raise "... cap exhausted: diagnostic inconclusive".
    """
    if target < -1 or target > 2:
        raise Error(_msg("L0", "target must be -1 (any diagonal) or a letter 0..2"))
    var g = build_packets(sigma, a, packet_cap, edge_cap, target, False)
    var stars = packet_stars(g)
    var births = packet_births(g)
    var order = packet_key_order(g)
    var hubs = packet_hub_rows(g)
    var pip = is_pip(Mat3(substitution_incidence(sigma)))
    return PacketSquare(g^, stars^, births^, order^, hubs^, pip)


# ---------------------------------------------------------------------------
# Independent literal recomputation.
# ---------------------------------------------------------------------------


def _slice(w: List[Int], lo: Int, hi: Int) -> List[Int]:
    var out = List[Int]()
    for i in range(lo, hi):
        out.append(w[i])
    return out^


def _image_starts(sigma: List[List[Int]], w: List[Int]) -> List[Int]:
    var out: List[Int] = [0]
    for i in range(len(w)):
        out.append(out[i] + len(sigma[w[i]]))
    return out^


def _interval(cuts: List[Int], position: Int, layer: String) raises -> Int:
    """The `k` with `cuts[k] <= position < cuts[k + 1]` (binary search)."""
    if len(cuts) < 2 or position < cuts[0] or position >= cuts[len(cuts) - 1]:
        raise Error(_msg(layer, "position outside the cut list"))
    var lo = 0
    var hi = len(cuts) - 1
    while hi - lo > 1:
        var mid = (lo + hi) // 2
        if cuts[mid] <= position:
            lo = mid
        else:
            hi = mid
    return lo


def _prefix_defect(u: List[Int], v: List[Int], i: Int, j: Int) -> List[Int]:
    var out: List[Int] = [0, 0, 0]
    for k in range(i):
        out[u[k]] += 1
    for k in range(j):
        out[v[k]] -= 1
    return out^


struct _Inflation(Copyable, Movable):
    """Literal inflation of one normalised state: both sides, cuts, image starts."""

    var top: List[Int]
    var bottom: List[Int]
    var cuts: List[Int]
    var top_starts: List[Int]
    var bottom_starts: List[Int]

    def __init__(out self, sigma: List[List[Int]], p: Pair):
        self.top = apply_substitution(sigma, p.u)
        self.bottom = apply_substitution(sigma, p.v)
        self.cuts = coincidence_boundaries(self.top, self.bottom)
        self.top_starts = _image_starts(sigma, p.u)
        self.bottom_starts = _image_starts(sigma, p.v)


def _oriented_words(p: Pair, sign: Int) -> Pair:
    if sign == 1:
        return p.copy()
    return Pair(p.v, p.u)


def _check_address(a: OccurrenceAddress, source: Int, digit: Int, global_position: Int, local: Int) -> Bool:
    return (a.source_occurrence == source and a.within_image == digit
            and a.global_position == global_position and a.local_position == local)


def _cut_address(starts: List[Int], position: Int) raises -> List[Int]:
    """(source occurrence, digit) of `position` in the inflation with these image starts."""
    var i = _interval(starts, position, "L4")
    return [i, position - starts[i]]


def _literal_hub_side(p: Pair, hub: Int) -> Int:
    if p.u[0] == p.v[0]:
        return -1
    if p.u[0] == hub:
        return 0
    if p.v[0] == hub:
        return 1
    return -1


def verify_packet_square(sq: PacketSquare) raises -> Bool:
    """Recompute every exported row from literal words; raise on any mismatch.

    Checks, in layer order: the configuration (alphabet 3, nonerasing, target
    in -1..2, not synchronize mode); the PIP record; the states (balanced,
    normalised, irreducible, distinct, automaton not capped, every normalised
    swap seed listed); the factor rows (exactly the literal ordered
    factorisation of each noncoincident state, none under a coincidence, every
    block a listed state, every state reached from the seeds); every packet
    row (validity, both addresses, letters, residual, interior, success), by a
    direct prefix count and by `verify_packet`; every star (the full digit
    product, row-major, child or split with both literal ordinals, every child
    entry the literal descendant and replayed with `replay_edge`, the child
    entries in bijection with the edges, the split total equal to
    `split_count`); the roots (exactly `(state, +1, P, Q)` for all
    noncoincident states and positions, in id order); the key order (a
    permutation along which keys strictly increase, components within the
    Lean key-code bounds); the births (earlier source, the source's star
    holds the child entry, the first incoming edge); the hub rows (one per
    noncoincident state and hub, bits from the literal first letters, -1
    exactly where undefined).

    The birth check is stricter than the Lean `birthOK`, which accepts any
    earlier packet whose star holds the child entry: here the birth must be
    the first incoming edge in edge order, which is what `build_packets`
    records. The check is a second computation from literal words, independent
    of the packet graph's caches but not of `verify_packet`, `replay_edge` and
    `_key_parts` (see the module docstring).
    """
    ref g = sq.graph
    ref sigma = g.tables.sigma
    var n = len(g.packets)

    # L0: input and configuration.
    if len(sigma) != 3 or g.bpa.alphabet != 3:
        raise Error(_msg("L0", "alphabet is not three letters"))
    for a in range(3):
        if len(sigma[a]) == 0:
            raise Error(_msg("L0", "erasing image"))
        for j in range(len(sigma[a])):
            if sigma[a][j] < 0 or sigma[a][j] > 2:
                raise Error(_msg("L0", "image letter outside 0..2"))
    if g.synchronize:
        raise Error(_msg("L0", SYNC_RIGHT_REFUSAL))
    if g.target < -1 or g.target > 2:
        raise Error(_msg("L0", "target outside -1..2"))

    # L1: the PIP status is recorded, never a filter.
    if is_pip(Mat3(substitution_incidence(sigma))) != sq.pip:
        raise Error(_msg("L1", "recorded PIP status differs from the incidence matrix"))

    # L2: complete automaton; normalised irreducible distinct states; seeds.
    if g.bpa.capped:
        raise Error(_msg("L2", "capped automaton"))
    var index = Dict[String, Int]()
    for s in range(g.bpa.size()):
        ref p = g.bpa.states[s]
        if p.length() == 0 or len(p.v) != p.length() or not is_balanced(p) or normalise(p) != p:
            raise Error(_msg("L2", "state is not a normalised balanced pair"))
        if len(coincidence_boundaries(p.u, p.v)) != 2:
            raise Error(_msg("L2", "state is not irreducible"))
        if p.key() in index:
            raise Error(_msg("L2", "state listed twice"))
        index[p.key()] = s
    var seeds = seed_states()
    for i in range(len(seeds)):
        if normalise(seeds[i]).key() not in index:
            raise Error(_msg("L2", "a normalised swap seed is not listed"))

    # L3: factor rows are the literal ordered factorisation.
    var inflations = List[_Inflation]()
    for s in range(g.bpa.size()):
        inflations.append(_Inflation(sigma, g.bpa.states[s]))
    var factor_ids = List[List[Int]]()
    for _ in range(g.bpa.size()):
        factor_ids.append(List[Int]())
    for f in range(len(g.factors)):
        if g.factors[f].parent < 0 or g.factors[f].parent >= g.bpa.size():
            raise Error(_msg("L3", "factor parent outside the states"))
        factor_ids[g.factors[f].parent].append(f)
    var reached = List[Bool](length=g.bpa.size(), fill=False)
    var queue = List[Int]()
    for i in range(len(seeds)):
        var s = index[normalise(seeds[i]).key()]
        if not reached[s]:
            reached[s] = True
            queue.append(s)
    for s in range(g.bpa.size()):
        ref p = g.bpa.states[s]
        if p.is_coincidence():
            if len(factor_ids[s]) != 0:
                raise Error(_msg("L3", "factor row under a coincidence"))
            continue
        ref inf = inflations[s]
        if len(factor_ids[s]) != len(inf.cuts) - 1:
            raise Error(_msg("L3", "factor rows differ from the literal block count"))
        for k in range(len(inf.cuts) - 1):
            ref f = g.factors[factor_ids[s][k]]
            var raw = Pair(_slice(inf.top, inf.cuts[k], inf.cuts[k + 1]), _slice(inf.bottom, inf.cuts[k], inf.cuts[k + 1]))
            var canonical = normalise(raw)
            if canonical.key() not in index:
                raise Error(_msg("L3", "a literal block is not a listed state"))
            var sign = 1 if raw == canonical else -1
            if (f.ordinal != k or f.child != index[canonical.key()] or f.sign != sign
                    or f.start != inf.cuts[k] or f.end != inf.cuts[k + 1] or f.total != len(inf.top)):
                raise Error(_msg("L3", "factor row differs from the literal ordered factorisation"))
    var head = 0
    while head < len(queue):
        var s = queue[head]
        head += 1
        for k in range(len(factor_ids[s])):
            var c = g.factors[factor_ids[s][k]].child
            if not reached[c]:
                reached[c] = True
                queue.append(c)
    if len(queue) != g.bpa.size():
        raise Error(_msg("L3", "a listed state is not reached from the seeds"))

    # L4: literal packet rows.
    if len(g.birth) != n or len(g.adj) != n:
        raise Error(_msg("L4", "packet tables of different lengths"))
    for i in range(n):
        ref p = g.packets[i]
        var s = p.key.state_id
        if s < 0 or s >= g.bpa.size() or (p.key.sign != 1 and p.key.sign != -1):
            raise Error(_msg("L4", "packet state or orientation out of range"))
        var block = _oriented_words(g.bpa.states[s], p.key.sign)
        if p.key.top < 0 or p.key.bottom < 0 or p.key.top >= block.length() or p.key.bottom >= block.length():
            raise Error(_msg("L4", "packet position outside its block"))
        if p.key.factor_edge == -1:
            if p.key.sign != 1:
                raise Error(_msg("L4", "a root outside the normalised orientation"))
            if (not _check_address(p.top_address, p.key.top, -1, p.key.top, p.key.top)
                    or not _check_address(p.bottom_address, p.key.bottom, -1, p.key.bottom, p.key.bottom)):
                raise Error(_msg("L4", "root address is not the root sentinel"))
        else:
            if p.key.factor_edge < 0 or p.key.factor_edge >= len(g.factors):
                raise Error(_msg("L4", "factor edge out of range"))
            ref f = g.factors[p.key.factor_edge]
            if f.child != s:
                raise Error(_msg("L4", "factor child is not the packet state"))
            var parent_sign = p.key.sign * f.sign
            ref parent = g.bpa.states[f.parent]
            if parent.is_coincidence():
                raise Error(_msg("L4", "packet born under a coincidence"))
            ref inf = inflations[f.parent]
            var ptop = inf.top.copy() if parent_sign == 1 else inf.bottom.copy()
            var pbot = inf.bottom.copy() if parent_sign == 1 else inf.top.copy()
            var pts = inf.top_starts.copy() if parent_sign == 1 else inf.bottom_starts.copy()
            var pbs = inf.bottom_starts.copy() if parent_sign == 1 else inf.top_starts.copy()
            var lo = inf.cuts[f.ordinal]
            var hi = inf.cuts[f.ordinal + 1]
            if _slice(ptop, lo, hi) != block.u or _slice(pbot, lo, hi) != block.v:
                raise Error(_msg("L4", "the oriented block is not the recorded child of its oriented parent"))
            var gt = lo + p.key.top
            var gb = lo + p.key.bottom
            var at = _cut_address(pts, gt)
            var ab = _cut_address(pbs, gb)
            if (not _check_address(p.top_address, at[0], at[1], gt, p.key.top)
                    or not _check_address(p.bottom_address, ab[0], ab[1], gb, p.key.bottom)):
                raise Error(_msg("L4", "occurrence address differs from the literal cut address"))
        if p.top_letter != block.u[p.key.top] or p.bottom_letter != block.v[p.key.bottom]:
            raise Error(_msg("L4", "selected letters differ from the block"))
        var r = _prefix_defect(block.u, block.v, p.key.top, p.key.bottom)
        if p.residual.x != r[0] or p.residual.y != r[1] or p.residual.z != r[2]:
            raise Error(_msg("L4", "residual differs from the literal prefix defect"))
        var interior = False
        if p.key.factor_edge >= 0:
            interior = p.key.top == 0 and p.key.bottom == 0 and g.factors[p.key.factor_edge].ordinal > 0
        if p.interior != interior:
            raise Error(_msg("L4", "interior flag differs from the birth ordinal"))
        var success = interior and block.u == block.v and (g.target == -1 or block.u[0] == g.target)
        if p.success != success:
            raise Error(_msg("L4", "success flag differs from interior coincidence and target"))
        if not verify_packet(g, p):
            raise Error(_msg("L4", "packet fails the target_packets literal replay"))

    # L5: full literal digit stars, child entries in bijection with edges.
    if len(sq.stars) != n:
        raise Error(_msg("L5", "one star per packet is required"))
    var width = 1
    for a in range(3):
        width = max(width, len(sigma[a]))
    var edge_at = Dict[Int, Int]()
    for eid in range(len(g.edges)):
        ref e = g.edges[eid]
        if e.source < 0 or e.source >= n or e.destination < 0 or e.destination >= n:
            raise Error(_msg("L5", "edge endpoint out of range"))
        if e.top_digit < 0 or e.top_digit >= width or e.bottom_digit < 0 or e.bottom_digit >= width:
            raise Error(_msg("L5", "edge digit out of range"))
        var code = (e.source * width + e.top_digit) * width + e.bottom_digit
        if code in edge_at:
            raise Error(_msg("L5", "two edges share a source and a digit pair"))
        edge_at[code] = eid
    var splits = 0
    var children = 0
    for i in range(n):
        ref p = g.packets[i]
        ref star = sq.stars[i]
        ref state = g.bpa.states[p.key.state_id]
        if state.is_coincidence():
            if len(star) != 0:
                raise Error(_msg("L5", "a coincidence packet has a nonempty star"))
            continue
        ref inf = inflations[p.key.state_id]
        var top = inf.top.copy() if p.key.sign == 1 else inf.bottom.copy()
        var bottom = inf.bottom.copy() if p.key.sign == 1 else inf.top.copy()
        var ts = inf.top_starts.copy() if p.key.sign == 1 else inf.bottom_starts.copy()
        var bs = inf.bottom_starts.copy() if p.key.sign == 1 else inf.top_starts.copy()
        var cursor = 0
        for td in range(len(sigma[p.top_letter])):
            for bd in range(len(sigma[p.bottom_letter])):
                var ti = ts[p.key.top] + td
                var bi = bs[p.key.bottom] + bd
                var k = _interval(inf.cuts, ti, "L5")
                var k2 = _interval(inf.cuts, bi, "L5")
                if cursor >= len(star):
                    raise Error(_msg("L5", "star is missing a digit pair"))
                var entry = star[cursor]
                cursor += 1
                if entry.top_digit != td or entry.bottom_digit != bd:
                    raise Error(_msg("L5", "star is not the row-major digit product"))
                if k != k2:
                    if entry.destination != -1 or entry.top_ordinal != k or entry.bottom_ordinal != k2:
                        raise Error(_msg("L5", "split entry differs from the literal ordinals"))
                    splits += 1
                    continue
                if entry.destination < 0 or entry.destination >= n or entry.top_ordinal != -1 or entry.bottom_ordinal != -1:
                    raise Error(_msg("L5", "child entry is malformed or out of range"))
                var raw = Pair(_slice(top, inf.cuts[k], inf.cuts[k + 1]), _slice(bottom, inf.cuts[k], inf.cuts[k + 1]))
                var canonical = normalise(raw)
                var child_sign = p.key.sign if canonical.is_coincidence() else (1 if raw == canonical else -1)
                var expected = PacketKey(index[canonical.key()], child_sign, ti - inf.cuts[k], bi - inf.cuts[k], factor_ids[p.key.state_id][k])
                ref q = g.packets[entry.destination]
                if q.key != expected:
                    raise Error(_msg("L5", "child entry is not the literal descendant"))
                if (not _check_address(q.top_address, p.key.top, td, ti, ti - inf.cuts[k])
                        or not _check_address(q.bottom_address, p.key.bottom, bd, bi, bi - inf.cuts[k])):
                    raise Error(_msg("L5", "child entry does not carry both source occurrences and digits"))
                var code = (i * width + td) * width + bd
                if code not in edge_at:
                    raise Error(_msg("L5", "child entry has no packet edge"))
                var eid = edge_at[code]
                if g.edges[eid].destination != entry.destination or not replay_edge(g, eid):
                    raise Error(_msg("L5", "child entry fails the edge replay"))
                children += 1
        if cursor != len(star):
            raise Error(_msg("L5", "star has entries beyond the digit product"))
    if splits != g.split_count:
        raise Error(_msg("L5", "split entries differ from split_count"))
    if children != len(g.edges):
        raise Error(_msg("L5", "child entries differ from the edges"))

    # L6: roots, key order, births.
    var root_ids = List[Int]()
    for i in range(n):
        if g.packets[i].key.factor_edge == -1:
            root_ids.append(i)
    var r = 0
    for s in range(g.bpa.size()):
        if g.bpa.states[s].is_coincidence():
            continue
        for ti in range(g.bpa.states[s].length()):
            for bi in range(g.bpa.states[s].length()):
                if r >= len(root_ids) or g.packets[root_ids[r]].key != PacketKey(s, 1, ti, bi, -1):
                    raise Error(_msg("L6", "roots differ from all position pairs of the noncoincident states"))
                r += 1
    if r != len(root_ids):
        raise Error(_msg("L6", "extra root packets"))
    if len(sq.key_order) != n:
        raise Error(_msg("L6", "key order has the wrong length"))
    var seen = List[Bool](length=n, fill=False)
    var bound = _max_state_length(g) + 1
    for k in range(n):
        var id = sq.key_order[k]
        if id < 0 or id >= n or seen[id]:
            raise Error(_msg("L6", "key order is not a permutation"))
        seen[id] = True
        var kp = _key_parts(g, id)
        if kp[2] >= bound or kp[3] >= bound or kp[4] < 0 or kp[4] >= len(g.factors) + 1:
            raise Error(_msg("L6", "key component outside the key-code bounds"))
        if k > 0:
            var prev = _key_parts(g, sq.key_order[k - 1])
            var less = False
            var decided = False
            for c in range(5):
                if not decided and prev[c] != kp[c]:
                    less = prev[c] < kp[c]
                    decided = True
            if not less:
                raise Error(_msg("L6", "keys do not strictly increase along the key order"))
    var first_in = List[Int](length=n, fill=-1)
    for eid in range(len(g.edges)):
        if first_in[g.edges[eid].destination] == -1:
            first_in[g.edges[eid].destination] = eid
    if len(sq.births) != n:
        raise Error(_msg("L6", "one birth per packet is required"))
    for i in range(n):
        ref b = sq.births[i]
        if g.packets[i].key.factor_edge == -1:
            if len(b) != 0:
                raise Error(_msg("L6", "a root has a birth"))
            continue
        if len(b) != 3:
            raise Error(_msg("L6", "a non-root packet has no birth"))
        if b[0] < 0 or b[0] >= i:
            raise Error(_msg("L6", "a birth does not name an earlier packet"))
        var found = False
        for k in range(len(sq.stars[b[0]])):
            var e = sq.stars[b[0]][k]
            if e.destination == i and e.top_digit == b[1] and e.bottom_digit == b[2]:
                found = True
        if not found:
            raise Error(_msg("L6", "the birth source's star has no such child entry"))
        if first_in[i] < 0:
            raise Error(_msg("L6", "a non-root packet has no incoming edge"))
        ref e = g.edges[first_in[i]]
        if e.source != b[0] or e.top_digit != b[1] or e.bottom_digit != b[2]:
            raise Error(_msg("L6", "a birth is not the first incoming edge"))

    # L7: hub rows from literal first letters; undefined bits stay -1.
    var h = 0
    for s in range(g.bpa.size()):
        if g.bpa.states[s].is_coincidence():
            continue
        for hub in range(3):
            if h >= len(sq.hubs):
                raise Error(_msg("L7", "missing hub row"))
            ref row = sq.hubs[h]
            h += 1
            if row.state != s or row.hub != hub or row.factors != factor_ids[s] or len(row.bits) != len(factor_ids[s]):
                raise Error(_msg("L7", "hub row is not the state's ordered factor list"))
            var parent_side = _literal_hub_side(g.bpa.states[s], hub)
            for j in range(len(factor_ids[s])):
                ref f = g.factors[factor_ids[s][j]]
                var child_side = _literal_hub_side(g.bpa.states[f.child], hub)
                var expected = -1
                if parent_side >= 0 and child_side >= 0:
                    expected = parent_side ^ child_side ^ Int(f.sign == -1)
                if row.bits[j] != expected:
                    raise Error(_msg("L7", "hub bit differs from the literal first letters (undefined must stay -1)"))
    if h != len(sq.hubs):
        raise Error(_msg("L7", "extra hub rows"))
    return True


# ---------------------------------------------------------------------------
# Counts.
# ---------------------------------------------------------------------------


def root_count(sq: PacketSquare) -> Int:
    var out = 0
    for i in range(len(sq.graph.packets)):
        if sq.graph.packets[i].key.factor_edge == -1:
            out += 1
    return out


def success_count(sq: PacketSquare) -> Int:
    var out = 0
    for i in range(len(sq.graph.packets)):
        if sq.graph.packets[i].success:
            out += 1
    return out


def split_entry_count(sq: PacketSquare) -> Int:
    var out = 0
    for i in range(len(sq.stars)):
        for k in range(len(sq.stars[i])):
            if sq.stars[i][k].is_split():
                out += 1
    return out


# ---------------------------------------------------------------------------
# JSONL emission (schema packet-square-v1).
# ---------------------------------------------------------------------------


def _bool_text(b: Bool) -> String:
    return "true" if b else "false"


def _sigma_json(sigma: List[List[Int]]) -> String:
    var out = String("[")
    for i in range(len(sigma)):
        if i > 0:
            out += ","
        out += ints_json(sigma[i])
    return out + "]"


def sigma_text(sigma: List[List[Int]]) -> String:
    """`1/02/202` form of a substitution."""
    var out = String("")
    for i in range(len(sigma)):
        if i > 0:
            out += "/"
        for j in range(len(sigma[i])):
            out += String(sigma[i][j])
    return out


def budget_json(state_cap: Int, length_cap: Int, packet_cap: Int, edge_cap: Int) -> String:
    return (String('{"record":"budget","bpa_states":') + String(state_cap) + ',"bpa_length":' + String(length_cap)
            + ',"packets":' + String(packet_cap) + ',"edges":' + String(edge_cap) + '}')


def _address_json(a: OccurrenceAddress, root: Bool) -> String:
    if root:
        return "null"
    return ints_json([a.source_occurrence, a.within_image, a.global_position, a.local_position])


def _bits_json(bits: List[Int]) raises -> String:
    var out = String("[")
    for j in range(len(bits)):
        if j > 0:
            out += ","
        if bits[j] == -1:
            out += "null"
        elif bits[j] == 0 or bits[j] == 1:
            out += String(bits[j])
        else:
            raise Error(_msg("L7", "hub bit outside {-1, 0, 1}"))
    return out + "]"


def packet_square_jsonl(sq: PacketSquare, hub_rows: Bool) raises -> List[String]:
    """Every packet-square-v1 row after the budget row, in schema order.

    Refuses (raises) unless `verify_packet_square` accepts the square, so no
    row is returned for an unverified table.
    """
    _ = verify_packet_square(sq)
    ref g = sq.graph
    var out = List[String]()
    var target = String("null") if g.target == -1 else String(g.target)
    var nhubs = len(sq.hubs) if hub_rows else 0
    out.append(String('{"record":"header","schema":"') + PACKET_SQUARE_SCHEMA + '","status":"finite-certificate-input","sigma":'
               + _sigma_json(g.tables.sigma) + ',"letters":[0,1,2],"target":' + target
               + ',"synchronize_right":false,"pip":' + _bool_text(sq.pip)
               + ',"states":' + String(g.bpa.size()) + ',"factors":' + String(len(g.factors))
               + ',"packets":' + String(len(g.packets)) + ',"edges":' + String(len(g.edges))
               + ',"split_descendants":' + String(g.split_count) + ',"roots":' + String(root_count(sq))
               + ',"hub_rows":' + String(nhubs) + '}')
    for s in range(g.bpa.size()):
        ref p = g.bpa.states[s]
        out.append(String('{"record":"state","id":') + String(s) + ',"top":' + ints_json(p.u)
                   + ',"bottom":' + ints_json(p.v) + ',"coincidence":' + _bool_text(p.is_coincidence()) + '}')
    for f in range(len(g.factors)):
        ref e = g.factors[f]
        out.append(String('{"record":"factor","id":') + String(f) + ',"parent":' + String(e.parent)
                   + ',"ordinal":' + String(e.ordinal) + ',"child":' + String(e.child)
                   + ',"orientation":' + String(e.sign) + ',"span":' + ints_json([e.start, e.end, e.total]) + '}')
    for i in range(len(g.packets)):
        ref p = g.packets[i]
        var root = p.key.factor_edge == -1
        var birth = String("null") if root else ints_json(sq.births[i])
        out.append(String('{"record":"packet","id":') + String(i) + ',"state":' + String(p.key.state_id)
                   + ',"orientation":' + String(p.key.sign) + ',"occurrences":' + ints_json([p.key.top, p.key.bottom])
                   + ',"factor_edge":' + String(p.key.factor_edge)
                   + ',"top_address":' + _address_json(p.top_address, root)
                   + ',"bottom_address":' + _address_json(p.bottom_address, root)
                   + ',"target_letters":' + ints_json([p.top_letter, p.bottom_letter])
                   + ',"residual":' + ints_json([p.residual.x, p.residual.y, p.residual.z])
                   + ',"interior":' + _bool_text(p.interior) + ',"success":' + _bool_text(p.success)
                   + ',"birth":' + birth + '}')
    for i in range(len(g.packets)):
        ref p = g.packets[i]
        var expanded = not (p.success or g.bpa.states[p.key.state_id].is_coincidence())
        var entries = String("[")
        for k in range(len(sq.stars[i])):
            var e = sq.stars[i][k]
            if k > 0:
                entries += ","
            if e.is_split():
                entries += String('["split",') + String(e.top_digit) + "," + String(e.bottom_digit) + "," + String(e.top_ordinal) + "," + String(e.bottom_ordinal) + "]"
            else:
                entries += String('["child",') + String(e.top_digit) + "," + String(e.bottom_digit) + "," + String(e.destination) + "]"
        entries += "]"
        out.append(String('{"record":"star","packet":') + String(i) + ',"expanded":' + _bool_text(expanded)
                   + ',"entries":' + entries + '}')
    out.append(String('{"record":"key_order","packets":') + ints_json(sq.key_order) + '}')
    if hub_rows:
        for k in range(len(sq.hubs)):
            ref row = sq.hubs[k]
            out.append(String('{"record":"hub","state":') + String(row.state) + ',"hub":' + String(row.hub)
                       + ',"factors":' + ints_json(row.factors) + ',"bits":' + _bits_json(row.bits) + '}')
    out.append(String('{"record":"summary","packets":') + String(len(g.packets)) + ',"edges":' + String(len(g.edges))
               + ',"split_descendants":' + String(g.split_count)
               + ',"part_b":"open","C4":"unchanged","G1":"unchanged","PSC":"unchanged"}')
    return out^


def emit_packet_square_jsonl(sq: PacketSquare, hub_rows: Bool) raises:
    """Print the rows of `packet_square_jsonl`, only after all of them exist."""
    var lines = packet_square_jsonl(sq, hub_rows)
    for i in range(len(lines)):
        print(lines[i])


# ---------------------------------------------------------------------------
# Lean emission: a data module of `Psc.PacketCertificate.Table (Fin 3)`.
# ---------------------------------------------------------------------------


def _is_ident_start(c: String) -> Bool:
    return (c >= "A" and c <= "Z") or (c >= "a" and c <= "z") or c == "_"


def _is_ident_char(c: String) -> Bool:
    return _is_ident_start(c) or (c >= "0" and c <= "9")


def check_lean_module_name(module: String) raises:
    """Dot-separated ASCII identifiers, each starting with a letter or `_`."""
    if module.byte_length() == 0 or module.byte_length() > 200:
        raise Error("Lean module name must be 1..200 characters")
    for part in module.split("."):
        var piece = String(part)
        if piece.byte_length() == 0:
            raise Error("Lean module name has an empty component")
        var first = True
        for ch in piece.codepoint_slices():
            var c = String(ch)
            if first and not _is_ident_start(c):
                raise Error("Lean module component must start with a letter or _")
            if not _is_ident_char(c):
                raise Error("Lean module name must be ASCII identifiers separated by dots")
            first = False


def _lean_list(xs: List[Int]) -> String:
    var out = String("[")
    for i in range(len(xs)):
        if i > 0:
            out += ", "
        out += String(xs[i])
    return out + "]"


def _lean_tuple(xs: List[Int]) -> String:
    var out = String("(")
    for i in range(len(xs)):
        if i > 0:
            out += ", "
        out += String(xs[i])
    return out + ")"


def _lean_bit(b: Int) raises -> String:
    if b == -1:
        return "none"
    if b == 0:
        return "some false"
    if b == 1:
        return "some true"
    raise Error(_msg("L7", "hub bit outside {-1, 0, 1}"))


def _lean_block(name: String, items: List[String]) -> List[String]:
    """`  name := [` then one item per line, closed on the last item."""
    var out = List[String]()
    if len(items) == 0:
        out.append(String("  ") + name + " := []")
        return out^
    out.append(String("  ") + name + " := [")
    for i in range(len(items)):
        var tail = String(",") if i + 1 < len(items) else String("]")
        out.append(String("    ") + items[i] + tail)
    return out^


def packet_square_lean(sq: PacketSquare, module: String, hub_rows: Bool, command: String) raises -> List[String]:
    """The data module, line by line: one `table` and one `decide +kernel` theorem.

    `command` is recorded in the leading comment as the regeneration command.
    Refuses (raises) unless `verify_packet_square` accepts the square.
    """
    check_lean_module_name(module)
    _ = verify_packet_square(sq)
    ref g = sq.graph
    var target = String("any") if g.target == -1 else String(g.target)
    var nhubs = len(sq.hubs) if hub_rows else 0
    var out = List[String]()
    out.append("/-")
    out.append("Generated by kernel/psc/packet_square_export.mojo (schema packet-square-v1). Do not edit:")
    out.append("kernel/check_packet_square.sh regenerates this file and compares the bytes.")
    out.append(String("Command: ") + command)
    out.append(String("Rows: ") + String(g.bpa.size()) + " states, " + String(len(g.factors)) + " factors, "
               + String(len(g.packets)) + " packets, " + String(len(g.edges)) + " edges, "
               + String(g.split_count) + " split descendants, " + String(root_count(sq)) + " roots, "
               + String(nhubs) + " hub rows.")
    out.append(String("PIP: ") + _bool_text(sq.pip) + " (recorded by the exporter; the checker does not read it).")
    out.append("-/")
    out.append("import PscVerif.PacketCertificate")
    out.append("")
    out.append("/-!")
    out.append(String("# packet-square-v1 data: `") + sigma_text(g.tables.sigma) + "`, target " + target)
    out.append("")
    out.append("The rows of the target-aware packet graph exported by `kernel/psc/packet_square_export.mojo`,")
    out.append("as a `Psc.PacketCertificate.Table (Fin 3)`. `accepted` states only that `Table.check` accepts")
    out.append("this finite table, by one kernel evaluation. The checker re-derives every factor row, every")
    out.append("packet row except its `birth` field, every digit star and every listed hub row from")
    out.append("`Psc.Reduction.red`; it checks that each `birth` names an incoming edge from an earlier row")
    out.append("(not necessarily the first), and it checks the letters, the states, the seeds, the roots and")
    out.append("the key order. Nothing here concerns states outside the table, absolute occurrences in the")
    out.append("iterates, the PIP status, or C4, G1 and PSC.")
    out.append("-/")
    out.append("")
    out.append(String("namespace ") + module)
    out.append("")
    out.append("open Psc.PacketCertificate")
    out.append("")
    out.append(String("/-- The exported packet-square-v1 rows of `") + sigma_text(g.tables.sigma) + "`, target " + target + ". -/")
    out.append("def table : Table (Fin 3) where")
    out.append("  letters := [0, 1, 2]")
    out.append(String("  s := ![") + _lean_list(g.tables.sigma[0]) + ", " + _lean_list(g.tables.sigma[1]) + ", " + _lean_list(g.tables.sigma[2]) + "]")
    out.append(String("  target := ") + (String("none") if g.target == -1 else String("some ") + String(g.target)))
    var states = List[String]()
    for s in range(g.bpa.size()):
        states.append(String("(") + _lean_list(g.bpa.states[s].u) + ", " + _lean_list(g.bpa.states[s].v) + ")")
    out.extend(_lean_block("states", states))
    out.append("  -- factor rows: parent, ordinal, child, sign, start, stop, total")
    var factors = List[String]()
    for f in range(len(g.factors)):
        ref e = g.factors[f]
        factors.append(String("⟨") + String(e.parent) + ", " + String(e.ordinal) + ", " + String(e.child) + ", "
                       + _bool_text(e.sign == 1) + ", " + String(e.start) + ", " + String(e.end) + ", " + String(e.total) + "⟩")
    out.extend(_lean_block("factors", factors))
    out.append("  -- packet rows: state, sign, top, bot, factor, topAddr, botAddr, letters, residual, interior,")
    out.append("  -- success, birth")
    var packets = List[String]()
    for i in range(len(g.packets)):
        ref p = g.packets[i]
        var root = p.key.factor_edge == -1
        var factor = String("none") if root else String("some ") + String(p.key.factor_edge)
        var ta = String("none") if root else String("some ") + _lean_tuple([p.top_address.source_occurrence, p.top_address.within_image, p.top_address.global_position, p.top_address.local_position])
        var ba = String("none") if root else String("some ") + _lean_tuple([p.bottom_address.source_occurrence, p.bottom_address.within_image, p.bottom_address.global_position, p.bottom_address.local_position])
        var birth = String("none") if root else String("some ") + _lean_tuple(sq.births[i])
        packets.append(String("⟨") + String(p.key.state_id) + ", " + _bool_text(p.key.sign == 1) + ", "
                       + String(p.key.top) + ", " + String(p.key.bottom) + ", " + factor + ", " + ta + ", " + ba + ", "
                       + _lean_tuple([p.top_letter, p.bottom_letter]) + ", " + _lean_list([p.residual.x, p.residual.y, p.residual.z]) + ", "
                       + _bool_text(p.interior) + ", " + _bool_text(p.success) + ", " + birth + "⟩")
    out.extend(_lean_block("packets", packets))
    var stars = List[String]()
    for i in range(len(sq.stars)):
        var row = String("[")
        for k in range(len(sq.stars[i])):
            var e = sq.stars[i][k]
            if k > 0:
                row += ", "
            if e.is_split():
                row += String(".split ") + String(e.top_digit) + " " + String(e.bottom_digit) + " " + String(e.top_ordinal) + " " + String(e.bottom_ordinal)
            else:
                row += String(".child ") + String(e.top_digit) + " " + String(e.bottom_digit) + " " + String(e.destination)
        stars.append(row + "]")
    out.extend(_lean_block("stars", stars))
    var keys = List[String]()
    var chunk = String("")
    for k in range(len(sq.key_order)):
        if k % 20 == 0 and k > 0:
            keys.append(chunk)
            chunk = String("")
        if k % 20 > 0:
            chunk += ", "
        chunk += String(sq.key_order[k])
    if len(sq.key_order) > 0:
        keys.append(chunk)
    out.extend(_lean_block("keyOrder", keys))
    var hubs = List[String]()
    if hub_rows:
        for k in range(len(sq.hubs)):
            ref row = sq.hubs[k]
            var bits = String("[")
            for j in range(len(row.bits)):
                if j > 0:
                    bits += ", "
                bits += _lean_bit(row.bits[j])
            hubs.append(String("⟨") + String(row.state) + ", " + String(row.hub) + ", " + bits + "]⟩")
    out.extend(_lean_block("hubs", hubs))
    out.append("")
    out.append("/-- The v1 checker accepts the exported table (one kernel evaluation). -/")
    out.append("theorem accepted : table.check = true := by decide +kernel")
    out.append("")
    out.append(String("end ") + module)
    return out^


def emit_packet_square_lean(sq: PacketSquare, module: String, hub_rows: Bool, command: String) raises:
    """Print the lines of `packet_square_lean`, only after all of them exist."""
    var lines = packet_square_lean(sq, module, hub_rows, command)
    for i in range(len(lines)):
        print(lines[i])
