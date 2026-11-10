"""Regression and mutation controls for the packet-square-v1 export.

Positive fixtures: Tribonacci `01/02/0`, real-secondary PIP `1/02/202`,
non-Pisot strict `1/012/1` and the actual closure of strong G/F `1/2/021`.
For the last three, the packet, edge and split counts equal the headers
archived in evidence/target-aware-bpa-2026-10-02 (Tribonacci has no archived
dump); the rows themselves are not compared with that archive here (that is
the Python oracle's job). Each mutation control must be refused by
`verify_packet_square` at the named layer (L0 configuration, L1 PIP record,
L2 states, L3 literal factorisation, L4 packet rows, L5 full digit stars, L6
roots/keys/births, L7 hub bits) and by the named check of that layer. Caps
refuse and synchronize mode refuses.

The Lean emitter is pinned row by row: the whole data module is rendered here
from the committed JSONL text of evidence/packet-square-2026-11-10 alone
(`lean_from_jsonl`, written without the exporter's helpers), and
`packet_square_lean` must print it line for line; the exporter must still
print exactly the committed JSONL rows. The file paths are relative to
`kernel/`, where `run_tests.sh` and `check_packet_square.sh` run. The
committed Lean data modules themselves are compared byte for byte by
`check_packet_square.sh`, not here.

Nothing here is a statement about the Lean checker, which decides acceptance
of the emitted table on its own, nor about C4, G1 or PSC.
"""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from psc.bounded_bpa import build_bounded
from psc.bpa import sigma3
from psc.words import Pair
from psc.target_packets import build_packets, make_root
from psc.packet_square_export import (
    StarEntry, PacketSquare, HubRow, build_packet_square, verify_packet_square,
    packet_stars, packet_square_jsonl, packet_square_lean, parse_packet_square_target,
    check_lean_module_name, root_count, success_count, split_entry_count, budget_json,
    SYNC_RIGHT_REFUSAL,
)


comptime EVIDENCE = "../evidence/packet-square-2026-11-10/"


def fixture(sigma: List[List[Int]], target: Int = -1) raises -> PacketSquare:
    var a = build_bounded(sigma3(sigma), 20000, 10000)
    assert_true(a.complete())
    return build_packet_square(sigma, a.graph, 200000, 2000000, target)


def refusal(sq: PacketSquare) -> String:
    try:
        _ = verify_packet_square(sq)
    except e:
        return String(e)
    return String("")


def assert_refused(sq: PacketSquare, layer: String, check: String) raises:
    """Refused, at `layer`, by the check whose message contains `check`."""
    var message = refusal(sq)
    assert_true(message.byte_length() > 0, "mutated square was accepted")
    assert_true((String("packet-square ") + layer + ": ") in message, message)
    assert_true(check in message, message)


def has_child(star: List[StarEntry], d: Int, e: Int, dst: Int) -> Bool:
    for k in range(len(star)):
        if star[k] == StarEntry(d, e, dst, -1, -1):
            return True
    return False


def lean_key_code(sq: PacketSquare, id: Int) -> Int:
    """The Lean `Table.keyCode`, computed here independently of the exporter."""
    ref g = sq.graph
    var longest = 0
    for s in range(g.bpa.size()):
        longest = max(longest, g.bpa.states[s].length())
    var b = longest + 1
    var f = len(g.factors) + 1
    ref k = g.packets[id].key
    var sign = 1 if k.sign == 1 else 0
    return (((k.state_id * 2 + sign) * b + k.top) * b + k.bottom) * f + (k.factor_edge + 1)


def swap_id(x: Int, i: Int, j: Int) -> Int:
    if x == i:
        return j
    if x == j:
        return i
    return x


def exchange_packets(sq: PacketSquare, i: Int, j: Int) -> PacketSquare:
    """The same table with packet ids `i` and `j` exchanged everywhere.

    Rows, stars, adjacency, edge ends, child destinations, births and the key
    order are all relabelled, so every row and star stays literal; only the
    order of the packet ids changes.
    """
    var out = sq.copy()
    out.graph.packets[i] = sq.graph.packets[j].copy()
    out.graph.packets[j] = sq.graph.packets[i].copy()
    out.graph.adj[i] = sq.graph.adj[j].copy()
    out.graph.adj[j] = sq.graph.adj[i].copy()
    out.graph.birth[i] = sq.graph.birth[j]
    out.graph.birth[j] = sq.graph.birth[i]
    out.stars[i] = sq.stars[j].copy()
    out.stars[j] = sq.stars[i].copy()
    out.births[i] = sq.births[j].copy()
    out.births[j] = sq.births[i].copy()
    for e in range(len(out.graph.edges)):
        out.graph.edges[e].source = swap_id(out.graph.edges[e].source, i, j)
        out.graph.edges[e].destination = swap_id(out.graph.edges[e].destination, i, j)
    for p in range(len(out.stars)):
        for k in range(len(out.stars[p])):
            if not out.stars[p][k].is_split():
                out.stars[p][k].destination = swap_id(out.stars[p][k].destination, i, j)
    for p in range(len(out.births)):
        if len(out.births[p]) == 3:
            out.births[p][0] = swap_id(out.births[p][0], i, j)
    for k in range(len(out.key_order)):
        out.key_order[k] = swap_id(out.key_order[k], i, j)
    return out^


# ---------------------------------------------------------------------------
# The Lean data module rendered from JSONL text alone.
# ---------------------------------------------------------------------------


def read_text(path: String) raises -> String:
    with open(path, "r") as f:
        return f.read()


def jsonl_rows(text: String) raises -> List[String]:
    """The rows of a JSONL text that ends in a newline; an empty row refuses."""
    assert_true(text.endswith("\n"), "JSONL text must end in a newline")
    var out = List[String]()
    var parts = text.split("\n")
    for k in range(len(parts) - 1):
        var row = String(parts[k])
        assert_true(row.byte_length() > 0, "empty JSONL row")
        out.append(row^)
    return out^


def jfield(row: String, name: String) raises -> String:
    """The raw text of the value of `"name":` in one packet-square-v1 row."""
    var key = String('"') + name + '":'
    var at = row.find(key)
    assert_true(at >= 0, String("row has no field ") + name + ": " + row)
    var start = at + key.byte_length()
    var bytes = row.as_bytes()
    var depth = 0
    var stop = start
    while stop < len(bytes):
        var c = Int(bytes[stop])
        if c == 91:
            depth += 1
        elif c == 93:
            depth -= 1
        elif depth == 0 and (c == 44 or c == 125):
            break
        stop += 1
    assert_equal(depth, 0, String("unbalanced value of ") + name)
    return String(row[byte=start:stop])


def jtokens(text: String) raises -> List[String]:
    """`[a,b,c]` as its tokens; `[]` has none; a nested list refuses."""
    assert_true(text.startswith("[") and text.endswith("]"), String("not a list: ") + text)
    var out = List[String]()
    var inner = String(text[byte=1:text.byte_length() - 1])
    if inner.byte_length() == 0:
        return out^
    for part in inner.split(","):
        var t = String(part)
        assert_false("[" in t or "]" in t or t.byte_length() == 0, String("not a flat list: ") + text)
        out.append(t^)
    return out^


def jnested(text: String) raises -> List[List[String]]:
    """`[[a,b],[c]]` as the token lists of its (flat) inner lists; `[]` has none."""
    var out = List[List[String]]()
    if text == "[]":
        return out^
    assert_true(text.startswith("[[") and text.endswith("]]"), String("not a list of lists: ") + text)
    var inner = String(text[byte=2:text.byte_length() - 2])
    for part in inner.split("],["):
        out.append(jtokens(String("[") + String(part) + "]"))
    return out^


def ljoin(xs: List[String], sep: String) -> String:
    var out = String("")
    for k in range(len(xs)):
        if k > 0:
            out += sep
        out += xs[k]
    return out


def llist(xs: List[String]) -> String:
    return String("[") + ljoin(xs, ", ") + "]"


def ltuple(xs: List[String]) -> String:
    return String("(") + ljoin(xs, ", ") + ")"


def lsome_tuple(text: String) raises -> String:
    """JSON `null` is Lean `none`; a flat list is `some (..)`."""
    if text == "null":
        return String("none")
    return String("some ") + ltuple(jtokens(text))


def lbool(text: String) raises -> String:
    assert_true(text == "true" or text == "false", text)
    return text


def lsign(text: String) raises -> String:
    """JSON orientation `1` / `-1` is the Lean sign `true` / `false`."""
    assert_true(text == "1" or text == "-1", text)
    return String("true") if text == "1" else String("false")


def lblock(name: String, items: List[String]) -> List[String]:
    var out = List[String]()
    if len(items) == 0:
        out.append(String("  ") + name + " := []")
        return out^
    out.append(String("  ") + name + " := [")
    for k in range(len(items)):
        out.append(String("    ") + items[k] + ("," if k + 1 < len(items) else "]"))
    return out^


def lean_from_jsonl(rows: List[String], module: String, command: String) raises -> List[String]:
    """The data module `packet_square_lean` must print for these packet-square-v1 rows.

    Built from the JSONL text alone (no `PacketSquare`, no exporter helper):
    each Lean row is the JSONL row of the same id, field by field. The
    prose lines are copied from the emitter; every other line is data.
    """
    assert_true(rows[0].startswith('{"record":"budget",'), rows[0])
    ref header = rows[1]
    assert_true(header.startswith('{"record":"header","schema":"packet-square-v1",'), header)
    assert_true(rows[len(rows) - 1].startswith('{"record":"summary",'), rows[len(rows) - 1])
    var sigma = jnested(jfield(header, "sigma"))
    assert_equal(len(sigma), 3)
    var images = List[String]()
    var words = List[String]()
    for a in range(3):
        images.append(llist(sigma[a]))
        words.append(ljoin(sigma[a], ""))
    var sigma_text = ljoin(words, "/")
    var target = jfield(header, "target")
    var target_word = String("any") if target == "null" else target
    var target_lean = String("none") if target == "null" else String("some ") + target
    var states = List[String]()
    var factors = List[String]()
    var packets = List[String]()
    var stars = List[String]()
    var keys = List[String]()
    var hubs = List[String]()
    var key_rows = 0
    for k in range(2, len(rows) - 1):
        ref r = rows[k]
        if r.startswith('{"record":"state",'):
            assert_equal(Int(jfield(r, "id")), len(states))
            states.append(String("(") + llist(jtokens(jfield(r, "top"))) + ", " + llist(jtokens(jfield(r, "bottom"))) + ")")
        elif r.startswith('{"record":"factor",'):
            assert_equal(Int(jfield(r, "id")), len(factors))
            var span = jtokens(jfield(r, "span"))
            assert_equal(len(span), 3)
            factors.append(String("⟨") + jfield(r, "parent") + ", " + jfield(r, "ordinal") + ", " + jfield(r, "child") + ", "
                           + lsign(jfield(r, "orientation")) + ", " + span[0] + ", " + span[1] + ", " + span[2] + "⟩")
        elif r.startswith('{"record":"packet",'):
            assert_equal(Int(jfield(r, "id")), len(packets))
            var factor_edge = jfield(r, "factor_edge")
            var factor = String("none") if factor_edge == "-1" else String("some ") + factor_edge
            var occurrences = jtokens(jfield(r, "occurrences"))
            assert_equal(len(occurrences), 2)
            packets.append(String("⟨") + jfield(r, "state") + ", " + lsign(jfield(r, "orientation")) + ", "
                           + occurrences[0] + ", " + occurrences[1] + ", " + factor + ", "
                           + lsome_tuple(jfield(r, "top_address")) + ", " + lsome_tuple(jfield(r, "bottom_address")) + ", "
                           + ltuple(jtokens(jfield(r, "target_letters"))) + ", " + llist(jtokens(jfield(r, "residual"))) + ", "
                           + lbool(jfield(r, "interior")) + ", " + lbool(jfield(r, "success")) + ", "
                           + lsome_tuple(jfield(r, "birth")) + "⟩")
        elif r.startswith('{"record":"star",'):
            assert_equal(Int(jfield(r, "packet")), len(stars))
            var entries = jnested(jfield(r, "entries"))
            var items = List[String]()
            for e in range(len(entries)):
                ref t = entries[e]
                if t[0] == '"child"':
                    assert_equal(len(t), 4)
                    items.append(String(".child ") + t[1] + " " + t[2] + " " + t[3])
                else:
                    assert_equal(t[0], String('"split"'))
                    assert_equal(len(t), 5)
                    items.append(String(".split ") + t[1] + " " + t[2] + " " + t[3] + " " + t[4])
            stars.append(llist(items))
        elif r.startswith('{"record":"key_order",'):
            key_rows += 1
            var ids = jtokens(jfield(r, "packets"))
            var chunk = List[String]()
            for i in range(len(ids)):
                chunk.append(ids[i])
                if len(chunk) == 20 or i + 1 == len(ids):
                    keys.append(ljoin(chunk, ", "))
                    chunk = List[String]()
        elif r.startswith('{"record":"hub",'):
            var bits = jtokens(jfield(r, "bits"))
            var lean_bits = List[String]()
            for j in range(len(bits)):
                if bits[j] == "null":
                    lean_bits.append("none")
                elif bits[j] == "1":
                    lean_bits.append("some true")
                else:
                    assert_equal(bits[j], String("0"))
                    lean_bits.append("some false")
            hubs.append(String("⟨") + jfield(r, "state") + ", " + jfield(r, "hub") + ", " + llist(lean_bits) + "⟩")
        else:
            raise Error(String("unexpected packet-square-v1 row: ") + r)
    assert_equal(key_rows, 1)
    assert_equal(len(states), Int(jfield(header, "states")))
    assert_equal(len(factors), Int(jfield(header, "factors")))
    assert_equal(len(packets), Int(jfield(header, "packets")))
    assert_equal(len(stars), len(packets))
    assert_equal(len(hubs), Int(jfield(header, "hub_rows")))

    var out = List[String]()
    out.append("/-")
    out.append("Generated by kernel/psc/packet_square_export.mojo (schema packet-square-v1). Do not edit:")
    out.append("kernel/check_packet_square.sh regenerates this file and compares the bytes.")
    out.append(String("Command: ") + command)
    out.append(String("Rows: ") + jfield(header, "states") + " states, " + jfield(header, "factors") + " factors, "
               + jfield(header, "packets") + " packets, " + jfield(header, "edges") + " edges, "
               + jfield(header, "split_descendants") + " split descendants, " + jfield(header, "roots") + " roots, "
               + jfield(header, "hub_rows") + " hub rows.")
    out.append(String("PIP: ") + lbool(jfield(header, "pip")) + " (recorded by the exporter; the checker does not read it).")
    out.append("-/")
    out.append("import PscVerif.PacketCertificate")
    out.append("")
    out.append("/-!")
    out.append(String("# packet-square-v1 data: `") + sigma_text + "`, target " + target_word)
    out.append("")
    out.append("The rows of the target-aware packet graph exported by `kernel/psc/packet_square_export.mojo`,")
    out.append("as a `Psc.PacketCertificate.Table (Fin 3)`. `accepted` states only that `Table.check` accepts")
    out.append("this finite table, by one kernel evaluation: the checker re-derives every factor row, packet")
    out.append("row and digit star from `Psc.Reduction.red`. Nothing here concerns states outside the table,")
    out.append("absolute occurrences in the iterates, the PIP status, or C4, G1 and PSC.")
    out.append("-/")
    out.append("")
    out.append(String("namespace ") + module)
    out.append("")
    out.append("open Psc.PacketCertificate")
    out.append("")
    out.append(String("/-- The exported packet-square-v1 rows of `") + sigma_text + "`, target " + target_word + ". -/")
    out.append("def table : Table (Fin 3) where")
    out.append(String("  letters := ") + llist(jtokens(jfield(header, "letters"))))
    out.append(String("  s := ![") + ljoin(images, ", ") + "]")
    out.append(String("  target := ") + target_lean)
    out.extend(lblock("states", states))
    out.append("  -- factor rows: parent, ordinal, child, sign, start, stop, total")
    out.extend(lblock("factors", factors))
    out.append("  -- packet rows: state, sign, top, bot, factor, topAddr, botAddr, letters, residual, interior,")
    out.append("  -- success, birth")
    out.extend(lblock("packets", packets))
    out.extend(lblock("stars", stars))
    out.extend(lblock("keyOrder", keys))
    out.extend(lblock("hubs", hubs))
    out.append("")
    out.append("/-- The v1 checker accepts the exported table (one kernel evaluation). -/")
    out.append("theorem accepted : table.check = true := by decide +kernel")
    out.append("")
    out.append(String("end ") + module)
    return out^


def assert_lines_equal(got: List[String], want: List[String], what: String) raises:
    """Line-for-line equality, naming the first differing line."""
    for k in range(min(len(got), len(want))):
        if got[k] != want[k]:
            raise Error(what + ", line " + String(k + 1) + ":\n  got  " + got[k] + "\n  want " + want[k])
    assert_equal(len(got), len(want), what + ": line count")


def with_budget(rows: List[String]) -> List[String]:
    var out: List[String] = [budget_json(20000, 10000, 200000, 2000000)]
    for k in range(len(rows)):
        out.append(rows[k])
    return out^


def fixture_sigmas() -> List[List[List[Int]]]:
    var sigmas = List[List[List[Int]]]()
    sigmas.append([[0, 1], [0, 2], [0]])
    sigmas.append([[1], [0, 2], [2, 0, 2]])
    sigmas.append([[1], [0, 1, 2], [1]])
    sigmas.append([[1], [2], [0, 2, 1]])
    return sigmas^


# ---------------------------------------------------------------------------
# Tests.
# ---------------------------------------------------------------------------


def test_fixture_counts() raises:
    var sigmas = fixture_sigmas()
    # packets, edges, split descendants, roots, successes, noncoincident states
    var expected: List[List[Int]] = [
        [132, 185, 194, 37, 0, 5],
        [507, 948, 1274, 118, 23, 8],
        [46, 82, 82, 12, 1, 3],
        [153, 235, 220, 39, 6, 6],
    ]
    var pip: List[Bool] = [True, True, False, True]
    for c in range(len(sigmas)):
        var sq = fixture(sigmas[c])
        ref g = sq.graph
        assert_equal(len(g.packets), expected[c][0])
        assert_equal(len(g.edges), expected[c][1])
        assert_equal(g.split_count, expected[c][2])
        assert_equal(root_count(sq), expected[c][3])
        assert_equal(success_count(sq), expected[c][4])
        assert_equal(len(sq.hubs), 3 * expected[c][5])
        assert_equal(sq.pip, pip[c])
        assert_true(verify_packet_square(sq))
        # Every split is recorded: the star totals equal the build's counter.
        assert_equal(split_entry_count(sq), g.split_count)
        var children = 0
        for i in range(len(sq.stars)):
            children += len(sq.stars[i])
            for k in range(len(sq.stars[i])):
                if sq.stars[i][k].is_split():
                    children -= 1
        assert_equal(children, len(g.edges))
        # Births precede; roots have none.
        for i in range(len(g.packets)):
            if g.packets[i].key.factor_edge == -1:
                assert_equal(len(sq.births[i]), 0)
            else:
                assert_equal(len(sq.births[i]), 3)
                assert_true(sq.births[i][0] < i)
                assert_true(has_child(sq.stars[sq.births[i][0]], sq.births[i][1], sq.births[i][2], i))
        # The Lean key codes strictly increase along the supplied order.
        for k in range(1, len(sq.key_order)):
            assert_true(lean_key_code(sq, sq.key_order[k - 1]) < lean_key_code(sq, sq.key_order[k]))
        # Coincidence and success packets carry empty stars.
        for i in range(len(g.packets)):
            if g.bpa.states[g.packets[i].key.state_id].is_coincidence() or g.packets[i].success:
                assert_equal(len(sq.stars[i]), 0)
            else:
                assert_true(len(sq.stars[i]) > 0)
        # Determinism: a second build emits the same rows.
        var again = fixture(sigmas[c])
        assert_true(packet_square_jsonl(sq, True) == packet_square_jsonl(again, True))


def test_real_secondary_rows_and_seed_depth_two() raises:
    var sq = fixture([[1], [0, 2], [2, 0, 2]])
    ref g = sq.graph
    # The cycle 209 -(0,0)-> 429 -(0,2)-> 209 with both stars literal.
    var star209: List[StarEntry] = [StarEntry(0, 0, 429, -1, -1), StarEntry(0, 1, 430, -1, -1), StarEntry(0, 2, -1, 2, 3)]
    assert_true(sq.stars[209] == star209)
    assert_true(has_child(sq.stars[429], 0, 2, 209))
    assert_equal(len(sq.stars[429]), 6)
    assert_equal(sq.births[209], [44, 0, 2])
    assert_equal(sq.births[429], [209, 0, 0])
    var lines = packet_square_jsonl(sq, True)
    var wanted: List[String] = [
        '{"record":"header","schema":"packet-square-v1","status":"finite-certificate-input","sigma":[[1],[0,2],[2,0,2]],"letters":[0,1,2],"target":null,"synchronize_right":false,"pip":true,"states":10,"factors":26,"packets":507,"edges":948,"split_descendants":1274,"roots":118,"hub_rows":24}',
        '{"record":"state","id":3,"top":[0,2,1],"bottom":[1,0,2],"coincidence":false}',
        '{"record":"factor","id":19,"parent":8,"ordinal":2,"child":7,"orientation":-1,"span":[7,10,13]}',
        '{"record":"packet","id":0,"state":0,"orientation":1,"occurrences":[0,0],"factor_edge":-1,"top_address":null,"bottom_address":null,"target_letters":[0,1],"residual":[0,0,0],"interior":false,"success":false,"birth":null}',
        '{"record":"packet","id":209,"state":8,"orientation":-1,"occurrences":[4,4],"factor_edge":16,"top_address":[2,0,4,4],"bottom_address":[1,2,4,4],"target_letters":[0,2],"residual":[-1,1,0],"interior":false,"success":false,"birth":[44,0,2]}',
        '{"record":"packet","id":429,"state":7,"orientation":1,"occurrences":[2,1],"factor_edge":19,"top_address":[4,0,9,2],"bottom_address":[4,0,8,1],"target_letters":[1,2],"residual":[1,-1,1],"interior":false,"success":false,"birth":[209,0,0]}',
        '{"record":"star","packet":209,"expanded":true,"entries":[["child",0,0,429],["child",0,1,430],["split",0,2,2,3]]}',
        '{"record":"star","packet":429,"expanded":true,"entries":[["child",0,0,207],["child",0,1,208],["child",0,2,209],["child",1,0,210],["child",1,1,211],["child",1,2,212]]}',
        '{"record":"hub","state":8,"hub":0,"factors":[17,18,19,20,21,22],"bits":[1,null,1,null,null,null]}',
        '{"record":"summary","packets":507,"edges":948,"split_descendants":1274,"part_b":"open","C4":"unchanged","G1":"unchanged","PSC":"unchanged"}',
    ]
    for w in range(len(wanted)):
        var found = False
        for i in range(len(lines)):
            if lines[i] == wanted[w]:
                found = True
        assert_true(found, wanted[w])
    assert_equal(lines[0], wanted[0])
    assert_equal(lines[len(lines) - 1], wanted[len(wanted) - 1])
    var head: List[Int] = [0, 1, 2, 3, 4, 143, 162, 5, 144, 163, 6, 145, 164, 7, 146, 165, 8, 9, 10, 11]
    for k in range(len(head)):
        assert_equal(sq.key_order[k], head[k])
    # Seed (01,10) = state 0, roots 0..3; no depth-one descendant is a success.
    for r in range(4):
        assert_equal(g.packets[r].key.state_id, 0)
    var depth_one = List[Int]()
    for r in range(4):
        for k in range(len(sq.stars[r])):
            if not sq.stars[r][k].is_split():
                depth_one.append(sq.stars[r][k].destination)
                assert_false(g.packets[sq.stars[r][k].destination].success)
    for k in range(len(depth_one)):
        assert_true(depth_one[k] >= 118 and depth_one[k] <= 126)
    # Success at depth two: 2 -(1,1)-> 124 -(0,2)-> 346.
    assert_true(has_child(sq.stars[2], 1, 1, 124))
    assert_true(has_child(sq.stars[124], 0, 2, 346))
    assert_true(g.packets[346].success)
    # Matching letters at depth one do not make a success: packet 154.
    assert_equal(g.packets[154].top_letter, 2)
    assert_equal(g.packets[154].bottom_letter, 2)
    assert_equal(g.packets[154].residual.x, -1)
    assert_equal(g.packets[154].residual.y, 1)
    assert_equal(g.packets[154].residual.z, 0)
    assert_false(g.packets[154].success)
    # ... and a row claiming that success is refused at the literal-row layer.
    var claimed = sq.copy()
    claimed.graph.packets[154].success = True
    assert_refused(claimed, "L4", "success flag differs from interior coincidence and target")


def test_mutations_refuse_at_their_layer() raises:
    var sq = fixture([[1], [0, 1, 2], [1]])
    assert_true(verify_packet_square(sq))
    var star0: List[StarEntry] = [StarEntry(0, 0, 12, -1, -1), StarEntry(0, 1, 13, -1, -1), StarEntry(0, 2, -1, 0, 1)]
    assert_true(sq.stars[0] == star0)
    # The states: 0 = (01,10), 1 = (02,20), 2 = (12,21), 3 = (1,1).
    assert_equal(sq.graph.bpa.size(), 4)
    assert_true(sq.graph.bpa.states[1] == Pair([0, 2], [2, 0]))
    assert_true(sq.graph.bpa.states[3] == Pair([1], [1]))

    # L5: a dropped split descendant, a dropped child edge, a retargeted child,
    # a wrong split account, an out-of-range destination, an extra entry.
    var bad = sq.copy()
    _ = bad.stars[0].pop(2)
    assert_refused(bad, "L5", "star is missing a digit pair")
    bad = sq.copy()
    _ = bad.stars[0].pop(0)
    assert_refused(bad, "L5", "star is not the row-major digit product")
    bad = sq.copy()
    bad.stars[0][0].destination = 13
    assert_refused(bad, "L5", "child entry is not the literal descendant")
    bad = sq.copy()
    bad.stars[0][2].top_ordinal = 1
    bad.stars[0][2].bottom_ordinal = 0
    assert_refused(bad, "L5", "split entry differs from the literal ordinals")
    bad = sq.copy()
    bad.stars[0][0].destination = len(sq.graph.packets)
    assert_refused(bad, "L5", "child entry is malformed or out of range")
    bad = sq.copy()
    bad.stars[0].append(StarEntry(0, 2, -1, 0, 1))
    assert_refused(bad, "L5", "star has entries beyond the digit product")
    bad = sq.copy()
    bad.graph.split_count += 1
    assert_refused(bad, "L5", "split entries differ from split_count")

    # L5: a truncated table (the last packet and everything naming it removed).
    bad = sq.copy()
    var last = len(bad.graph.packets) - 1
    _ = bad.graph.packets.pop(last)
    _ = bad.graph.adj.pop(last)
    _ = bad.graph.birth.pop(last)
    _ = bad.stars.pop(last)
    _ = bad.births.pop(last)
    var order = List[Int]()
    for k in range(len(sq.key_order)):
        if sq.key_order[k] != last:
            order.append(sq.key_order[k])
    bad.key_order = order^
    assert_refused(bad, "L5", "edge endpoint out of range")

    # L6: two key-order entries swapped; a duplicated key.
    bad = sq.copy()
    var t = bad.key_order[0]
    bad.key_order[0] = bad.key_order[1]
    bad.key_order[1] = t
    assert_refused(bad, "L6", "keys do not strictly increase along the key order")
    bad = sq.copy()
    var success = -1
    for i in range(len(sq.graph.packets)):
        if sq.graph.packets[i].success:
            success = i
    assert_equal(success, 21)
    bad.graph.packets.append(sq.graph.packets[success].copy())
    bad.graph.adj.append(List[Int]())
    bad.graph.birth.append(sq.graph.birth[success])
    bad.stars.append(List[StarEntry]())
    bad.births.append(sq.births[success].copy())
    var dup = List[Int]()
    for k in range(len(sq.key_order)):
        dup.append(sq.key_order[k])
        if sq.key_order[k] == success:
            dup.append(len(sq.graph.packets))
    bad.key_order = dup^
    assert_refused(bad, "L6", "keys do not strictly increase along the key order")

    # L6: a birth naming a later packet, a missing birth (root-unreachable
    # packet), a birth whose source star lacks the entry.
    bad = sq.copy()
    bad.births[12] = [20, 0, 0]
    assert_refused(bad, "L6", "a birth does not name an earlier packet")
    bad = sq.copy()
    bad.births[13] = List[Int]()
    assert_refused(bad, "L6", "a non-root packet has no birth")
    bad = sq.copy()
    bad.births[13] = [1, 0, 0]
    assert_refused(bad, "L6", "the birth source's star has no such child entry")

    # L6: a birth naming a later incoming edge. Its source is earlier and its
    # star holds the child entry, so the Lean `birthOK` accepts it; the Mojo
    # check is stricter and wants the first incoming edge, as `build_packets`
    # records it.
    var first_in = List[Int](length=len(sq.graph.packets), fill=-1)
    var later = -1
    var later_edge = -1
    for eid in range(len(sq.graph.edges)):
        ref e = sq.graph.edges[eid]
        if first_in[e.destination] == -1:
            first_in[e.destination] = eid
        elif later == -1 and e.source < e.destination:
            later = e.destination
            later_edge = eid
    assert_true(later >= 0)
    ref le = sq.graph.edges[later_edge]
    assert_true(has_child(sq.stars[le.source], le.top_digit, le.bottom_digit, later))
    assert_false(sq.births[later] == [le.source, le.top_digit, le.bottom_digit])
    bad = sq.copy()
    bad.births[later] = [le.source, le.top_digit, le.bottom_digit]
    assert_refused(bad, "L6", "a birth is not the first incoming edge")

    # L6: the roots. Packet ids 0 and 1 (both roots of state 0) exchanged
    # everywhere: every row and star stays literal and the keys still
    # increase, but the roots are no longer all position pairs in order.
    # Exchanging back restores an accepted table, so the relabelling itself
    # damages nothing else.
    assert_true(verify_packet_square(exchange_packets(exchange_packets(sq, 0, 1), 0, 1)))
    assert_refused(exchange_packets(sq, 0, 1), "L6", "roots differ from all position pairs of the noncoincident states")
    # An extra literal root at the coincidence state 3, with an empty star,
    # spliced into the key order at its key.
    bad = sq.copy()
    var extra = make_root(sq.graph, 3, 0, 0)
    bad.graph.packets.append(extra^)
    bad.graph.adj.append(List[Int]())
    bad.graph.birth.append(-1)
    bad.stars.append(List[StarEntry]())
    bad.births.append(List[Int]())
    var fresh = len(sq.graph.packets)
    var spliced = List[Int]()
    var placed = False
    for k in range(len(sq.key_order)):
        if not placed and lean_key_code(bad, sq.key_order[k]) > lean_key_code(bad, fresh):
            spliced.append(fresh)
            placed = True
        spliced.append(sq.key_order[k])
    if not placed:
        spliced.append(fresh)
    bad.key_order = spliced^
    assert_refused(bad, "L6", "extra root packets")

    # L7: an undefined hub bit coerced to 0, and a defined bit exported as undefined.
    assert_equal(sq.hubs[0].state, 0)
    assert_equal(sq.hubs[0].hub, 0)
    assert_equal(sq.hubs[0].bits, [1, -1])
    bad = sq.copy()
    bad.hubs[0].bits[1] = 0
    assert_refused(bad, "L7", "hub bit differs from the literal first letters")
    bad = sq.copy()
    bad.hubs[0].bits[0] = -1
    assert_refused(bad, "L7", "hub bit differs from the literal first letters")
    bad = sq.copy()
    _ = bad.hubs.pop(len(bad.hubs) - 1)
    assert_refused(bad, "L7", "missing hub row")

    # L4: the side-swapped row (packet 12 in the other orientation), a wrong
    # residual, a wrong interior flag, a wrong global position, wrong letters.
    assert_equal(sq.graph.packets[12].key.sign, -1)
    bad = sq.copy()
    bad.graph.packets[12].key.sign = 1
    assert_refused(bad, "L4", "selected letters differ from the block")
    bad = sq.copy()
    bad.graph.packets[13].residual.x += 1
    assert_refused(bad, "L4", "residual differs from the literal prefix defect")
    assert_true(sq.graph.packets[16].interior)
    bad = sq.copy()
    bad.graph.packets[16].interior = False
    assert_refused(bad, "L4", "interior flag differs from the birth ordinal")
    bad = sq.copy()
    bad.graph.packets[13].top_address.global_position = 99
    assert_refused(bad, "L4", "occurrence address differs from the literal cut address")
    bad = sq.copy()
    bad.graph.packets[13].top_letter = (bad.graph.packets[13].top_letter + 1) % 3
    assert_refused(bad, "L4", "selected letters differ from the block")

    # L3: a wrong ordinal, a wrong span, a template that merges two blocks.
    bad = sq.copy()
    bad.graph.factors[1].ordinal = 0
    assert_refused(bad, "L3", "factor row differs from the literal ordered factorisation")
    bad = sq.copy()
    bad.graph.factors[1].start = 1
    assert_refused(bad, "L3", "factor row differs from the literal ordered factorisation")
    bad = sq.copy()
    _ = bad.graph.factors.pop(3)
    assert_refused(bad, "L3", "factor rows differ from the literal block count")
    # L3: a listed coincidence state (0,0) that no seed reaches.
    bad = sq.copy()
    bad.graph.bpa.states.append(Pair([0], [0]))
    assert_refused(bad, "L3", "a listed state is not reached from the seeds")

    # L2: a state stored in the unnormalised orientation.
    bad = sq.copy()
    var u = bad.graph.bpa.states[0].u.copy()
    bad.graph.bpa.states[0].u = bad.graph.bpa.states[0].v.copy()
    bad.graph.bpa.states[0].v = u^
    assert_refused(bad, "L2", "state is not a normalised balanced pair")
    # L2: the swap seed (02,20) replaced by another normalised irreducible
    # balanced pair, (021,120), which is not otherwise listed.
    bad = sq.copy()
    bad.graph.bpa.states[1] = Pair([0, 2, 1], [1, 2, 0])
    assert_refused(bad, "L2", "a normalised swap seed is not listed")

    # L1 and L0: the PIP record, synchronize mode, the target letter.
    bad = sq.copy()
    bad.pip = True
    assert_refused(bad, "L1", "recorded PIP status differs from the incidence matrix")
    bad = sq.copy()
    bad.graph.synchronize = True
    assert_refused(bad, "L0", SYNC_RIGHT_REFUSAL)
    bad = sq.copy()
    bad.graph.target = 3
    assert_refused(bad, "L0", "target outside -1..2")

    # Changing the target without recomputing success flags is refused at L4.
    var rs = fixture([[1], [0, 2], [2, 0, 2]])
    var first = -1
    for i in range(len(rs.graph.packets)):
        if first == -1 and rs.graph.packets[i].success:
            first = i
    assert_true(first >= 0)
    var wrong = rs.copy()
    wrong.graph.target = (rs.graph.packets[first].top_letter + 1) % 3
    assert_refused(wrong, "L4", "success flag differs from interior coincidence and target")
    # The rebuilt square for that letter is accepted, with fewer successes.
    var lettered = fixture([[1], [0, 2], [2, 0, 2]], wrong.graph.target)
    assert_true(verify_packet_square(lettered))
    assert_true(success_count(lettered) < success_count(rs))
    assert_equal(len(lettered.graph.packets), len(rs.graph.packets))

    # The producer refuses inconsistent graph data before any export.
    var g = sq.graph.copy()
    g.split_count += 1
    var message = String("")
    try:
        _ = packet_stars(g)
    except e:
        message = String(e)
    assert_true("recomputed split entries differ from split_count" in message, message)
    g = sq.graph.copy()
    _ = g.adj[0].pop(0)
    message = String("")
    try:
        _ = packet_stars(g)
    except e:
        message = String(e)
    assert_true("packet-square L5: " in message, message)

    # Emission refuses an unverified square.
    bad = sq.copy()
    _ = bad.stars[0].pop(2)
    message = String("")
    try:
        _ = packet_square_jsonl(bad, True)
    except e:
        message = String(e)
    assert_true("star is missing a digit pair" in message, message)
    message = String("")
    try:
        _ = packet_square_lean(bad, "Scratch.Module", True, "")
    except e:
        message = String(e)
    assert_true("star is missing a digit pair" in message, message)


def test_caps_and_synchronize_mode_refuse() raises:
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1]]
    # A state-capped and a length-capped automaton: no table is built from either.
    var capped = build_bounded(sigma3(sigma), 1, 10000)
    var length_capped = build_bounded(sigma3(sigma), 20000, 1)
    assert_false(capped.complete())
    assert_false(length_capped.complete())
    var message = String("")
    try:
        _ = build_packet_square(sigma, capped.graph)
    except e:
        message = String(e)
    assert_true("automaton is capped" in message, message)
    message = String("")
    try:
        _ = build_packet_square(sigma, length_capped.graph)
    except e:
        message = String(e)
    assert_true("automaton is capped" in message, message)
    var a = build_bounded(sigma3(sigma), 20000, 10000)
    assert_true(a.complete())
    message = String("")
    try:
        _ = build_packet_square(sigma, a.graph, packet_cap=1)
    except e:
        message = String(e)
    assert_true("packet cap exhausted: diagnostic inconclusive" in message, message)
    message = String("")
    try:
        _ = build_packet_square(sigma, a.graph, edge_cap=1)
    except e:
        message = String(e)
    assert_true("packet edge cap exhausted: diagnostic inconclusive" in message, message)
    message = String("")
    try:
        _ = build_packet_square(sigma, a.graph, target=3)
    except e:
        message = String(e)
    assert_true("packet-square L0: " in message, message)
    # sync-right is refused at the boundary and by the producer.
    message = String("")
    try:
        _ = parse_packet_square_target("sync-right")
    except e:
        message = String(e)
    assert_equal(message, String(SYNC_RIGHT_REFUSAL))
    assert_equal(parse_packet_square_target("any"), -1)
    assert_equal(parse_packet_square_target("2"), 2)
    message = String("")
    try:
        _ = parse_packet_square_target("3")
    except e:
        message = String(e)
    assert_true("target must be any, 0, 1 or 2" in message, message)
    var sync_sigma: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var b = build_bounded(sigma3(sync_sigma), 20000, 10000)
    assert_true(b.complete())
    var synced = build_packets(sync_sigma, b.graph, 200000, 2000000, -1, True)
    message = String("")
    try:
        _ = packet_stars(synced)
    except e:
        message = String(e)
    assert_true(SYNC_RIGHT_REFUSAL in message, message)


def test_emission_formats() raises:
    var sq = fixture([[1], [0, 1, 2], [1]])
    var lines = packet_square_jsonl(sq, True)
    assert_equal(len(lines), 1 + 4 + 6 + 46 + 46 + 1 + 9 + 1)
    var bare = packet_square_jsonl(sq, False)
    assert_equal(len(bare), len(lines) - 9)
    var hub_free = True
    for i in range(len(bare)):
        if '"record":"hub"' in bare[i]:
            hub_free = False
    assert_true(hub_free)
    assert_true('"hub_rows":0}' in bare[0])
    assert_true('"hub_rows":9}' in lines[0])
    assert_true('"pip":false' in lines[0])
    var want: List[String] = [
        '{"record":"packet","id":12,"state":0,"orientation":-1,"occurrences":[0,0],"factor_edge":0,"top_address":[0,0,0,0],"bottom_address":[0,0,0,0],"target_letters":[1,0],"residual":[0,0,0],"interior":false,"success":false,"birth":[0,0,0]}',
        '{"record":"star","packet":0,"expanded":true,"entries":[["child",0,0,12],["child",0,1,13],["split",0,2,0,1]]}',
        '{"record":"star","packet":21,"expanded":false,"entries":[]}',
        '{"record":"hub","state":0,"hub":0,"factors":[0,1],"bits":[1,null]}',
        '{"record":"key_order","packets":[12,38,13,39,14,40,15,41,0,30,22,1,32,24,2,31,23,3,33,25,4,5,6,7,34,26,35,27,36,28,37,29,8,16,42,9,18,44,10,17,43,11,19,45,20,21]}',
    ]
    for w in range(len(want)):
        var found = False
        for i in range(len(lines)):
            if lines[i] == want[w]:
                found = True
        assert_true(found, want[w])

    var lean = packet_square_lean(sq, "PscVerif.PacketSquareData.NonPisot", True, "replay command")
    var theorems = 0
    var imports = 0
    for i in range(len(lean)):
        if lean[i].startswith("theorem "):
            theorems += 1
            assert_equal(lean[i], String("theorem accepted : table.check = true := by decide +kernel"))
        if lean[i].startswith("import "):
            imports += 1
            assert_equal(lean[i], String("import PscVerif.PacketCertificate"))
        assert_false("sorry" in lean[i] or "native_decide" in lean[i] or "private" in lean[i] or "set_option" in lean[i])
    assert_equal(theorems, 1)
    assert_equal(imports, 1)
    assert_equal(lean[len(lean) - 1], String("end PscVerif.PacketSquareData.NonPisot"))
    # Literal anchors, independent of both emitters.
    var lean_want: List[String] = [
        "namespace PscVerif.PacketSquareData.NonPisot",
        "  s := ![[1], [0, 1, 2], [1]]",
        "  target := none",
        "    ⟨0, 0, 0, false, 0, 2, 4⟩,",
        "    ⟨0, false, 0, 1, some 0, some (0, 0, 0, 0), some (0, 1, 1, 1), (1, 1), [-1, 0, 0], false, false, some (0, 0, 1)⟩,",
        "    [.child 0 0 12, .child 0 1 13, .split 0 2 0 1],",
        "    ⟨0, 0, [some true, none]⟩,",
        "    12, 38, 13, 39, 14, 40, 15, 41, 0, 30, 22, 1, 32, 24, 2, 31, 23, 3, 33, 25,",
    ]
    for w in range(len(lean_want)):
        var found = False
        for i in range(len(lean)):
            if lean[i] == lean_want[w]:
                found = True
        assert_true(found, lean_want[w])
    var no_hubs = packet_square_lean(sq, "M", False, "")
    var empty_hubs = False
    for i in range(len(no_hubs)):
        if no_hubs[i] == "  hubs := []":
            empty_hubs = True
    assert_true(empty_hubs)
    var lettered = fixture([[1], [0, 1, 2], [1]], 1)
    var lean_letter = packet_square_lean(lettered, "M", False, "")
    var some_target = False
    for i in range(len(lean_letter)):
        if lean_letter[i] == "  target := some 1":
            some_target = True
    assert_true(some_target)
    assert_true('"target":1,' in packet_square_jsonl(lettered, False)[0])
    # Module names are ASCII identifiers separated by dots.
    var bad_names: List[String] = ["", "1abc", "a..b", "a b", "a.b-c", ".a", "a."]
    for k in range(len(bad_names)):
        var caught = False
        try:
            check_lean_module_name(bad_names[k])
        except:
            caught = True
        assert_true(caught, bad_names[k])
    check_lean_module_name("PscVerif.PacketSquareData.RealSecondary")


def test_lean_emission_equals_committed_jsonl() raises:
    """The Lean emitter, row by row, against the committed JSONL evidence.

    For each fixture: the exporter prints exactly the committed rows of
    evidence/packet-square-2026-11-10 (after the budget row, which is the
    default budget), and `packet_square_lean` prints line for line the module
    `lean_from_jsonl` renders from that committed text. Then the same for a
    letter target without hub rows, from the in-memory rows.
    """
    var names: List[String] = ["tribonacci", "real-secondary", "non-pisot-strict", "gf-actual"]
    var modules: List[String] = ["Tribonacci", "RealSecondary", "NonPisot", "GfActual"]
    var sigmas = fixture_sigmas()
    for c in range(len(names)):
        var rows = jsonl_rows(read_text(String(EVIDENCE) + names[c] + ".jsonl"))
        assert_equal(rows[0], budget_json(20000, 10000, 200000, 2000000))
        var sq = fixture(sigmas[c])
        assert_lines_equal(with_budget(packet_square_jsonl(sq, True)), rows, names[c] + ".jsonl")
        var module = String("PscVerif.PacketSquareData.") + modules[c]
        var command = String("regeneration command of ") + names[c]
        assert_lines_equal(packet_square_lean(sq, module, True, command), lean_from_jsonl(rows, module, command),
                           names[c] + " Lean module")
    var lettered = fixture([[1], [0, 1, 2], [1]], 1)
    var rows = with_budget(packet_square_jsonl(lettered, False))
    assert_lines_equal(packet_square_lean(lettered, "Scratch.Lettered", False, ""),
                       lean_from_jsonl(rows, "Scratch.Lettered", ""), "1/012/1 target 1 Lean module")
    # The comparison sees a one-field change in one row: the bottom address
    # of packet 209 of 1/02/202 printed with the top address's source.
    var rs_rows = jsonl_rows(read_text(String(EVIDENCE) + "real-secondary.jsonl"))
    var rendered = lean_from_jsonl(rs_rows, "M", "")
    var row209 = String("    ⟨8, false, 4, 4, some 16, some (2, 0, 4, 4), some (1, 2, 4, 4), (0, 2), [-1, 1, 0], false, false, some (44, 0, 2)⟩,")
    var at = -1
    for k in range(len(rendered)):
        if rendered[k] == row209:
            at = k
    assert_true(at >= 0, row209)
    var forged = rendered.copy()
    forged[at] = String("    ⟨8, false, 4, 4, some 16, some (2, 0, 4, 4), some (2, 2, 4, 4), (0, 2), [-1, 1, 0], false, false, some (44, 0, 2)⟩,")
    var caught = String("")
    try:
        assert_lines_equal(forged, rendered, "forged")
    except e:
        caught = String(e)
    assert_true(("line " + String(at + 1)) in caught, caught)


def main() raises:
    test_fixture_counts()
    test_real_secondary_rows_and_seed_depth_two()
    test_mutations_refuse_at_their_layer()
    test_caps_and_synchronize_mode_refuse()
    test_emission_formats()
    test_lean_emission_equals_committed_jsonl()
    print("[PASS] packet-square-v1 export: four fixtures, literal stars and splits, births, key order, hub bits, mutation controls at their checks, caps, sync-right, Lean emission row by row against the committed JSONL")
    require_contract("packet-square-v1 export: every packet's full literal digit star with split ordinals, root-reachable births, distinct keys and undefined hub bits as null; caps and synchronize mode refuse")
