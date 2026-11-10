"""Tests of the independent packet-square-v1 oracle (`oracles/python/packet_square_oracle.py`).

The canonical exporter is `kernel/psc/packet_square_export.mojo`; acceptance of a table is
decided by the Lean checker `Psc.PacketCertificate.Table.check`. These tests run without Mojo
or Lean. They pin, on the four committed fixtures of `evidence/packet-square-2026-11-10/`:

1. every JSONL file is rebuilt from `sigma` alone and its bytes equal the rebuild (a carriage
   return or a missing final newline is refused);
2. the clause-by-clause audit accepts every committed table, the table is a fixed point of
   the literal transition and every packet is reachable from a root, and each named forgery
   is refused at its named layer (a root-unreachable mirrored closure, a dropped split entry,
   exchanged split ordinals, a side-swapped row, a wrong factor ordinal, a late birth, a
   coerced hub bit, a wrong global position, JSON values of the wrong type or shape, a budget
   row that does not admit the table, rows that cannot be read as a table);
3. the residual transport law `r' = M r + lambda` on every child entry, from the listed
   words of both rows, its asynchronous form on every digit pair, and the split account;
4. agreement with the archived `target-aware-bpa-v1` dumps, a bounded absolute replay in
   the iterates of the swap seeds and of their swaps, and the committed Lean data modules
   field by field and against a template rendered from the JSONL. That test fails when
   `proof/PscVerif/PscVerif.lean` imports a data module whose file is absent, and skips,
   naming the paths it looked for, only when the module is neither present nor imported;
5. the command line: exit 0 with the pass line only when every check passed and all four
   Lean data modules were compared; exit 1 on a mutated, re-encoded or malformed fixture
   and on a missing module; exit 2 (INCOMPLETE, never the pass line) for a missing module
   under `--allow-missing-lean`;
6. the hand-decoded rows 209 and 429 of `1/02/202`, the depth-two success and the
   second-letter control from the seed `(01, 10)`, and the dead-end, productive-root and
   seed-reach counts of the four graphs.

Every number pinned here is a finite observation about four tables, not a theorem. The
packet, edge, split, root, success and PIP counts (`COUNTS`) are the canonical Mojo pins of
`kernel/tests/test_packet_square_export.mojo` (`test_fixture_counts`), here recomputed from
sigma; the seed-reach, dead-end and productive-root counts are pinned here only, as
Python-oracle observations on the committed tables, with no canonical Mojo pin. Nothing here
moves a claim or concerns C4, G1, #84, #138, #139 or PSC.
"""

import ast
import hashlib
import importlib.util
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT / "oracles/python/packet_square_oracle.py"
spec = importlib.util.spec_from_file_location("packet_square_oracle", PATH)
o = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = o
spec.loader.exec_module(o)

NAMES = list(o.FIXTURES)
# packets, edges (child entries), split entries, roots, successes, pip: the canonical pins of
# `test_fixture_counts` in kernel/tests/test_packet_square_export.mojo, here recomputed from
# sigma by the oracle.
COUNTS = {
    "tribonacci": (132, 185, 194, 37, 0, True),
    "real-secondary": (507, 948, 1274, 118, 23, True),
    "non-pisot-strict": (46, 82, 82, 12, 1, False),
    "gf-actual": (153, 235, 220, 39, 6, True),
}
_ROWS = {}


def lean_list(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def rows_of(name):
    if name not in _ROWS:
        _ROWS[name] = o.load_rows(o.fixture_path(name))
    return o._copy(_ROWS[name])


def test_oracle_is_independent_of_the_kernel():
    """No import of kernel/ or of a Lean file; the only repository import is the PIP screen."""
    tree = ast.parse(PATH.read_text())
    modules = {a.name for n in ast.walk(tree) if isinstance(n, ast.Import) for a in n.names}
    modules |= {n.module for n in ast.walk(tree) if isinstance(n, ast.ImportFrom)}
    assert modules <= {"__future__", "argparse", "hashlib", "json", "re", "sys", "collections",
                       "pathlib", "psc_research.pip_screen"}
    assert "kernel" not in "".join(sorted(modules))
    assert "float(" not in PATH.read_text() and "random" not in modules


def test_digests_of_the_committed_evidence():
    assert sorted(o.check_digests()) == sorted(f"{n}.jsonl" for n in NAMES)


@pytest.mark.parametrize("name", NAMES)
def test_rebuild_from_sigma_alone(name):
    rebuilt = o.rebuild(o.parse_sigma(o.FIXTURES[name][0]))
    assert ("\n".join(o.render(rebuilt)) + "\n").encode() == o.fixture_path(name).read_bytes()
    assert o.compare_rebuild(name) == len(rebuilt)
    t = o.Table(rebuilt)
    h = t.header
    assert (h["packets"], h["edges"], h["split_descendants"], h["roots"],
            sum(p["success"] for p in t.packets), h["pip"]) == COUNTS[name]


def evidence_copy(tmp_path, edit=None, sums=True):
    """A copy of the evidence directory; `edit` rewrites the bytes of non-pisot-strict.jsonl,
    and `sums` regenerates SHA256SUMS so that only the later checks can refuse."""
    d = tmp_path / "evidence"
    shutil.copytree(o.EVIDENCE, d)
    if edit is not None:
        f = d / "non-pisot-strict.jsonl"
        f.write_bytes(edit(f.read_bytes()))
    if sums:
        (d / "SHA256SUMS").write_text("".join(
            f"{hashlib.sha256(f.read_bytes()).hexdigest()}  {f.name}\n"
            for f in sorted(d.glob("*.jsonl"))))
    return d


def one_residual_edit(data):
    """Packet 13 of `1/012/1`: residual [-1,0,0] -> [-1,0,1] (valid JSON, one byte)."""
    old = b'"residual":[-1,0,0],"interior":false,"success":false,"birth":[0,0,1]}'
    assert data.count(old) == 1
    return data.replace(old, old.replace(b"[-1,0,0]", b"[-1,0,1]"))


@pytest.mark.parametrize("label,edit,match", [
    ("carriage returns", lambda b: b.replace(b"\n", b"\r\n"), "row 1 differs"),
    ("no final newline", lambda b: b[:-1], "missing final newline"),
    ("one residual", one_residual_edit, "row 26 differs"),
])
def test_rebuild_comparison_is_byte_for_byte(tmp_path, label, edit, match):
    d = evidence_copy(tmp_path, edit)
    assert sorted(o.check_digests(d)) == sorted(f"{n}.jsonl" for n in NAMES)
    with pytest.raises(o.InvalidPacketSquare, match=match) as e:
        o.compare_rebuild("non-pisot-strict", d)
    assert e.value.layer == "L0"
    assert o.compare_rebuild("tribonacci", d) == 301


def test_rebuild_reproduces_the_hand_decoded_rows():
    """Rows 209 and 429 of `1/02/202` and their 2-cycle, decoded by hand from the archive in
    `proof/PscVerif/PscVerif/OccurrenceGraph.lean` (`rs_rows_edges`) and pinned by the Mojo
    regression test; here rebuilt from sigma by the oracle."""
    t = o.Table(o.rebuild(o.parse_sigma("1/02/202")))
    assert o.render([t.packets[209], t.packets[429]]) == [
        '{"record":"packet","id":209,"state":8,"orientation":-1,"occurrences":[4,4],'
        '"factor_edge":16,"top_address":[2,0,4,4],"bottom_address":[1,2,4,4],'
        '"target_letters":[0,2],"residual":[-1,1,0],"interior":false,"success":false,'
        '"birth":[44,0,2]}',
        '{"record":"packet","id":429,"state":7,"orientation":1,"occurrences":[2,1],'
        '"factor_edge":19,"top_address":[4,0,9,2],"bottom_address":[4,0,8,1],'
        '"target_letters":[1,2],"residual":[1,-1,1],"interior":false,"success":false,'
        '"birth":[209,0,0]}']
    assert t.stars[209]["entries"] == [["child", 0, 0, 429], ["child", 0, 1, 430],
                                       ["split", 0, 2, 2, 3]]
    assert ["child", 0, 2, 209] in t.stars[429]["entries"]
    m = o.incidence(t.sigma)
    assert m == ((0, 1, 1), (1, 0, 0), (0, 1, 2))
    assert o.act(m, (-1, 1, 0)) == (1, -1, 1)
    assert o.add(o.act(m, (1, -1, 1)), o.defect((1,), (2, 0, 2), 0, 2)) == (-1, 1, 0)


def test_seed_01_10_depth_two_success_and_second_letter_control():
    """Seed `(01, 10)` of `1/02/202` (docs/target-aware-bpa-diagnostic-2026-10-02.md, the
    paragraph on the default swap seed): no depth-one descendant of roots 0-3 is a success;
    the success 346 is reached as 2 -(1,1)-> 124 -(0,2)-> 346. At depth two the words are
    `(021202, 120202)` with cuts 0, 3, 4, 5, 6; the pair (3, 3) is the interior diagonal
    child start, read as the success 346, and position 1 has the matching letters
    (2, 2) at a nonzero residual: that pair is packet 341, read as 0 -(0,1)-> 119 -(1,0)->
    341 (state 7 = (021, 120), orientation +1, local positions (1, 1), residual (1, -1, 0)),
    not a success, so "second letter, depth one" is not a success. Packet 154 (state 7,
    orientation -1, (1, 1), the same factor 6) is its mirror: it is born from root 15 of state
    3, outside the reach of the seed roots, and is what the swapped frame `(10, 01)` reads at
    the same position."""
    t = o.Table(o.rebuild(o.parse_sigma("1/02/202")))
    assert t.states[0] == ((0, 1), (1, 0))
    depth_one = {e[3] for i in range(4) for e in t.stars[i]["entries"] if e[0] == "child"}
    assert depth_one == set(range(118, 127))
    assert not any(t.packets[i]["success"] for i in depth_one)
    assert ["child", 1, 1, 124] in t.stars[2]["entries"]
    assert ["child", 0, 2, 346] in t.stars[124]["entries"] and t.packets[346]["success"]
    U, V = (0, 1), (1, 0)
    for _ in range(2):
        U, V = o.inflate(t.sigma, U), o.inflate(t.sigma, V)
    assert (U, V) == ((0, 2, 1, 2, 0, 2), (1, 2, 0, 2, 0, 2))
    assert o.balanced_cuts(U, V) == [0, 3, 4, 5, 6]
    assert (U[1], V[1], o.defect(U, V, 1, 1)) == (2, 2, (1, -1, 0))
    readings = o.frame_readings(t, (0, 1), (1, 0), 2)[2]
    assert readings[3, 3] == o._fields(t.packets[346])
    assert ["child", 0, 1, 119] in t.stars[0]["entries"]
    assert ["child", 1, 0, 341] in t.stars[119]["entries"]
    p = t.packets[341]
    assert (t.states[p["state"]], p["state"], p["orientation"], p["occurrences"],
            p["factor_edge"], p["target_letters"], p["residual"], p["birth"]) == (
        ((0, 2, 1), (1, 2, 0)), 7, 1, [1, 1], 6, [2, 2], [1, -1, 0], [119, 1, 0])
    assert (p["interior"], p["success"]) == (False, False)
    assert readings[1, 1] == o._fields(p)
    q = t.packets[154]
    assert o._fields(q) == o._fields(o._mirror(p, None))
    assert q["birth"] == [15, 0, 1] and t.packets[15]["factor_edge"] == -1
    assert t.states[t.packets[15]["state"]] == ((0, 2, 1), (1, 0, 2))  # not a swap seed
    assert [s["packet"] for s in t.stars if any(e[0] == "child" and e[3] == 154
                                                for e in s["entries"])] == [15]
    assert o.frame_readings(t, (1, 0), (0, 1), 2)[2][1, 1] == o._fields(q)


@pytest.mark.parametrize("name", NAMES)
def test_committed_tables_are_accepted(name):
    rows = rows_of(name)
    assert o.audit(rows) == {}
    packets, edges, splits, roots, _, _ = COUNTS[name]
    counts = o.verify(rows)
    assert (counts["packets"], counts["edges"], counts["split_descendants"], counts["roots"]) == (
        packets, edges, splits, roots)


@pytest.mark.parametrize("name", NAMES)
def test_fixed_point_and_reachability_from_roots(name):
    """The table contains the roots, every literal child of every listed packet is listed
    (the L5 star equation resolves each child key to a listed row), and every listed packet
    is reached from a root: the least fixed point, not a superset of it."""
    t = o.Table(rows_of(name))
    ids = o._resolve(t)
    factor_of = {(f["parent"], f["ordinal"]): f["id"] for f in t.factors}
    for p, star in zip(t.packets, t.stars):
        assert o.expected_star(t, p, ids, factor_of) == (star["expanded"], star["entries"])
    roots = [p["id"] for p in t.packets if p["factor_edge"] == -1]
    assert len(roots) == COUNTS[name][3] and roots == list(range(len(roots)))
    assert o.unreachable(t) == []
    for p in t.packets[len(roots):]:
        j, d, e = p["birth"]
        assert j < p["id"] and ["child", d, e, p["id"]] in t.stars[j]["entries"]


def test_root_unreachable_mirrored_closure_is_refused():
    """Mirror the forward closure of the 2-cycle 127 -(0,0)-> 162 -(0,0)-> 127 of `1/02/202`.

    Each added row is a literal occurrence pair with its literal star, and the enlarged table
    is still closed under the literal transition, so every local check passes (rows, stars,
    transport law, split account); only reachability from the roots (and the births, which
    imply it) refuses it. This is the v1 form of the forged file that passed the former
    fixed-point-only oracle of the archive (33 mirrored packets).
    """
    rows = rows_of("real-secondary")
    t = o.Table(rows)
    assert ["child", 0, 0, 162] in t.stars[127]["entries"]
    assert ["child", 0, 0, 127] in t.stars[162]["entries"]
    forged = o.forged_mirror(rows, {127, 162})
    f = o.Table(forged)
    added = list(range(len(t.packets), len(f.packets)))
    assert len(added) == 33
    failures = o.audit(forged)
    assert set(failures) == {"L6"}
    assert any("unreachable from every root" in r for r in failures["L6"])
    assert any("birth" in r for r in failures["L6"])
    assert o.unreachable(f) == added
    children, splits, violations = o.transport_law(forged)
    assert violations == [] and children > COUNTS["real-secondary"][1]
    assert o.split_account(forged)["children"] == children
    with pytest.raises(o.InvalidPacketSquare, match="unreachable from every root") as e:
        o.verify(forged)
    assert e.value.layer == "L6"


def test_a_mirror_of_a_listed_closure_adds_nothing():
    """The forgery generator is exact: the 209/429 cycle's closure is already mirror-closed."""
    rows = rows_of("real-secondary")
    assert o.forged_mirror(rows, {209, 429}) == rows


CONTROLS = [
    # (name, generator on the 1/012/1 rows, first failing layer, exact layer set or None)
    ("dropped split entry", lambda r: o.drop_split(r, 0, 2), "L5", {"L5"}),
    ("exchanged split ordinals", lambda r: o.swap_split_ordinals(r, 0, 2), "L5", {"L5"}),
    ("side-swapped row 12", lambda r: o.side_swap(r, 12), "L4", None),
    ("wrong factor ordinal", lambda r: o.wrong_factor_ordinal(r, 1, 0), "L3", None),
    ("birth at a later packet", lambda r: o.late_birth(r, 13), "L6", {"L6"}),
    ("coerced undefined hub bit", o.coerce_hub_bit, "L7", {"L7"}),
    ("wrong global position", lambda r: o.wrong_global_position(r, 13), "L4", {"L4"}),
]


@pytest.mark.parametrize("label,mutate,layer,exact", CONTROLS, ids=[c[0] for c in CONTROLS])
def test_negative_controls_are_refused_at_their_layer(label, mutate, layer, exact):
    rows = rows_of("non-pisot-strict")
    forged = mutate(rows)
    assert forged != rows
    failures = o.audit(forged)
    assert min(failures, key=o.LAYERS.index) == layer, failures
    if exact is not None:
        assert set(failures) == exact, failures
    with pytest.raises(o.InvalidPacketSquare) as e:
        o.verify(forged)
    assert e.value.layer == layer
    assert o.audit(rows) == {}


def test_side_swap_fails_at_the_letters_and_at_the_parent_star():
    failures = o.audit(o.side_swap(rows_of("non-pisot-strict"), 12))
    assert any("packet 12: letters" in r for r in failures["L4"])
    assert any("packet 0: literal child (0, -1, 0, 0, 0) is not listed" in r
               for r in failures["L5"])


def _row(rows, record, key=None, value=None):
    return next(r for r in rows if r["record"] == record and (key is None or r[key] == value))


def _first_hub_with(rows, bit):
    return next(r for r in rows if r["record"] == "hub" and bit in r["bits"])


def _set_bit(rows, old, new):
    r = _first_hub_with(rows, old)
    r["bits"][r["bits"].index(old)] = new


SHAPE_CONTROLS = [
    # (label, mutation, exact failing layers). With the layer set {"L0"} the forged rows are
    # equal to the committed rows under Python's 1 == 1.0 == True, so only the L0 JSON-shape
    # check can refuse them; the others are also refused by a later layer that compares by
    # identity or by value.
    ("residual as floats", lambda r: _row(r, "packet", "id", 13).update(
        residual=[float(x) for x in _row(r, "packet", "id", 13)["residual"]]), {"L0"}),
    ("residual entry true", lambda r: _row(r, "packet", "id", 2).update(residual=[True, 0, 0]),
     {"L0"}),
    ("hub bit true", lambda r: _set_bit(r, 1, True), {"L0"}),
    ("hub bit 1.0", lambda r: _set_bit(r, 1, 1.0), {"L0"}),
    ("star destination as float", lambda r: _row(r, "star", "packet", 0)["entries"][1]
     .__setitem__(3, float(_row(r, "star", "packet", 0)["entries"][1][3])), {"L0"}),
    ("header packets 46.0", lambda r: _row(r, "header").update(packets=46.0), {"L0"}),
    ("extra key on a packet row", lambda r: _row(r, "packet", "id", 13).update(extra=1),
     {"L0"}),
    ("packet keys reordered", lambda r: r.__setitem__(
        r.index(_row(r, "packet", "id", 13)),
        dict(reversed(list(_row(r, "packet", "id", 13).items())))), {"L0"}),
    ("budget below the state count", lambda r: r[0].update(bpa_states=3), {"L0"}),
    ("budget below the longest state", lambda r: r[0].update(bpa_length=1), {"L0"}),
    ("budget below the packet count", lambda r: r[0].update(packets=45), {"L0"}),
    ("budget below the edge count", lambda r: r[0].update(edges=81), {"L0"}),
    ("hub bit 2", lambda r: _set_bit(r, 1, 2), {"L0", "L7"}),
    ("header pip 1", lambda r: _row(r, "header").update(pip=1), {"L0", "L1"}),
    ("coincidence flag 1", lambda r: _row(r, "state", "id", 3).update(coincidence=1),
     {"L0", "L2"}),
]


@pytest.mark.parametrize("label,mutate,layers", SHAPE_CONTROLS,
                         ids=[c[0] for c in SHAPE_CONTROLS])
def test_json_shape_and_budget_controls_are_refused_at_l0(label, mutate, layers):
    rows = rows_of("non-pisot-strict")
    forged = o._copy(rows)
    mutate(forged)
    assert o.render(forged) != o.render(rows)
    failures = o.audit(forged)
    assert set(failures) == layers, failures
    with pytest.raises(o.InvalidPacketSquare) as e:
        o.verify(forged)
    assert e.value.layer == "L0"


def test_admissible_variants_are_tables_and_only_the_rebuild_pins_the_committed_file():
    """`verify` judges a table, not the committed file: a budget row that admits the table and
    a target letter that changes no success bit give tables the exporter would print for that
    budget or target (the rebuild shows it); the committed file is pinned by its bytes."""
    rows = rows_of("non-pisot-strict")
    sigma = o.parse_sigma("1/012/1")
    for budget in (4, 5):
        variant = o._copy(rows)
        variant[0]["bpa_states"] = budget
        assert o.verify(variant)["states"] == 4
        assert o.rebuild(sigma, budget={**o.DEFAULT_BUDGET, "bpa_states": budget}) == variant
    with pytest.raises(o.BudgetExhausted, match="inconclusive"):
        o.rebuild(sigma, budget={**o.DEFAULT_BUDGET, "bpa_states": 3})
    variant = o._copy(rows)
    variant[1]["target"] = 1  # the one success of 1/012/1 is a coincidence of letter 1
    assert o.verify(variant) and o.rebuild(sigma, target=1) == variant
    variant[1]["target"] = 0  # its success bit is then wrong (a coincidence is terminal
    assert set(o.audit(variant)) == {"L4"}  # either way, so its star is unchanged)


def _without(rows, row, key=None):
    if key is None:
        rows.remove(row)
    else:
        row.pop(key)
    return rows


MALFORMED = [
    # (label, rows -> malformed value); each reaches `verify` as a refusal, never a raw error.
    ("a row that is not an object", lambda r: r[:3] + [[1, 2, 3]] + r[3:]),
    ("a state row without top", lambda r: _without(r, _row(r, "state", "id", 1), "top")),
    ("sigma null", lambda r: [{**x, "sigma": None} if x["record"] == "header" else x
                              for x in r]),
    ("a packet row without birth", lambda r: _without(r, _row(r, "packet", "id", 20), "birth")),
    ("no key order row", lambda r: _without(r, _row(r, "key_order"))),
    ("not a list of rows", lambda r: {"rows": r}),
]


@pytest.mark.parametrize("label,mutate", MALFORMED, ids=[c[0] for c in MALFORMED])
def test_malformed_rows_refuse_at_l0_without_a_raw_exception(label, mutate):
    forged = mutate(rows_of("non-pisot-strict"))
    failures = o.audit(forged)
    assert "L0" in failures, failures
    with pytest.raises(o.InvalidPacketSquare) as e:
        o.verify(forged)
    assert e.value.layer == "L0"


def test_a_line_that_is_not_json_refuses_at_l0(tmp_path):
    f = tmp_path / "bad.jsonl"
    f.write_text('{"record":"budget"}\n{"record":\n')
    with pytest.raises(o.InvalidPacketSquare, match="line 2 is not JSON") as e:
        o.load_rows(f)
    assert e.value.layer == "L0"


@pytest.mark.parametrize("name", NAMES)
def test_residual_transport_law_on_every_edge(name):
    rows = rows_of(name)
    children, splits, violations = o.transport_law(rows)
    assert violations == []
    assert (children, splits) == COUNTS[name][1:3]


@pytest.mark.parametrize("name", NAMES)
def test_transport_law_is_not_vacuous(name):
    """Dropping lambda breaks the law on some edge of every fixture; the transposed incidence
    breaks it exactly where M is not symmetric (`1/012/1` has a symmetric M, so the transpose
    is no control there)."""
    rows = rows_of(name)
    m = o.incidence(o.Table(rows).sigma)
    without = o.transport_law(rows, forcing=False)[2]
    assert any(v[0] == "child" for v in without)
    transposed = o.transport_law(rows, matrix=o.transpose(m))[2]
    assert bool(transposed) == (m != o.transpose(m))


@pytest.mark.parametrize("name", NAMES)
def test_split_account(name):
    account = o.split_account(rows_of(name))
    _, edges, splits, _, _, _ = COUNTS[name]
    assert account == {"children": edges, "splits": splits, "digit_pairs": edges + splits}


def test_split_account_refuses_a_dropped_split():
    with pytest.raises(o.InvalidPacketSquare, match="every digit pair once"):
        o.split_account(o.drop_split(rows_of("non-pisot-strict"), 0, 2))


@pytest.mark.parametrize("name", o.ARCHIVED)
def test_v1_rows_agree_with_the_archived_target_aware_dump(name):
    archive = o.load_rows(o.ARCHIVE / f"{name}.jsonl")
    assert o.compare_with_archive(rows_of(name), archive) == COUNTS[name][1]


# Python-oracle observations on the committed tables (no canonical Mojo pin): packets read by
# retained absolute pairs up to level 9 from the three normalised swap seeds. Level 9 exceeds
# the child depth of every seed-root reach (4, 8, 2, 5), so these are all the packets
# reachable from the seed roots. The other packets are never read in the normalised seed
# iterates: on `01/02/0` and `1/2/021` they are exactly the 25 and 27 non-seed root rows; on
# `1/02/202` they are the 106 non-seed root rows and the 12 non-root packets 150-161; on
# `1/012/1` there are none (its 12 roots are the seed roots).
REPLAY_HITS = {"tribonacci": 107, "real-secondary": 389, "non-pisot-strict": 46, "gf-actual": 126}
SEED_REACH_DEPTH = {"tribonacci": 4, "real-secondary": 8, "non-pisot-strict": 2, "gf-actual": 5}
NOT_READ = {"tribonacci": (25, []), "real-secondary": (106, list(range(150, 162))),
            "non-pisot-strict": (0, []), "gf-actual": (27, [])}
# Distinct readings of the swapped frames (ba, ab) up to level 9, and how many of them are
# listed packets (the twelve mirrored roots never are).
SWAP_LISTED = {"tribonacci": (107, 90), "real-secondary": (389, 328),
               "non-pisot-strict": (46, 32), "gf-actual": (126, 110)}


@pytest.mark.parametrize("name", NAMES)
def test_bounded_absolute_replay(name):
    rows = rows_of(name)
    replay = o.absolute_replay(rows, 9)
    assert replay["packets_hit"] == REPLAY_HITS[name]
    assert replay["pairs_per_level"][0] == 12
    assert (replay["swap_readings"], replay["swap_readings_listed"]) == SWAP_LISTED[name]
    assert o.absolute_replay(rows, 10)["packets_hit"] == REPLAY_HITS[name]
    t = o.Table(rows)
    seeds = {t.states.index(((a, b), (b, a))) for a in range(3) for b in range(a + 1, 3)}
    near = {p["id"] for p in t.packets if p["factor_edge"] == -1 and p["state"] in seeds}
    frontier, depth = set(near), 0
    while True:
        frontier = {e[3] for i in frontier for e in t.stars[i]["entries"] if e[0] == "child"}
        frontier -= near
        if not frontier:
            break
        near |= frontier
        depth += 1
    assert (len(near), depth) == (REPLAY_HITS[name], SEED_REACH_DEPTH[name])
    outside = sorted(set(range(len(t.packets))) - near)
    roots = [i for i in outside if t.packets[i]["factor_edge"] == -1]
    assert (len(roots), [i for i in outside if i not in roots]) == NOT_READ[name]
    assert all(t.packets[i]["state"] not in seeds for i in roots)


@pytest.mark.parametrize("name", NAMES)
def test_swapped_frame_reads_the_mirrors(name):
    """The swapped seed `(ba, ab)` reads, at every level, the mirror of the normalised reading
    of the exchanged pair; its level-0 readings are roots in orientation -1, never listed."""
    t = o.Table(rows_of(name))
    ids = {o.packet_key(p) for p in t.packets}
    for a, b in ((0, 1), (0, 2), (1, 2)):
        normal = o.frame_readings(t, (a, b), (b, a), 4)
        swapped = o.frame_readings(t, (b, a), (a, b), 4)
        for level, readings in enumerate(normal):
            assert swapped[level] == {(Q, P): o._fields(o._mirror(r, None))
                                      for (P, Q), r in readings.items()}
        assert all(r["orientation"] == -1 and r["factor_edge"] == -1
                   and (r["state"], -1, *r["occurrences"], -1) not in ids
                   for r in swapped[0].values())


def test_absolute_replay_refuses_a_wrong_residual():
    rows = rows_of("real-secondary")
    o._find(rows, "packet", "id", 429)["residual"] = [1, -1, 0]
    with pytest.raises(o.InvalidPacketSquare, match="absolute prefix defect"):
        o.absolute_replay(rows, 9)


def test_budgets_refuse_and_are_not_verdicts():
    sigma = o.parse_sigma("1/02/202")
    for cap in ("bpa_states", "bpa_length", "packets", "edges"):
        with pytest.raises(o.BudgetExhausted, match="inconclusive"):
            o.rebuild(sigma, budget={**o.DEFAULT_BUDGET, cap: 1})
    for bad in ("1/02", "1//202", "1/02/203"):
        with pytest.raises(o.InvalidPacketSquare) as e:
            o.parse_sigma(bad)
        assert e.value.layer == "L0"


def test_dead_ends_and_productive_roots():
    """Python-oracle observations on the committed tables (no canonical Mojo pin):
    noncoincident packets without a child entry (dead ends) and root packets that reach a
    coincidence packet. Dead ends exist on every fixture, so on these graphs "reaches the
    target" is not "every path reaches the target"."""
    observed = {}
    for name in NAMES:
        t = o.Table(rows_of(name))
        coincident = {p["id"] for p in t.packets
                      if t.states[p["state"]][0] == t.states[p["state"]][1]}
        dead = sum(p["id"] not in coincident and not any(e[0] == "child" for e in s["entries"])
                   for p, s in zip(t.packets, t.stars))
        good, changed = set(coincident), True
        while changed:
            changed = False
            for s in t.stars:
                if s["packet"] not in good and any(e[0] == "child" and e[3] in good
                                                   for e in s["entries"]):
                    good.add(s["packet"])
                    changed = True
        roots = [p["id"] for p in t.packets if p["factor_edge"] == -1]
        observed[name] = (dead, sum(r in good for r in roots), len(roots))
    assert observed == {"tribonacci": (38, 21, 37), "real-secondary": (208, 48, 118),
                        "non-pisot-strict": (12, 2, 12), "gf-actual": (42, 24, 39)}


def imported_data_modules():
    """The `import PscVerif.PacketSquareData...` lines of proof/PscVerif/PscVerif.lean."""
    text = (o.LEAN_ROOT / "PscVerif.lean").read_text()
    return re.findall(r"^import (PscVerif\.PacketSquareData\S*)\s*$", text, flags=re.M)


@pytest.mark.parametrize("name", NAMES)
def test_committed_lean_data_module_against_the_jsonl(name):
    layouts = [o.lean_module_path(name, layout) for layout in ("nested", "flat")]
    imported = [m for m in imported_data_modules() if m in {x for x, _ in layouts}]
    assert len(imported) <= 1, imported
    found = o.find_lean_module(name)
    if imported:
        # Imported by the library: the file must exist, in the imported layout.
        assert found is not None, (f"PscVerif.lean imports {imported[0]}, but its file is "
                                   f"absent (looked for {[str(p) for _, p in layouts]})")
        assert found[0] == imported[0]
    elif found is None:
        pytest.skip(f"Lean data module for {name} is neither in the tree nor imported by "
                    f"PscVerif.lean (looked for {[str(p) for _, p in layouts]}); nothing "
                    "compared")
    module, path = found
    text = path.read_text()
    rows = rows_of(name)
    table = o.parse_lean_module(text, module)
    assert o.compare_lean_module(table, rows, name, module) == COUNTS[name][0] > 0
    assert o.check_lean_template(text, rows, name, module) == 9
    # The field comparison is not vacuous: one changed residual and one exchanged pair of
    # key-order entries are each refused, by both guards.
    p = o.Table(rows).packets[-1]
    old = f"{lean_list(p['residual'])}, {str(p['interior']).lower()}"
    assert text.count(old) >= 1
    bad = text.replace(old, f"{lean_list([p['residual'][0] + 1, *p['residual'][1:]])}, "
                       f"{str(p['interior']).lower()}")
    with pytest.raises(o.InvalidPacketSquare):
        o.compare_lean_module(o.parse_lean_module(bad, module), rows, name, module)
    with pytest.raises(o.InvalidPacketSquare):
        o.check_lean_template(bad, rows, name, module)
    order = o.Table(rows).key_order
    head = ", ".join(map(str, order[:2]))
    swapped = text.replace(f"keyOrder := [\n    {head},",
                           f"keyOrder := [\n    {order[1]}, {order[0]},", 1)
    assert swapped != text
    with pytest.raises(o.InvalidPacketSquare, match="key order"):
        o.compare_lean_module(o.parse_lean_module(swapped, module), rows, name, module)
    with pytest.raises(o.InvalidPacketSquare):
        o.check_lean_template(swapped, rows, name, module)
    # Text the field comparison does not see is refused by the template.
    injections = {
        "instance": ("open Psc.PacketCertificate\n",
                     "open Psc.PacketCertificate\n\nlocal instance : LT (Fin 3) := "
                     "⟨fun _ _ => False⟩\n"),
        "option": ("theorem accepted", "set_option maxHeartbeats 0 in\ntheorem accepted"),
        "import": ("import PscVerif.PacketCertificate\n",
                   "import PscVerif.PacketCertificate\nimport PscVerif.PacketSquare\n"),
        "open": ("open Psc.PacketCertificate\n", "open Psc.PacketCertificate Psc.Reduction\n"),
        "example": ("by decide +kernel\n", "by decide +kernel\nexample : True := trivial\n"),
        "def": (f"\nend {module}", f"def table2 : Nat := 0\n\nend {module}"),
        "comment in the table": ("  keyOrder := [", "  -- 1, 2, 3\n  keyOrder := ["),
        "early end of the docstring": ("the key order.", "the key order. -/ def x := 1 /-"),
    }
    for label, (old, new) in injections.items():
        assert text.count(old) >= 1, label
        forged = text.replace(old, new, 1)
        # Every field still equals its row: only the template refuses these.
        assert o.compare_lean_module(o.parse_lean_module(forged, module), rows, name,
                                     module) == COUNTS[name][0], label
        with pytest.raises(o.InvalidPacketSquare):
            o.check_lean_template(forged, rows, name, module)
    # Boundary, stated rather than hidden: the prose of the docstring paragraph is not
    # compared here; the byte comparison with the emitter is kernel/check_packet_square.sh.
    edited = text.replace("by one kernel evaluation", "by one kernel evaluation (edited)", 1)
    assert edited != text and o.check_lean_template(edited, rows, name, module) == 9


def run_main(capsys, *argv):
    code = o.main(["--levels", "2", *argv])
    out, err = capsys.readouterr()
    return code, out, err


def test_command_line_runs_every_check(capsys):
    code, out, err = run_main(capsys, "--levels", "4")
    assert code == 0, err
    assert out.splitlines()[-1] == o.PASS_LINE and "INCOMPLETE" not in out


def test_command_line_refuses_missing_lean_modules(tmp_path, capsys):
    """An empty Lean root: no module is compared, so there is no pass line. Without the flag
    the run refuses (exit 1); with `--allow-missing-lean` it is INCOMPLETE (exit 2)."""
    empty = tmp_path / "lean"
    empty.mkdir()
    code, out, err = run_main(capsys, "--lean-root", str(empty))
    assert code == 1 and o.PASS_LINE not in out
    assert "REFUSED: Lean data modules missing" in err
    assert all(f"PscVerif.PacketSquareData.{s}" in err for _, s in o.FIXTURES.values())
    code, out, err = run_main(capsys, "--lean-root", str(empty), "--allow-missing-lean")
    assert code == 2 and o.PASS_LINE not in out
    assert out.splitlines()[-1].startswith("INCOMPLETE: Lean data modules not compared: ")
    # One module absent of four is enough: copy every present module except that of 1/2/021.
    partial = tmp_path / "partial"
    present = []
    for name in NAMES:
        found = o.find_lean_module(name)
        if found is not None and name != "gf-actual":
            target = partial / found[1].relative_to(o.LEAN_ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(found[1], target)
            present.append(found[0])
    code, out, err = run_main(capsys, "--lean-root", str(partial), "--allow-missing-lean")
    assert code == 2 and o.PASS_LINE not in out
    missing = out.splitlines()[-1]
    assert "PscVerif.PacketSquareData.GfActual" in missing
    assert not any(f"{module} (looked for" in missing for module in present)


def test_command_line_process_exit_code_for_missing_modules(tmp_path):
    """The script as a process (as CI or a reader runs it), on an empty Lean root."""
    result = subprocess.run([sys.executable, str(PATH), "--levels", "1", "--lean-root",
                             str(tmp_path), "--allow-missing-lean"], capture_output=True,
                            text=True)
    assert result.returncode == 2 and o.PASS_LINE not in result.stdout
    assert "INCOMPLETE" in result.stdout and "Traceback" not in result.stderr


@pytest.mark.parametrize("label,edit,sums,match", [
    ("one residual, SHA256SUMS stale", one_residual_edit, False, "digest differs"),
    ("one residual, SHA256SUMS regenerated", one_residual_edit, True, "row 26 differs"),
    ("carriage returns", lambda b: b.replace(b"\n", b"\r\n"), True, "row 1 differs"),
    ("no final newline", lambda b: b[:-1], True, "missing final newline"),
    ("a line that is not JSON", lambda b: b.replace(b'"record":"star"', b'"record":star"', 1),
     True, "not JSON"),
])
def test_command_line_refuses_a_mutated_fixture(tmp_path, capsys, label, edit, sums, match):
    d = evidence_copy(tmp_path, edit, sums)
    code, out, err = run_main(capsys, "--evidence", str(d))
    assert code == 1 and o.PASS_LINE not in out
    assert err.startswith("REFUSED: L0: ") and match in err
    assert "Traceback" not in err
