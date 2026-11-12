"""Authenticate the canonical addressed packet and emit finite Lean replay modules."""

import argparse
from dataclasses import dataclass, field
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "oracles/python"))
import c4_archived_graph_refinement as oracle

PACKET_HASHES = (
    "e960043f7481993fd56d7ac3976f119e132e00d5762bdcb78b8a061557ecfe8c",
    "915126ff282c0b1347c4518c57b7b7e350ebaaf1c6838c56776e6a12bdc61bc9",
)
COUNTS = (7150, 7083)
NUMERATORS = (99, 101)
CHUNK_SIZE = 32
SHARD_SIZE = CHUNK_SIZE * 16


@dataclass
class Fixture:
    images: list = field(default_factory=list)
    digits: list = field(default_factory=list)
    nodes: list = field(default_factory=list)
    slots: list = field(default_factory=list)


def authenticate(packet):
    oracle.require(len(packet) <= 16_000_000, "addressed payload byte budget")
    header, *lines = packet.decode("ascii").splitlines(keepends=True)
    oracle.require(header == f"schema {oracle.SCHEMA}\n", "wrong addressed schema")
    records = [line.split() for line in lines]
    hashes = [hashlib.sha256(), hashlib.sha256()]
    for line, record in zip(lines, records, strict=True):
        f = int(record[1])
        oracle.require(f in (0, 1), "unknown fixture")
        hashes[f].update(line.encode("ascii"))
    oracle.require(tuple(h.hexdigest() for h in hashes) == PACKET_HASHES,
                   "archived addressed payload hash mismatch")
    oracle.verify_native(packet.decode("ascii"))
    fixtures = [Fixture(), Fixture()]
    for kind, fixture, *fields in records:
        data = fixtures[int(fixture)]
        values = tuple(map(int, fields))
        if kind == "image":
            data.images.append(values[2:])
        elif kind == "digit":
            data.digits.append(values[1:])
        elif kind == "node":
            data.nodes.append(values[1:])
            data.slots.append([])
        elif kind == "slot":
            data.slots[values[0]].append(values[2:])
    return fixtures


def lean_list(items):
    return "[" + ", ".join(map(str, items)) + "]"


def lean_record(*fields):
    return "⟨" + ", ".join(map(str, fields)) + "⟩"


def lookup(name, type_name, entries):
    """Emit a balanced lookup with small leaves for kernel reduction."""
    lines = []
    for start in range(0, len(entries), CHUNK_SIZE):
        leaf = entries[start:start + CHUNK_SIZE]
        lines.append(f"def {name}{start} : List {type_name} := [\n  "
                     + ",\n  ".join(map(str, leaf)) + "\n]\n")

    def branch(lo, hi):
        if hi - lo == 1:
            start = lo * CHUNK_SIZE
            return f"{name}{start}[i - {start}]?"
        mid = (lo + hi) // 2
        return (f"(if i < {mid * CHUNK_SIZE} then {branch(lo, mid)}"
                f" else {branch(mid, hi)})")

    tree = f"def {name} (i : Nat) : Option {type_name} := {branch(0, len(lines))}\n"
    return lines, tree


def emit_data(f, data, output):
    order = sorted(range(len(data.nodes)), key=lambda i: data.nodes[i][:5])
    ranks = {i: rank for rank, i in enumerate(order)}
    nodes = []
    for i, ((a, b, x, y, z, weight, parent, position, depth), slots) in enumerate(
        zip(data.nodes, data.slots, strict=True)
    ):
        state = lean_record(a, b, lean_record(x, y, z))
        birth = "none" if parent < 0 else f"some ({parent}, {position})"
        edges = lean_list(lean_record(target, top, bottom, str(bool(swapped)).lower())
                          for target, top, bottom, swapped in slots)
        nodes.append(lean_record(state, ranks[i], weight, birth, depth, edges))

    marks = []
    for selected, parent, position, x, y, z, outer, local in data.digits:
        marks.append(lean_record(selected, parent, position, outer, local, lean_record(x, y, z)))
    images = lean_list(lean_list(word) for word in data.images)
    row_leaves, row_tree = lookup("rows", "Row", nodes)
    rank_leaves, rank_tree = lookup("byRank", "Nat", order)
    imports = []
    leaves = row_leaves + rank_leaves
    leaves_per_module = SHARD_SIZE // CHUNK_SIZE
    for start in range(0, len(leaves), leaves_per_module):
        module = f"Fixture{f}Leaves{start}"
        imports.append(f"import {module}")
        (output / f"{module}.lean").write_text("\n".join([
            "import Check",
            "noncomputable section",
            f"namespace ArchivedC4.Fixture{f}",
            *leaves[start:start + leaves_per_module],
            f"end ArchivedC4.Fixture{f}",
            "",
        ]))
    return "\n".join([
        *imports,
        "noncomputable section",
        f"namespace ArchivedC4.Fixture{f}",
        f"def marks : List Digit := {lean_list(marks)}",
        f"theorem literalMarks : marks = digits {images} := by decide +kernel",
        row_tree,
        rank_tree,
        f"def acceptedRow := rowOK marks rows byRank {len(data.nodes)} {NUMERATORS[f]}",
        f"end ArchivedC4.Fixture{f}",
        "",
    ])


def emit_checks(f, count, start, stop):
    lines = [
        f"import Fixture{f}Data",
        f"namespace ArchivedC4.Fixture{f}",
        "set_option maxRecDepth 4096",
        "set_option maxHeartbeats 0",
    ]
    for first in range(start, stop, CHUNK_SIZE):
        size = min(CHUNK_SIZE, count - first)
        lines.append(f"theorem chunk{first} : checkChunk {first} {size} acceptedRow = true := "
                     "by decide +kernel")
    names = [f"(fun _i lo hi => row_of_chunk chunk{first} lo hi)"
             for first in range(start, stop, CHUNK_SIZE)]
    lines.extend([
        f"theorem rows{start}Accepted : ∀ i, {start} ≤ i → i < {stop} → acceptedRow i = true :=",
        f"  {join_proofs(names)}",
        f"end ArchivedC4.Fixture{f}", "",
    ])
    return "\n".join(lines)


def join_proofs(names):
    if len(names) == 1:
        return names[0]
    mid = len(names) // 2
    return f"(joinRows {join_proofs(names[:mid])} {join_proofs(names[mid:])})"


def emit_acceptance(f, count, starts):
    imports = [f"import Fixture{f}Rows{start}" for start in starts]
    proof = join_proofs([f"rows{start}Accepted" for start in starts])
    return "\n".join(imports + [
        f"namespace ArchivedC4.Fixture{f}",
        f"theorem allRowsAccepted : ∀ i, 0 ≤ i → i < {count} → acceptedRow i = true :=",
        f"  {proof}",
        f"end ArchivedC4.Fixture{f}",
        "",
    ])


def emit_bridge(f, count):
    return f"""import Geometry
import Fixture{f}Accepted

noncomputable section

namespace ArchivedC4.Fixture{f}

open Psc.ArchivedGraphRefinement Psc.OccurrenceGraphBinding
open Psc.OccurrenceInverse (iterateImages)
open Psc.NamedStableChart (substitution)

def certificate : PscVerif.OverlapContraction.Certificate {count} :=
  toCertificate rows {NUMERATORS[f]} fun i =>
    (row_checks (allRowsAccepted i (Nat.zero_le _) i.isLt)).2.1

theorem certificateCheck : certificate.check = true :=
  certificateAccepted allRowsAccepted

def rootID (i : Fin 3) : Fin {count} := ⟨i.val, by omega⟩

theorem rootBound (i : Fin 3) :
    statesOf rows (rootID i) = Psc.ArchivedGraphRefinement.archivedRoot i := by
  rw [← rootGeometry i]
  apply congrArg Packet.toGeometry
  fin_cases i <;> decide +kernel

theorem discovery
    (table : TableBinding (iterateImages (substitution {f}) 2) (statesOf rows) certificate) :
    TableDiscovery table.row ArchivedRoot :=
  importedDiscovery allRowsAccepted table fun i hi => rootBound ⟨i.val, hi⟩

#print axioms allRowsAccepted
#print axioms certificateCheck
#print axioms rootBound
#print axioms discovery
#print axioms conditionalNullity

end ArchivedC4.Fixture{f}
"""


def emit_controls(f, data):
    populated = next(i for i, slots in enumerate(data.slots) if slots)
    controls = [
        ("missingEdge", populated, "slots := row.slots.drop 1"),
        ("duplicatePosition", populated, "slots := row.slots.take 1 ++ row.slots"),
        ("swappedIdentity", populated, "state := row.state.swap"),
        ("alteredRoot", 0, "state := ⟨0, 2, ⟨0, 0, 0⟩⟩"),
        ("missingAncestry", 3, "birth := none"),
        ("corruptPotential", 0, "weight := 0"),
    ]
    lines = [f"import Fixture{f}Data", f"namespace ArchivedC4.Fixture{f}",
             "set_option maxRecDepth 4096", "set_option maxHeartbeats 0"]
    for name, i, update in controls:
        lines.extend([
            f"theorem {name} :",
            f"    rowOK marks (fun j => (rows j).map fun row =>",
            f"      if j = {i} then {{ row with {update} }} else row) byRank",
            f"      {len(data.nodes)} {NUMERATORS[f]} {i} = false := by decide +kernel",
        ])
    return "\n".join(lines + [f"end ArchivedC4.Fixture{f}", ""])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native_packet", type=Path)
    parser.add_argument("output_directory", type=Path)
    args = parser.parse_args()
    packet = args.native_packet.read_bytes()
    fixtures = authenticate(packet)
    altered = packet.replace(b"graph 0 2 16 8 ", b"graph 0 2 16 9 ", 1)
    try:
        authenticate(altered)
    except oracle.InvalidCertificate as exc:
        if str(exc) != "archived addressed payload hash mismatch":
            raise
    else:
        raise oracle.InvalidCertificate("altered payload digest was accepted")
    args.output_directory.mkdir(parents=True, exist_ok=True)
    for f, (data, count) in enumerate(zip(fixtures, COUNTS, strict=True)):
        (args.output_directory / f"Fixture{f}Data.lean").write_text(emit_data(f, data, args.output_directory))
        (args.output_directory / f"Fixture{f}Controls.lean").write_text(emit_controls(f, data))
        (args.output_directory / f"Fixture{f}Bridge.lean").write_text(emit_bridge(f, count))
        starts = range(0, count, SHARD_SIZE)
        for start in starts:
            module = f"Fixture{f}Rows{start}"
            stop = min(count, start + SHARD_SIZE)
            (args.output_directory / f"{module}.lean").write_text(
                emit_checks(f, count, start, stop))
        (args.output_directory / f"Fixture{f}Accepted.lean").write_text(
            emit_acceptance(f, count, starts))


if __name__ == "__main__":
    main()
