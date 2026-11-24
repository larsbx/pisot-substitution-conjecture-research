"""Independent finite replay controls; this is not a universal proof or kernel."""
import argparse
import copy
import importlib
import json
from pathlib import Path
import sys
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--root", type=Path, required=True)
parser.add_argument("--transcript", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()
sys.path.insert(0, str(args.root / "oracles/python"))
E = importlib.import_module("class_a_plus_upper_entry_independent")
rows = [json.loads(line) for line in args.transcript.open()]
lookup = {(r["n"], r["J"], tuple(r["source"])): r for r in rows}
assert len(lookup) == len(rows)
edge_count = 0
for row in rows:
    reverse = lookup[(row["n"], row["J"], E.reverse(row["source"]))]
    assert len(row["steps"]) == len(reverse["steps"])
    assert row["top_prefix"] == reverse["bottom_prefix"]
    assert row["bottom_prefix"] == reverse["top_prefix"]
    for step, other in zip(row["steps"], reverse["steps"]):
        assert tuple(step[0]) == tuple(other[0])[::-1]
        assert E.reverse(step[2]) == tuple(other[2])
        edge_count += 1

offset_controls = []
one_edge_pairs = 0
for n, J in E.PARAMETERS:
    member = E.LiteralMember(n, J)
    source = (E.Y, E.C, 0, 1, 0)
    steps = E.construct(member, source)
    E.verify_path(member, source, steps, steps[-1][-1])
    assert len(steps) == 2
    assert steps[0][0] == (n + 2, 0) and steps[1][0] == (1, 2)
    for i in range(len(member.words[E.Y])):
        for j in range(len(member.words[E.C])):
            child, _, _ = member.step(source, (i, j))
            assert not member.central(child)
            one_edge_pairs += 1
    for coordinate in range(3):
        altered = list(steps)
        target = list(altered[0][2])
        target[coordinate + 2] += 1
        altered[0] = (altered[0][0], altered[0][1], tuple(target))
        try:
            E.verify_path(member, source, altered, steps[-1][-1])
        except ValueError as error:
            assert str(error) == "wrong literal target", str(error)
            offset_controls.append({"n": n, "J": J, "coordinate": coordinate,
                                    "rejection": str(error)})
        else:
            raise AssertionError("altered complete target offset accepted")

record = rows[0]
member = E.LiteralMember(record["n"], record["J"])
source = E.packet(record["source"])
steps = [(tuple(indices), case, E.packet(target))
         for indices, case, target in record["steps"]]
endpoint = steps[-1][-1] if steps else source
P, Q = E.verify_path(member, source, steps, endpoint)
assert (P, Q) == (tuple(record["top_prefix"]), tuple(record["bottom_prefix"]))
prefix_controls = []
with tempfile.TemporaryDirectory(prefix="psc-entry-prefix-controls-") as folder:
    for field in ("top_prefix", "bottom_prefix"):
        for coordinate in range(3):
            altered = copy.deepcopy(record)
            altered[field][coordinate] += 1
            file = Path(folder) / f"{field}-{coordinate}.jsonl"
            file.write_text(json.dumps(altered) + "\n")
            try:
                E.replay_transcripts(file)
            except ValueError as error:
                assert str(error) == "wrong supplied original prefix", str(error)
                prefix_controls.append({"field": field, "coordinate": coordinate,
                                        "rejection": str(error)})
            else:
                raise AssertionError("altered original prefix accepted")

result = {
    "scope": "independent finite exact replay; no universal mathematical verdict",
    "source_records_checked_for_reversal": len(rows),
    "edges_checked_for_reversal": edge_count,
    "reversal_preserves_depth_indices_complete_targets_and_both_prefix_tracks": True,
    "two_edge_control_parameter_members": len(E.PARAMETERS),
    "one_edge_alternatives_exhaustively_rejected": one_edge_pairs,
    "mutated_complete_target_offsets_rejected": len(offset_controls),
    "mutated_original_prefix_coordinates_rejected": len(prefix_controls),
    "offset_controls": offset_controls,
    "prefix_controls": prefix_controls,
}
with args.output.open("x") as output:
    json.dump(result, output, indent=2)
    output.write("\n")
print(json.dumps({key: value for key, value in result.items()
                  if key not in ("offset_controls", "prefix_controls")}, sort_keys=True))
