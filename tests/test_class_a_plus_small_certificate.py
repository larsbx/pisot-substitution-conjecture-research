"""Finite complete plus-S18 certificates and original-prefix refusal controls."""
from copy import deepcopy
from pathlib import Path
import runpy

import pytest

O = runpy.run_path(str(Path(__file__).resolve().parents[1] /
                      "oracles/python/class_a_plus_small_certificate.py"))
EXPECTED = ((306, 1466, 9084, 4, 764), (288, 1744, 13396, 4, 680),
            (280, 2008, 18366, 4, 642), (278, 2338, 24828, 4, 636),
            (276, 2676, 32134, 4, 630))


@pytest.fixture(scope="module")
def packets():
    return [O["make_member"](n, d)[0] for n, d in O["MEMBERS"]]


@pytest.mark.parametrize("index", range(5))
def test_complete_original_small_graph_and_every_prefix(index, packets):
    packet = packets[index]
    summary = O["verify_member"](packet)
    assert tuple(packet["complete"][:5]) == EXPECTED[index]
    assert summary["sources"] == 18
    assert summary["target_policy"] == "typed full integral zero"
    assert len(summary["original_prefix_certificates"]) == summary["vertices"]
    assert sum(p["depth"] for p in summary["original_prefix_certificates"]) == summary["path_edges"]
    for certificate in summary["original_prefix_certificates"]:
        assert certificate["scaled_source"] == [
            p-q for p, q in zip(certificate["top_prefix"], certificate["bottom_prefix"])]
        assert 0 <= certificate["top_ordinal"] < certificate["top_image_length"]
        assert 0 <= certificate["bottom_ordinal"] < certificate["bottom_image_length"]
        assert certificate["terminal_letters"][0] == certificate["terminal_letters"][1]


def test_actual_plus_middle_and_mixed_zero_policy(packets):
    for packet in packets:
        sources = [tuple(v[1:6]) for v in packet["vertices"][:18]]
        assert (2, 2, 0, -1, 0) in sources
        assert (2, 2, 0, 1, 0) in sources
        assert (1, 1, 0, 0, 1) not in sources
        for v, top, bottom, x, c, y, distance, selected, _ in packet["vertices"]:
            if (x, c, y) == (0, 0, 0):
                assert (distance == 0) == (top == bottom)
                assert (selected == -1) == (top == bottom)


@pytest.mark.parametrize("n,d", ((0, 4), (6, 10), (2, 5), (True, 5)))
def test_small_scope_does_not_expand(n, d):
    with pytest.raises(ValueError):
        O["make_member"](n, d)


@pytest.mark.parametrize("kwargs", ({"state_cap": 17}, {"state_cap": 18},
                                     {"pair_cap": 0}, {"pair_cap": 1}))
def test_caps_refuse_incomplete_graphs(kwargs):
    with pytest.raises((ValueError, RuntimeError)):
        O["make_member"](1, 5, **kwargs)


@pytest.mark.parametrize("mutation", (
    "missing_seed", "missing_edge", "duplicate_edge", "full_state", "index",
    "distance", "selected", "path", "empty_path", "truncate", "cap", "nonintegral"))
def test_complete_certificate_mutations_refuse(packets, mutation):
    packet = deepcopy(packets[0])
    if mutation == "missing_seed":
        packet["vertices"].pop(0)
    elif mutation == "missing_edge":
        packet["edges"].pop(0)
    elif mutation == "duplicate_edge":
        packet["edges"].insert(0, packet["edges"][0].copy())
    elif mutation == "full_state":
        packet["vertices"][18][3] += 1
    elif mutation == "index":
        packet["edges"][0][3] += 1
    elif mutation == "distance":
        packet["vertices"][0][6] += 1
    elif mutation == "selected":
        packet["vertices"][0][7] = -1
    elif mutation == "path":
        packet["paths"][0][2] += 1
    elif mutation == "empty_path":
        packet["paths"][0] = [0, 0]
    elif mutation == "truncate":
        packet["paths"].pop()
    elif mutation == "cap":
        packet["complete"][-1] -= 1
    elif mutation == "nonintegral":
        packet["vertices"][0][0] = 0.0
    with pytest.raises(ValueError):
        O["verify_member"](packet)


def transcript(packets):
    lines = []
    for packet in packets:
        member = [packet["n"], packet["d"]]
        for vertex in packet["vertices"]:
            lines.append("PLUS_SMALL_VERTEX " + " ".join(map(str, member+vertex)))
        for edge in packet["edges"]:
            lines.append("PLUS_SMALL_EDGE " + " ".join(map(str, member+edge)))
        for path in packet["paths"]:
            lines.append("PLUS_SMALL_PATH " + " ".join(map(str, member+path)))
        lines.append("PLUS_SMALL_COMPLETE " + " ".join(map(str, member+packet["complete"])))
        lines.append("CLASS_A_PLUS_SMALL_MEMBER_PASS " + " ".join(map(str, member+packet["complete"][:5])))
    counts = [sum(p["complete"][i] for p in packets) for i in (0, 1, 2)]
    total = counts+[counts[0], sum(p["complete"][4] for p in packets),
                    max(p["complete"][3] for p in packets), 12]
    lines += ["CLASS_A_PLUS_FIVE_SMALL_ENTRY_PASS " + " ".join(map(str, total)),
              "contract-receipt: " + O["CONTRACT"]]
    return "\n".join(lines)+"\n"


def test_complete_transcript_accepts_all_records(packets):
    summary = O["verify_native_text"](transcript(packets))
    assert summary["total"] == dict(vertices=1428, indexed_edges=10232,
        occurrence_pairs=97808, paths=1428, path_edges=3352,
        max_distance=4, native_refusals=12)


@pytest.mark.parametrize("mutation", (
    "missing_member", "missing_vertex", "missing_edge", "duplicate_vertex",
    "duplicate_complete", "truncated_path", "wrong_total", "missing_contract",
    "altered_contract", "duplicate_contract", "unknown_output"))
def test_native_transcript_refuses_incomplete_or_altered_receipts(packets, mutation):
    lines = transcript(packets).splitlines()
    if mutation == "missing_member":
        lines = [line for line in lines if not line.startswith(("PLUS_SMALL_VERTEX 1 5 ",
            "PLUS_SMALL_EDGE 1 5 ", "PLUS_SMALL_PATH 1 5 ", "PLUS_SMALL_COMPLETE 1 5 ",
            "CLASS_A_PLUS_SMALL_MEMBER_PASS 1 5 "))]
    elif mutation in ("missing_vertex", "missing_edge"):
        prefix = "PLUS_SMALL_VERTEX " if mutation == "missing_vertex" else "PLUS_SMALL_EDGE "
        lines.pop(next(i for i, line in enumerate(lines) if line.startswith(prefix)))
    elif mutation == "duplicate_vertex":
        lines.insert(0, lines[0])
    elif mutation == "duplicate_complete":
        lines.append(next(line for line in lines if line.startswith("PLUS_SMALL_COMPLETE ")))
    elif mutation == "truncated_path":
        i = next(i for i, line in enumerate(lines) if line.startswith("PLUS_SMALL_PATH "))
        lines[i] = lines[i].rsplit(" ", 1)[0]
    elif mutation == "wrong_total":
        lines[-2] = lines[-2].replace("1428", "1429", 1)
    elif mutation == "missing_contract":
        lines.pop()
    elif mutation == "altered_contract":
        lines[-1] = "contract-receipt: ClassAPlusFiveSmallCompleteS18"
    elif mutation == "duplicate_contract":
        lines.append(lines[-1])
    elif mutation == "unknown_output":
        lines.append("UNDECLARED_RESULT 1 5 0")
    with pytest.raises(ValueError):
        O["verify_native_text"]("\n".join(lines)+"\n")


def test_original_prefix_checker_rejects_changed_actual_occurrence(packets):
    packet = packets[0]
    g = O["SmallGeometry"](1, 5)
    source = tuple(packet["vertices"][0][1:6])
    raw = packet["paths"][0][2:]
    path = [(raw[i], raw[i+1], tuple(packet["vertices"][raw[i+2]][1:6]))
            for i in range(0, len(raw), 3)]
    O["original_prefix_certificate"](g, source, path, typed=True)
    with pytest.raises(ValueError):
        O["original_prefix_certificate"](g, source, [], typed=True)
    with pytest.raises((ValueError, AssertionError)):
        O["original_prefix_certificate"](g, source,
            [(path[0][0]+1, path[0][1], path[0][2]), *path[1:]], typed=True)
