"""Independent finite claims and adversarial incomplete-cover controls."""

from dataclasses import replace
from pathlib import Path
import os
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "oracles/python"))
import c4_bounded_cover as cover


EXPECTED = (
    (8, 24, 18, 0, 2, 2, 0, 2),
    (15, 28, 14, 0, 8, 8, 7, 1),
    (12, 10, 0, 6, 6, 2, 0, 6),
    (128, 558, 432, 122, 114, 0, 30, 92),
)


def oracle_packet():
    lines = ["schema " + cover.SCHEMA, "limits " + " ".join(map(str, cover.LIMITS))]
    for index in range(4):
        lines.extend(cover.core_lines(index, cover.reference(index)))
    for name, values in cover.geometric_controls().items():
        lines.append("control " + name + " " + " ".join(map(str, values)))
    lines.append("total 4 163 620 130")
    return "\n".join(lines) + "\n"


@pytest.mark.parametrize("index", range(4))
def test_full_integer_histories_and_literal_iterated_addresses(index):
    value = cover.reference(index)
    assert value.summary() == EXPECTED[index]
    cover.check_addresses(value)
    assert all(n[1] < i for i, n in enumerate(value.nodes))
    # Every candidate is retained, including failed integral solves and exits.
    assert sum(c[3] != 0 for c in value.candidates) == len(value.nodes) - len(value.roots)


def test_repeated_endpoint_histories_are_eight_distinct_actual_addresses():
    value = cover.reference(1)
    leaves = [(i, n) for i, n in enumerate(value.nodes) if n[2] == 3]
    assert len({n[5:10] for _, n in leaves}) == 1
    assert len({cover.path(value, i) for i, _ in leaves}) == 8
    assert {n[10] for _, n in leaves} == set(range(8))
    assert all(n[10:13] == n[13:16] for _, n in leaves)


def test_nonunit_source_uses_actual_square_words_and_retains_outside_paths():
    value = cover.reference(3)
    assert value.words == ((2, 1, 0, 2, 1, 0), (1, 0, 2, 1, 0, 1, 1), (2, 1, 0, 1, 1))
    assert cover.determinant(value.matrix) == 4
    outside_parents = {i for i, n in enumerate(value.nodes) if not n[16] and n[2] < value.depth}
    assert outside_parents
    assert any(c[0] in outside_parents for c in value.candidates)
    assert any(n[1] in outside_parents for n in value.nodes)
    assert value.summary()[4:6] == (114, 0)  # Full tree vs root-only retained paths.


def test_inverse_closed_leaking_domain_does_not_imply_forward_completeness():
    value = cover.reference(0)
    assert value.summary()[3] == 0  # Complete finite-depth inverse scan stays in S.
    # Unbounded one-step inverse closure follows independently by parity:
    # 2*y=j*e1-i*e0 with i,j in {0,1} forces i=j=0 and y=0.
    for i in range(2):
        for j in range(2):
            y = cover.inverse_integer(value.matrix, (-i, j, 0))
            assert (y is not None) == (i == j == 0)
    child = (0, 1, 1, -1, 0)  # Forward literal positions (1,1).
    assert child not in value.domain
    scalar_offset = sum(child[2:])
    assert max(0, min(1, 1-scalar_offset)-max(0, -scalar_offset)) == 1


def test_exact_inverse_does_not_round_and_supports_negative_determinant():
    matrix = ((0, 2, 0), (1, 0, 0), (0, 0, 1))
    assert cover.determinant(matrix) == -2
    assert cover.inverse_integer(matrix, (2, 3, -1)) == (3, 1, -1)
    assert cover.inverse_integer(matrix, (1, 0, 0)) is None
    with pytest.raises(cover.InvalidCertificate, match="singular"):
        cover.inverse_integer(((0, 0, 0),)*3, (0, 0, 0))


@pytest.mark.parametrize("budget", (
    {"history_cap": 2}, {"candidate_cap": 1}, {"state_cap": 2},
))
def test_resource_exhaustion_cannot_return_a_complete_tree(budget):
    with pytest.raises(cover.InvalidCertificate, match="budget exhausted"):
        cover.construct(*cover.fixture(3), **budget)


def test_zero_depth_cover_keeps_root_and_empty_occurrence_address():
    words, roots, domain, _ = cover.fixture(3)
    value = cover.construct(words, roots, domain, 0)
    assert len(value.nodes) == 2 and not value.candidates
    assert all(cover.path(value, i) == () for i in range(2))


def test_word_budget_includes_unreached_letters_and_rejects_before_expansion():
    words = ((0,), (1,), (2,)*27)
    root = ((0, 0, 0, 0, 0),)
    with pytest.raises(cover.InvalidCertificate, match="word budget exhausted"):
        cover.construct(words, root, root, 6)
    with pytest.raises(cover.InvalidCertificate, match="invalid resource budget"):
        cover.construct(*cover.fixture(0), history_cap=20001)
    with pytest.raises(cover.InvalidCertificate, match="state budget exhausted"):
        cover.construct(words, root, (root[0], (1, 1, 0, 0, 0)), 0, state_cap=1)


def test_forged_circular_history_is_refused_before_address_traversal():
    value = cover.reference(1)
    nodes = list(value.nodes)
    changed = list(nodes[-1])
    changed[1] = len(nodes)-1
    nodes[-1] = tuple(changed)
    with pytest.raises(cover.InvalidCertificate, match="strictly earlier"):
        cover.check_addresses(replace(value, nodes=tuple(nodes)))


def test_compact_group_and_enclosure_countercontrols():
    controls = cover.geometric_controls()
    assert controls["missing_reflection"] == (3, 0, 4)
    assert controls["physical_not_compact"] == (0, 3)
    assert controls["false_enclosure"] == (0, 3)
    assert controls["boundary_contact"] == (1,)
    assert controls["redundant_occurrence"] == (2, 1)
    assert controls["missing_piece"] == (2, 1)


def test_actual_prefix_corruption_is_rejected_despite_equal_endpoint():
    value = cover.reference(1)
    nodes = list(value.nodes)
    changed = list(nodes[-1])
    changed[10] -= 1
    changed[11] += 1  # Same prefix length, wrong literal Parikh address.
    nodes[-1] = tuple(changed)
    with pytest.raises(cover.InvalidCertificate, match="literal iterate"):
        cover.check_addresses(replace(value, nodes=tuple(nodes)))


@pytest.mark.parametrize("mutation", ("drop", "duplicate", "target", "prefix", "candidate", "control", "extra"))
def test_whole_packet_refuses_missing_or_substituted_occurrence_records(mutation):
    lines = oracle_packet().splitlines()
    victim = next(i for i, line in enumerate(lines) if line.startswith("node 1 14 "))
    if mutation == "drop":
        del lines[victim]
    elif mutation == "duplicate":
        lines[victim] = lines[victim-1]
    elif mutation in ("target", "prefix"):
        fields = lines[victim].split()
        field = 3+7 if mutation == "target" else 3+10
        fields[field] = str(int(fields[field])+1)
        lines[victim] = " ".join(fields)
    elif mutation == "candidate":
        i = next(i for i, line in enumerate(lines) if line.startswith("candidate ") and line.endswith(" 0 -1"))
        del lines[i]
    elif mutation == "control":
        i = next(i for i, line in enumerate(lines) if line.startswith("control "))
        del lines[i]
    else:
        lines.insert(-1, "control undeclared 1")
    with pytest.raises(cover.InvalidCertificate):
        cover.validate_native("\n".join(lines)+"\n")


def test_packet_acceptance_requires_complete_native_inventory_when_supplied():
    native = os.environ.get("PSC_BOUNDED_COVER_NATIVE_OUTPUT")
    if native is None:
        pytest.skip("canonical native packet not supplied; no native replay credited")
    result = cover.validate_native(Path(native).read_text())
    assert len(result["fixtures"]) == 4
    assert result["no_governed_claim_promoted"]


def test_public_oracle_rejection_remains_active_under_python_optimization(tmp_path):
    altered = oracle_packet().replace("summary 0 8 24", "summary 0 7 24")
    packet = tmp_path / "bad.txt"
    packet.write_text(altered)
    run = subprocess.run([sys.executable, "-O", str(ROOT / "oracles/python/c4_bounded_cover.py"),
                          "--native", str(packet)], capture_output=True, text=True)
    assert run.returncode != 0
    assert "inventory differs" in run.stderr
