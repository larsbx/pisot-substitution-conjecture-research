"""Independent literal binding and controls that preserve false row summaries."""

from dataclasses import FrozenInstanceError, replace
from itertools import islice
from pathlib import Path
import os
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "oracles/python"))
import c4_literal_inverse_binding as binding


EXPECTED_STATES = (3664, 3649, 3667, 3667, 3653, 3667, 3693, 3674, 3643, 3643, 3646, 3649)
EXPECTED_EDGES = (21151, 21164, 21103, 21033, 21186, 21168, 21144, 21203, 20976, 21054, 21095, 21118)


def change_slot(value, row, position, slot):
    rows = list(value.rows)
    slots = list(rows[row])
    slots[position] = slot
    rows[row] = tuple(slots)
    return replace(value, rows=tuple(rows))


def change_birth(value, vertex, birth):
    births = list(value.births)
    births[vertex] = birth
    return replace(value, births=tuple(births))


@pytest.mark.parametrize("source", range(12))
def test_every_source_has_complete_literal_rows_and_ordered_lift(source):
    value = binding.reference(source)
    summary = binding.validate_binding(value)
    assert len(value.digits) == 18
    assert summary["states"] == EXPECTED_STATES[source]
    assert summary["edges"] == EXPECTED_EDGES[source]
    assert summary["ordered_states"] == 2 * EXPECTED_STATES[source]
    assert summary["ordered_edges"] == 2 * EXPECTED_EDGES[source]
    assert summary["nonroot_births"] == EXPECTED_STATES[source] - 3
    assert summary["swapped"] > 0
    assert summary["repeated_target_slots"] > 0
    assert value.states[:3] == binding.ROOTS
    assert all(value.states[i] != binding.swap(value.states[i]) for i in range(len(value.states)))
    assert all(0 <= value.births[i][0] < i for i in range(3, len(value.states)))


def test_literal_iterate_incidence_and_rescanned_prefixes():
    matrix = ((0, 1, 1), (2, 1, 1), (0, 1, 0))
    square = ((2, 2, 1), (2, 4, 3), (2, 1, 1))
    assert binding.matrix_product(matrix, matrix) == square
    for source in range(12):
        value = binding.reference(source)
        assert binding.incidence(value.images) == matrix
        assert binding.incidence(value.words) == square
        assert len({(d.parent, d.position) for d in value.digits}) == 18
        for digit in value.digits:
            word = value.words[digit.parent]
            assert word[digit.position] == digit.selected
            assert digit.prefix == tuple(word[:digit.position].count(c) for c in range(3))


def test_integral_preimages_are_not_rounded_or_coordinate_residues():
    square = binding.incidence(binding.square_words(binding.source_images(0)))
    admitted = rejected = 0
    for x in range(-3, 4):
        for y in range(-3, 4):
            for z in range(-3, 4):
                delta = (x, y, z)
                ancestor = binding.integral_ancestor_offset(delta)
                if ancestor is None:
                    rejected += 1
                else:
                    admitted += 1
                    assert binding.matrix_vector(square, ancestor) == delta
    assert admitted and rejected
    assert binding.integral_ancestor_offset((1, 0, 0)) is None
    assert binding.integral_ancestor_offset((2, 2, 2)) == (1, 0, 0)
    for bad in ((True, 0, 0), (0, 0), (1000001, 0, 0), [0, 0, 0]):
        with pytest.raises(binding.InvalidCertificate):
            binding.integral_ancestor_offset(bad)


def test_full_ordered_edges_reconstruct_the_transpose_without_filters():
    value = binding.reference(0)
    vertices, edges, matrix_entries = binding.check_lifted_edges(value)
    assert vertices == 2 * EXPECTED_STATES[0]
    assert edges == 2 * EXPECTED_EDGES[0]
    assert matrix_entries < EXPECTED_EDGES[0]  # repeated targets really occur


def test_normalization_retains_the_translation_correction_for_each_actual_slot():
    value = binding.reference(0)
    matrix = binding.incidence(value.words)
    nonzero_corrections = 0
    for source, row in enumerate(value.rows):
        packet = value.states[source]
        for slot in row:
            stored = value.states[slot.target]
            raw = binding.swap(stored) if slot.swapped else stored
            p, q = value.digits[slot.top], value.digits[slot.bottom]
            linear = binding.matrix_vector(matrix, raw[2:])
            assert tuple(linear[k] + p.prefix[k] - q.prefix[k] for k in range(3)) == packet[2:]
            if slot.swapped:
                corrected = tuple(packet[2+k] + q.prefix[k] for k in range(3))
                assert corrected == tuple(p.prefix[k] + linear[k] for k in range(3))
                nonzero_corrections += corrected != p.prefix
    assert nonzero_corrections > 0  # the stored target cannot always keep P


def test_duplicate_occurrence_with_same_target_preserves_counts_but_is_refused():
    value = binding.reference(0)
    victim = None
    for row_id, row in enumerate(value.rows):
        for i, slot in enumerate(row):
            j = next((j for j in range(i) if row[j].target == slot.target), None)
            if j is not None:
                victim = row_id, i, j
                break
        if victim is not None:
            break
    assert victim is not None
    row_id, i, j = victim
    altered = change_slot(value, row_id, i, value.rows[row_id][j])
    assert altered.rows[row_id][i] != value.rows[row_id][i]
    assert [x.target for x in altered.rows[row_id]] == [x.target for x in value.rows[row_id]]
    with pytest.raises(binding.InvalidCertificate, match="slot identity"):
        binding.validate_binding(altered)
    with pytest.raises(binding.InvalidCertificate, match="duplicate ordered positional"):
        binding.check_lifted_edges(altered)


def test_missing_occurrence_cannot_hide_in_the_same_quotient_graph():
    value = binding.reference(0)
    row_id = next(i for i, row in enumerate(value.rows) if len(row) > 1)
    rows = list(value.rows)
    rows[row_id] = rows[row_id][:-1]
    with pytest.raises(binding.InvalidCertificate, match="slot identity"):
        binding.validate_binding(replace(value, rows=tuple(rows)))


@pytest.mark.parametrize("mutation", ("orientation", "indices", "top", "bottom", "target", "bool"))
def test_slot_mutations_refuse_even_when_all_indices_remain_in_range(mutation):
    value = binding.reference(0)
    row_id, position = next((r, i) for r, row in enumerate(value.rows)
                            for i, slot in enumerate(row) if slot.swapped and slot.top != slot.bottom)
    slot = value.rows[row_id][position]
    if mutation == "orientation":
        altered = replace(slot, swapped=0)
    elif mutation == "indices":
        altered = replace(slot, top=slot.bottom, bottom=slot.top)
    elif mutation == "top":
        altered = replace(slot, top=(slot.top+1) % 18)
    elif mutation == "bottom":
        altered = replace(slot, bottom=(slot.bottom+1) % 18)
    elif mutation == "target":
        altered = replace(slot, target=(slot.target+1) % len(value.states))
    else:
        altered = replace(slot, swapped=True)
    with pytest.raises(binding.InvalidCertificate):
        binding.validate_binding(change_slot(value, row_id, position, altered))


@pytest.mark.parametrize("mutation", ("prefix", "position", "letter", "parent", "duplicate", "omit"))
def test_literal_digit_mutations_refuse(mutation):
    value = binding.reference(0)
    digits = list(value.digits)
    original = digits[1]
    if mutation == "prefix":
        digits[1] = replace(original, prefix=(original.prefix[0]+1, *original.prefix[1:]))
    elif mutation == "position":
        digits[1] = replace(original, position=original.position+1)
    elif mutation == "letter":
        digits[1] = replace(original, selected=(original.selected+1) % 3)
    elif mutation == "parent":
        digits[1] = replace(original, parent=(original.parent+1) % 3)
    elif mutation == "duplicate":
        digits[1] = digits[0]
    else:
        digits.pop()
    with pytest.raises(binding.InvalidCertificate, match="digit"):
        binding.validate_binding(replace(value, digits=tuple(digits)))


def test_discovery_requires_actual_earlier_occurrence_and_all_vertices():
    value = binding.reference(0)
    for vertex, birth in ((3, (3, 0)), (3, (-1, -1)), (0, (0, 0)),
                          (3, (0, len(value.rows[0]))), (3, (True, 0))):
        with pytest.raises(binding.InvalidCertificate, match="birth"):
            binding.validate_binding(change_birth(value, vertex, birth))
    victim = next(i for i in range(3, len(value.states)) if value.births[i][0] > 0)
    with pytest.raises(binding.InvalidCertificate, match="birth"):
        binding.validate_binding(change_birth(value, victim, (0, 0)))
    with pytest.raises(binding.InvalidCertificate, match="birth inventory"):
        binding.validate_binding(replace(value, births=value.births[:-1]))


def test_forged_source_state_word_and_order_refuse():
    value = binding.reference(0)
    for source in (-1, 12, True):
        with pytest.raises(binding.InvalidCertificate, match="source"):
            binding.validate_binding(replace(value, source=source))
    altered_states = list(value.states)
    altered_states[1] = altered_states[0]
    with pytest.raises(binding.InvalidCertificate, match="state inventory"):
        binding.validate_binding(replace(value, states=tuple(altered_states)))
    altered_states = list(value.states)
    altered_states[3] = binding.swap(altered_states[3])
    with pytest.raises(binding.InvalidCertificate, match="state inventory"):
        binding.validate_binding(replace(value, states=tuple(altered_states)))
    for field in ("images", "words"):
        values = list(getattr(value, field))
        values[1] = tuple(reversed(values[1]))
        if tuple(values) == getattr(value, field):
            values[1] = (0,)
        with pytest.raises(binding.InvalidCertificate, match="word mismatch"):
            binding.validate_binding(replace(value, **{field: tuple(values)}))


def test_cached_reference_and_historical_snapshots_are_immutable():
    value = binding.reference(0)
    with pytest.raises(FrozenInstanceError):
        value.source = 1
    with pytest.raises(TypeError):
        value.rows[0][0] = value.rows[0][1]
    states, rows = binding.historical_snapshot(0)
    with pytest.raises(TypeError):
        rows[0][0] = 999
    with pytest.raises(TypeError):
        states[0][0] = 2
    assert binding.reference(0) is value
    assert binding.validate_binding(value)["edges"] == EXPECTED_EDGES[0]


@pytest.mark.parametrize("preamble", ("", "schema wrong\n", "schema "+binding.SCHEMA+"\n"))
def test_empty_wrong_or_truncated_packets_refuse(preamble):
    with pytest.raises(binding.InvalidCertificate):
        binding.verify_native(preamble)


def test_packet_record_identity_is_compared_before_summary_acceptance():
    prefix = tuple(islice(binding.packet_lines(), 3))
    assert prefix[1].startswith("source 0 ")
    for records in ((prefix[0], prefix[1]+" 0", prefix[2]),
                    (prefix[0], prefix[1], prefix[1], prefix[2]),
                    (prefix[0], "source 1 3664 21151", prefix[2]),
                    (prefix[0], prefix[1], "image 0 0 2 1 0")):
        with pytest.raises(binding.InvalidCertificate, match="record"):
            binding.verify_native_lines(iter(records))


def test_true_occurrences_do_not_authorize_a_counterfeit_summary():
    records = ["schema " + binding.SCHEMA, *binding.source_lines(binding.reference(0))]
    fields = records[-1].split()
    assert fields[0] == "summary"
    fields[5] = str(int(fields[5]) + 1)  # repeated-target count only
    records[-1] = " ".join(fields)
    with pytest.raises(binding.InvalidCertificate, match="native packet mismatch"):
        binding.verify_native_lines(iter(records))


def test_optimized_python_cannot_accept_forged_literal_data():
    script = """
import c4_literal_inverse_binding as b
try:
    b.integral_ancestor_offset((True,0,0))
except b.InvalidCertificate:
    print('rejected')
else:
    raise SystemExit('optimized acceptance bypass')
"""
    env = os.environ.copy()
    env["PYTHONPATH"] = str(ROOT / "oracles/python")
    result = subprocess.run([sys.executable, "-O", "-c", script], env=env,
                            check=False, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "rejected"


def test_complete_native_packet_when_requested():
    path = os.environ.get("PSC_LITERAL_INVERSE_NATIVE_OUTPUT")
    if not path:
        pytest.skip("canonical native packet supplied by dedicated workflow")
    with Path(path).open(encoding="ascii") as stream:
        result = binding.verify_native_lines(stream)
    assert result["total_states"] == 43915
    assert result["total_edges"] == 253395
    assert result["total_ordered_states"] == 87830
    assert result["total_ordered_edges"] == 506790
    assert result["total_nonroot_births"] == 43879
