"""Independent literal slices, full-window coverage, and fail-closed packets."""

from dataclasses import replace
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "oracles/python"))
import c4_prefix_closure as prefix


SUMMARIES = (
    ((1, 3, 2, 3, 1, 0, 0, 1, 1, 1),
     (3, 15, 4, 15, 1, 1, 1, 5, 7, 3),
     (15, 79, 16, 79, 5, 7, 3, 29, 35, 15)),
    ((1, 3, 2, 3, 1, 0, 0, 1, 1, 1),
     (3, 15, 4, 15, 1, 1, 1, 5, 7, 3),
     (15, 79, 16, 79, 5, 7, 3, 29, 35, 15)),
    ((1, 2, 2, 2, 1, 0, 0, 1, 1, 0),
     (2, 4, 3, 4, 1, 1, 0, 2, 1, 1),
     (4, 7, 5, 7, 2, 1, 1, 4, 2, 1)),
    ((1, 2, 2, 2, 1, 0, 0, 2, 0, 0),
     (2, 4, 3, 4, 2, 0, 0, 4, 0, 0),
     (4, 8, 5, 8, 4, 0, 0, 8, 0, 0)),
)


@pytest.mark.parametrize("fixture", range(4))
def test_complete_source_output_and_every_full_mark(fixture):
    certificate = prefix.reference(fixture)
    prefix.validate_certificate(certificate)
    assert tuple(prefix.summary(certificate, g) for g in range(3)) == SUMMARIES[fixture]
    assert prefix.bind_windows(certificate.images, certificate.period, certificate.seed,
                               certificate.windows) == certificate
    for identity, mark in enumerate(certificate.marks):
        parent, local, selected = mark[:3]
        before, after = certificate.mark_before[identity], certificate.mark_after[identity]
        assert before + (selected,) + after == certificate.block_images[parent]
        assert len(before) == local
        assert prefix.parikh(before) == mark[3:6]
        assert prefix.parikh(after) == mark[6:9]
    for generation, transition in enumerate(certificate.transitions):
        source, target = certificate.windows[generation:generation + 2]
        assert target == prefix.expand(certificate.block_images, source)
        assert target[:len(source)] == source
        assert len(transition.cuts) == len(source) + 1
        assert transition.cuts[-1][1] == len(target)
        assert {row[4] for row in transition.occurrences} == set(range(len(target)))
        assert {(row[0], row[3]) for row in transition.occurrences} == {
            (parent, local) for parent, letter in enumerate(source)
            for local in range(len(certificate.block_images[letter]))}
        for global_position, row in enumerate(transition.occurrences):
            assert prefix.lookup(certificate, generation, global_position) == row
            parent, letter, mark_id, local, global_index, selected = row[:6]
            assert global_index == global_position and source[parent] == letter
            assert certificate.marks[mark_id][:3] == (letter, local, selected)
            before = prefix.expand(certificate.block_images, source[:parent]) + certificate.mark_before[mark_id]
            after = certificate.mark_after[mark_id] + prefix.expand(certificate.block_images, source[parent + 1:])
            assert target == before + (selected,) + after
            assert target[:global_position] == before
            assert row[6:9] == prefix.parikh(source[:parent])
            assert row[15:18] == prefix.parikh(before)
            assert row[15:18] == tuple(a + b for a, b in zip(row[9:12], row[12:15]))


def test_period_scale_reordered_words_and_productive_seed_scope():
    named, reordered = prefix.reference(0), prefix.reference(1)
    assert named.period == 2
    assert named.block_images == ((0, 2, 1), (1, 0, 0, 1, 0, 2, 1), (1, 1, 0, 2, 1))
    assert named.block_matrix == (1, 3, 1, 1, 3, 3, 1, 1, 1)
    assert named.matrix == reordered.matrix and named.block_matrix == reordered.block_matrix
    assert named.windows[1] != reordered.windows[1]
    assert prefix.parikh(named.windows[1]) == prefix.parikh(reordered.windows[1])
    with pytest.raises(prefix.InvalidCertificate, match="prolonging"):
        prefix.construct(named.images, 1, (0,), 1)
    # A singular matrix does not obstruct a word-level address bijection.
    singular = prefix.construct(((0, 0), (0, 0), (0, 0)), 1, (0,), 3)
    assert singular.windows[3] == (0,) * 8
    longer_seed = prefix.construct(prefix.FIXTURES[2][0], 1, (0, 1), 3)
    assert len(longer_seed.windows[3]) == 13
    # Both identity and the square of a permutation do fix infinite words;
    # they merely do not meet this constructor's strict-growth premise.
    for images, period in ((((0,), (1,), (2,)), 1), (((1,), (0,), (2,)), 2)):
        with pytest.raises(prefix.InvalidCertificate, match="strictly growing"):
            prefix.construct(images, period, (0,), 1)


def test_exact_boundaries_terminal_cut_and_first_omitted_successor():
    named = prefix.reference(0)
    for generation, transition in enumerate(named.transitions):
        for parent, cut in enumerate(transition.cuts[:-1]):
            row = prefix.lookup(named, generation, cut[1])
            assert row[0] == parent and row[3] == 0
        terminal = transition.cuts[-1]
        assert terminal[0] == len(named.windows[generation])
        assert terminal[1] == len(named.windows[generation + 1])
        with pytest.raises(prefix.InvalidCertificate, match="actual output occurrence"):
            prefix.lookup(named, generation, terminal[1])
    first_missing = prefix.lookup(named, 0, len(named.windows[0]))
    assert first_missing[:6] == (0, 0, 1, 1, 1, 2)
    assert named.transitions[2].cuts[-1] == (15, 79, 5, 7, 3, 29, 35, 15)
    with pytest.raises(prefix.InvalidCertificate, match="full consecutive"):
        prefix.bind_windows(named.images, 2, (0,), ((0,), (0,)))


def test_equal_residue_does_not_identify_occurrence_addresses():
    named = prefix.reference(0)
    first, second = prefix.lookup(named, 2, 0), prefix.lookup(named, 2, 29)
    assert second == (5, 0, 0, 0, 29, 0, 1, 3, 1, 11, 13, 5, 0, 0, 0, 11, 13, 5)
    assert first[2] == second[2] and first[5] == second[5]
    assert first[0] != second[0] and first[4] != second[4]
    assert first[15:18] != second[15:18]
    assert prefix.same_residue_control() == (0, 2, 2, 0, 29, 0, 5, 0, 0, 0)
    # The full inventory is larger than the set of local mark IDs; repeating
    # a local Mark at a later parent still contributes an actual occurrence.
    transition = named.transitions[2]
    assert len(transition.occurrences) == 79
    assert len({row[2] for row in transition.occurrences}) == 15


def test_finite_letter_support_and_mandatory_physical_forward_leak():
    doubled = prefix.reference(3)
    assert prefix.parikh(doubled.windows[3]) == (8, 0, 0)
    assert {mark[2] for mark in doubled.marks} == {0, 1, 2}
    assert {row[5] for row in doubled.transitions[2].occurrences} == {0}
    # Original two-state physical calibration, independent of the prefix
    # fixture's letter support.  This is not compact overlap measure.
    assert prefix.forward_leak() == (4, 2, 2)


@pytest.mark.parametrize("control", range(14))
def test_recorded_constructor_refusals(control):
    prefix.refusal(control)


@pytest.mark.parametrize("kwargs", (
    {"images": ((0, 0), (1,))},
    {"images": ((0, 0, 0, 0), (1,), (2,))},
    {"images": ((0, 3), (1,), (2,))},
    {"images": ((False, 0), (1,), (2,))},
    {"seed": (-1,)}, {"seed": (3,)}, {"seed": (0.0,)}, {"seed": (0,) * 33},
    {"period": 0}, {"period": -1}, {"period": True},
    {"generations": 0}, {"generations": -1}, {"generations": 1.0},
    {"word_cap": 0}, {"word_cap": 4097},
    {"occurrence_cap": 0}, {"occurrence_cap": 12289}, {"occurrence_cap": False},
))
def test_malformed_inputs_and_outside_budget_parameters(kwargs):
    arguments = dict(images=prefix.FIXTURES[0][0], period=2, seed=(0,), generations=3)
    arguments.update(kwargs)
    with pytest.raises(prefix.InvalidCertificate):
        prefix.construct(**arguments)


def test_exact_caps_and_skipped_or_changed_whole_windows():
    named = prefix.reference(0)
    exact = prefix.construct(named.images, 2, (0,), 3, word_cap=79, occurrence_cap=97)
    assert exact.windows == named.windows
    for windows in ((), ((0,),), ((0,), named.windows[2]), ((1,), named.windows[1]),
                    ((0,), (0, 1, 2)), ((0,), (0, 2, 1, 0))):
        with pytest.raises(prefix.InvalidCertificate):
            prefix.bind_windows(named.images, 2, (0,), windows)
    for generation, position in ((0, -1), (3, 0), (2, 79), (-1, 0), (True, 0), (0, 0.0)):
        with pytest.raises(prefix.InvalidCertificate):
            prefix.lookup(named, generation, position)


def _change_tuple(value, index, replacement):
    return value[:index] + (replacement,) + value[index + 1:]


@pytest.mark.parametrize("field", range(18))
def test_each_address_field_is_authenticated(field):
    certificate = prefix.reference(0)
    transition = certificate.transitions[2]
    row = transition.occurrences[29]
    changed = _change_tuple(row, field, row[field] + 1)
    altered_transition = replace(transition, occurrences=_change_tuple(transition.occurrences, 29, changed))
    altered = replace(certificate, transitions=_change_tuple(certificate.transitions, 2, altered_transition))
    with pytest.raises(prefix.InvalidCertificate, match="inventory changed"):
        prefix.validate_certificate(altered)


@pytest.mark.parametrize("mutation", (
    "block_word", "local_before", "local_after", "window", "terminal_cut",
    "omitted_occurrence", "repeated_occurrence", "same_residue_alias", "boolean_integer",
))
def test_literal_inventory_mutations_do_not_pass_aggregate_checks(mutation):
    certificate = prefix.reference(0)
    transition = certificate.transitions[2]
    if mutation == "block_word":
        altered = replace(certificate, block_images=_change_tuple(certificate.block_images, 0, (0, 1, 2)))
    elif mutation == "local_before":
        altered = replace(certificate, mark_before=_change_tuple(certificate.mark_before, 6, (0, 1, 0)))
    elif mutation == "local_after":
        altered = replace(certificate, mark_after=_change_tuple(certificate.mark_after, 6, (0, 1, 2)))
    elif mutation == "window":
        altered = replace(certificate, windows=_change_tuple(certificate.windows, 1, (0, 1, 2)))
    elif mutation == "terminal_cut":
        changed = replace(transition, cuts=transition.cuts[:-1])
        altered = replace(certificate, transitions=_change_tuple(certificate.transitions, 2, changed))
    elif mutation in ("omitted_occurrence", "repeated_occurrence", "same_residue_alias"):
        occurrences = transition.occurrences
        if mutation == "omitted_occurrence":
            occurrences = occurrences[:-1]
        elif mutation == "repeated_occurrence":
            occurrences += (occurrences[29],)
        else:
            occurrences = _change_tuple(occurrences, 0, occurrences[29])
        changed = replace(transition, occurrences=occurrences)
        altered = replace(certificate, transitions=_change_tuple(certificate.transitions, 2, changed))
    else:
        altered = replace(certificate, matrix=_change_tuple(certificate.matrix, 0, False))
    with pytest.raises(prefix.InvalidCertificate, match="inventory changed"):
        prefix.validate_certificate(altered)


def _change_line(text, starts, operation):
    lines = text.splitlines(keepends=True)
    matches = [index for index, line in enumerate(lines) if line.startswith(starts)]
    assert len(matches) == 1
    index = matches[0]
    lines[index] = operation(lines[index])
    return "".join(lines)


@pytest.mark.parametrize("starts", (
    "limits ", "fixture 0 ", "image 0 1 ", "incidence 0 ",
    "block_image 0 1 ", "block_incidence 0 ", "seed 0 ", "mark 0 6 ",
    "mark_before 0 6 ", "mark_after 0 6 ", "window 0 2 ", "cut 0 2 15 ",
    "address 0 2 29 ", "summary 0 2 ", "control same_residue ",
    "control truncated_successor ", "control terminal_cut ",
    "control finite_letter_support ", "control forward_leak ", "refusal 9 ", "total ",
))
def test_packet_authenticates_every_record_family(starts):
    def change(line):
        tokens = line.split()
        tokens[-1] = str(int(tokens[-1]) + 1)
        return " ".join(tokens) + "\n"
    with pytest.raises(prefix.InvalidCertificate, match="inventory differs"):
        prefix.validate_native(_change_line(prefix.expected_packet(), starts, change))


@pytest.mark.parametrize("mutation", (
    "omitted", "repeated", "reordered", "same_residue_alias", "same_parikh_word",
    "no_newline", "extra_line", "spacing", "crlf",
))
def test_packet_rejects_missing_repeated_aliased_and_noncanonical_records(mutation):
    text = prefix.expected_packet()
    if mutation == "omitted":
        text = _change_line(text, "address 0 2 29 ", lambda _: "")
    elif mutation == "repeated":
        text = _change_line(text, "address 0 2 29 ", lambda line: line + line)
    elif mutation == "reordered":
        lines = text.splitlines(keepends=True)
        first = next(i for i, line in enumerate(lines) if line.startswith("address 0 2 0 "))
        lines[first], lines[first + 1] = lines[first + 1], lines[first]
        text = "".join(lines)
    elif mutation == "same_residue_alias":
        text = _change_line(text, "address 0 2 0 ", lambda _: prefix.record(
            "address", 0, 2, 0, *prefix.lookup(prefix.reference(0), 2, 29)) + "\n")
    elif mutation == "same_parikh_word":
        text = _change_line(text, "window 0 1 ", lambda _: "window 0 1 2 3 0 1 2\n")
    elif mutation == "no_newline":
        text = text[:-1]
    elif mutation == "extra_line":
        text += "unknown 1\n"
    elif mutation == "spacing":
        text = text.replace("limits ", "limits  ", 1)
    else:
        text = text.replace("\n", "\r\n")
    with pytest.raises(prefix.InvalidCertificate):
        prefix.validate_native(text)


def test_optimized_packet_verifier_rejects_a_truncated_full_window(tmp_path):
    text = _change_line(prefix.expected_packet(), "window 0 1 ", lambda _: "window 0 1 2 1 0\n")
    path = tmp_path / "truncated-window.txt"
    path.write_text(text)
    result = subprocess.run(
        [sys.executable, "-O", "-c",
         "import sys; sys.path.insert(0, sys.argv[1]); import c4_prefix_closure as p; "
         "p.validate_native(open(sys.argv[2]).read())",
         str(ROOT / "oracles/python"), str(path)], text=True, capture_output=True, check=False)
    assert result.returncode != 0 and "InvalidCertificate" in result.stderr


def test_real_native_packet_when_supplied(tmp_path):
    path = os.environ.get("C4_PREFIX_CLOSURE_NATIVE")
    if not path:
        pytest.skip("canonical Mojo packet not supplied; oracle-only checks are not native evidence")
    result = prefix.validate_native(Path(path).read_bytes().decode("utf-8"))
    assert result["same_residue_distinct_addresses"] == [0, 2, 2, 0, 29, 0, 5, 0, 0, 0]
    assert result["physical_forward_leak"] == [4, 2, 2]
    receipt = tmp_path / "prefix-closure-receipt.json"
    subprocess.run([sys.executable, "-O", str(ROOT / "oracles/python/c4_prefix_closure.py"),
                    "--native-output", path, "--output", str(receipt)], check=True,
                   text=True, capture_output=True)
    saved = json.loads(receipt.read_text())
    assert saved["native_sha256"] == result["native_sha256"]
    assert set(saved["sources"]) == set(prefix.SOURCES)
