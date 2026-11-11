"""Independent full-quotient, literal-profile and packet-tampering controls."""

from dataclasses import replace
from pathlib import Path
import os
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "oracles/python"))
import c4_madic_residue as residue


SUMMARIES = (
    ((1, 3, 3, 3, 1, 1, 0), (2, 6, 7, 4, 2, 1, 0), (4, 12, 15, 6, 2, 2, 2),
     (8, 24, 35, 10, 2, 4, 9), (16, 48, 79, 19, 2, 8, 29)),
    ((1, 3, 3, 3, 1, 1, 0), (2, 6, 7, 5, 2, 1, 0), (4, 12, 15, 9, 2, 2, 1),
     (8, 24, 35, 18, 2, 4, 2), (16, 48, 79, 36, 2, 8, 10)),
    ((1, 3, 3, 3, 1, 1, 0), (1, 3, 5, 3, 1, 1, 0),
     (1, 3, 9, 3, 1, 1, 2), (1, 3, 17, 3, 1, 1, 8)),
    ((1, 3, 3, 3, 1, 1, 0), (8, 24, 6, 6, 8, 1, 0), (64, 192, 12, 12, 8, 8, 0)),
)


@pytest.mark.parametrize("fixture", range(4))
def test_complete_exact_quotient_and_literal_inventory(fixture):
    certificate = residue.reference(fixture)
    residue.validate_certificate(certificate)
    assert tuple(level.summary() for level in certificate.levels) == SUMMARIES[fixture]
    for level in certificate.levels:
        assert len({row[3:6] for row in level.representatives}) == level.index
        assert level.index == abs(residue.determinant(level.matrix))
        assert level.candidates == 3 * level.index
        assert len(level.occurrences) == sum(map(len, level.words))
        addresses = {(row[0], row[1]) for row in level.occurrences}
        assert addresses == {(source, position) for source, word in enumerate(level.words)
                             for position in range(len(word))}
        assert len(addresses) == len(level.occurrences)
        for row in level.occurrences:
            source, position, selected = row[:3]
            word = level.words[source]
            assert selected == word[position]
            assert row[3:6] == residue.parikh(word[:position])
            assert row[6:9] == residue.parikh(word[position + 1:])
            assert row[9] == residue.class_of(level, row[3:6])


def test_named_depth_two_group_has_three_nonzero_involutions():
    level = residue.reference(0).levels[2]
    assert level.matrix == ((1, 3, 1), (1, 3, 3), (1, 1, 1))
    assert level.smith == (1, 2, 2)
    assert level.orders == (1, 2, 2, 2)
    assert level.addition == ((0, 1, 2, 3), (1, 0, 3, 2), (2, 3, 0, 1), (3, 2, 1, 0))
    assert level.action == (0, 2, 0, 2)
    assert level.reduction == (0, 1, 0, 1)
    # The cyclic table has the right cardinality and is itself a valid group,
    # but is not the group represented by the actual matrix lattice.
    cyclic = tuple(tuple((i + j) % 4 for j in range(4)) for i in range(4))
    assert cyclic[1][1] != level.addition[1][1]
    certificate = residue.reference(0)
    altered = replace(certificate, levels=certificate.levels[:2] +
                      (replace(level, addition=cyclic),) + certificate.levels[3:])
    with pytest.raises(residue.InvalidCertificate, match="inventory changed"):
        residue.validate_certificate(altered)


@pytest.mark.parametrize("fixture", range(4))
def test_actual_reductions_and_noninjective_actions(fixture):
    certificate = residue.reference(fixture)
    for level in certificate.levels:
        for identity, representative in enumerate(level.representatives):
            assert level.action[identity] == residue.class_of(
                level, residue.mv(certificate.matrix, representative[:3]))
            value = identity
            for _ in range(level.depth):
                value = level.action[value]
            assert value == 0
            if level.depth:
                previous = certificate.levels[level.depth - 1]
                assert level.reduction[identity] == residue.class_of(previous, representative[:3])
                assert level.reduction[level.action[identity]] == previous.action[level.reduction[identity]]
        if level.depth:
            assert set(level.reduction) == set(range(previous.index))
    # Injectivity is a separate inverse-limit theorem with integral injectivity.
    if fixture == 0:
        assert certificate.levels[2].action[0] == certificate.levels[2].action[2] == 0


def test_repeated_residue_buckets_do_not_identify_literal_occurrences():
    level = residue.reference(0).levels[2]
    assert level.counts[6] == (1, 2, 1, 2, 2)
    assert level.occurrences[6] == (1, 3, 1, 2, 1, 0, 1, 1, 1, 2)
    assert level.occurrences[9] == (1, 6, 1, 3, 2, 1, 0, 0, 0, 2)
    assert level.occurrences[6][9] == level.occurrences[9][9]
    assert level.occurrences[6][1] != level.occurrences[9][1]
    assert len(level.occurrences) == 15
    assert len({(m[0], m[2], m[9]) for m in level.occurrences}) == 13


def test_reordering_equal_incidence_changes_complete_support_profiles():
    first, second = (residue.reference(i).levels[2] for i in (0, 1))
    assert first.matrix == second.matrix and first.addition == second.addition
    assert first.counts[0] == (0, 0, 1, 1, 1)
    assert second.counts[0] == (0, 0, 1, 0, 1)
    assert first.profiles != second.profiles
    assert tuple(map(len, first.words)) == tuple(map(len, second.words))


def test_projected_set_exclusion_and_inconclusive_intersection():
    level = residue.reference(0).levels[2]
    assert level.profiles == ((0, 2, 3), (0, 2), (1,))
    assert residue.profile_intersection(level, 2, 2, (1, 0, 0)) == ()
    assert residue.profile_intersection(level, 2, 2, (0, 0, 0)) == (1,)
    # No actual compact tiles are supplied to this finite test.  The first
    # result becomes a geometric exclusion only after the Lean enclosure;
    # the second result does not assert an actual positive overlap.


def test_non_two_torsion_profile_query_pins_positive_overlap_translation():
    level = residue.reference(0).levels[3]
    assert level.orders[residue.class_of(level, (1, 0, 0))] == 4
    assert residue.profile_intersection(level, 0, 0, (1, 0, 0)) == (3,)
    assert residue.profile_intersection(level, 0, 0, (-1, 0, 0)) == (2,)
    # Preserve the +e0 label and cardinality but substitute the -e0 result.
    text = _change_line(residue.expected_packet(), "profile_query 0 3 0 0 1 0 0 ",
                        lambda _: "profile_query 0 3 0 0 1 0 0 1 2\n")
    with pytest.raises(residue.InvalidCertificate, match="inventory differs"):
        residue.validate_native(text)


def test_actual_column_lattice_differs_from_row_lattice():
    certificate = residue.reference(0)
    vector = (5, 7, 3)
    lattice = certificate.levels[4].matrix
    transposed = tuple(zip(*lattice))
    assert residue.inverse_integer(lattice, vector) == (1, 0, 0)
    assert residue.inverse_integer(transposed, vector) is None
    assert residue.class_of(certificate.levels[4], vector) == 0


def test_finite_zero_residue_does_not_mean_zero_displacement_or_all_level_zero():
    doubled = residue.reference(3)
    assert doubled.levels[2].smith == (4, 4, 4)
    vector = (2, 0, 0)
    assert vector != residue.ZERO
    assert residue.class_of(doubled.levels[1], vector) == 0
    assert residue.class_of(doubled.levels[2], vector) == 4
    assert doubled.levels[2].reduction[4] == 0


def test_unimodular_action_has_no_residue_exclusion_power():
    unit = residue.reference(2)
    assert unit.determinant == 1
    for level in unit.levels:
        assert level.index == 1 and level.smith == (1, 1, 1)
        assert residue.class_of(level, (1, 0, 0)) == 0
        assert residue.profile_intersection(level, 0, 2, (1, 0, 0)) == (0,)


@pytest.mark.parametrize("words,determinant", (
    (((1,), (0,), (2,)), -1),
    (((1, 1), (0, 0), (2, 2)), -8),
))
def test_negative_determinants_preserve_absolute_column_index(words, determinant):
    certificate = residue.construct(words, 2)
    assert certificate.determinant == determinant
    assert certificate.levels[1].determinant == determinant
    assert certificate.levels[1].index == abs(determinant)
    assert certificate.levels[2].index == determinant ** 2


@pytest.mark.parametrize("control", range(8))
def test_recorded_negative_constructions_refuse(control):
    residue.refusal(control)


def test_full_basis_probe_budget_applies_after_all_classes_are_discovered():
    words = residue.FIXTURES[0][0]
    complete = residue.construct(words, 2, candidate_cap=12)
    assert complete.levels[2].candidates == 12
    # The root has already discovered all four classes after three probes.
    assert tuple(row[6:] for row in complete.levels[2].representatives[1:]) == ((0, 0), (0, 1), (0, 2))
    with pytest.raises(residue.InvalidCertificate, match="candidate budget"):
        residue.construct(words, 2, candidate_cap=11)
    with pytest.raises(residue.InvalidCertificate, match="candidate budget"):
        residue.construct(words, 0, candidate_cap=2)
    maximal = residue.construct(words, 6)
    assert maximal.levels[6].index == 64 and maximal.levels[6].candidates == 192


@pytest.mark.parametrize("images,depth,kwargs", (
    (((0,), (1,)), 1, {}),
    (((0,), (), (2,)), 1, {}),
    (((0,), (1,), (3,)), 1, {}),
    (((0, 0, 0, 0), (1,), (2,)), 1, {}),
    (((False,), (1,), (2,)), 1, {}),
    (residue.FIXTURES[0][0], -1, {}),
    (residue.FIXTURES[0][0], True, {}),
    (residue.FIXTURES[0][0], 1, {"index_cap": 0}),
    (residue.FIXTURES[0][0], 1, {"index_cap": 65}),
    (residue.FIXTURES[0][0], 1, {"candidate_cap": 0}),
    (residue.FIXTURES[0][0], 1, {"candidate_cap": 193}),
    (residue.FIXTURES[0][0], 1, {"word_cap": 0}),
    (residue.FIXTURES[0][0], 1, {"word_cap": 730}),
    (residue.FIXTURES[0][0], 1, {"occurrence_cap": 0}),
    (residue.FIXTURES[0][0], 1, {"occurrence_cap": 2188}),
    (residue.FIXTURES[0][0], 0, {"occurrence_cap": 2}),
))
def test_invalid_literal_inputs_and_budgets_refuse(images, depth, kwargs):
    with pytest.raises(residue.InvalidCertificate):
        residue.construct(images, depth, **kwargs)


def test_mandatory_inverse_closed_domain_retains_positive_physical_exit():
    assert residue.forward_leak() == (4, 2, 2)


def _change_line(text, prefix, replacement):
    lines = text.splitlines(keepends=True)
    indices = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    assert len(indices) == 1
    index = indices[0]
    lines[index] = replacement(lines[index])
    return "".join(lines)


@pytest.mark.parametrize("prefix", (
    "power 0 2 ", "adjugate 0 2 ", "smith 0 2 ",
    "representative 0 2 1 ", "add 0 2 1 ", "generators 0 2 ",
    "inverse 0 2 ", "orders 0 2 ", "action 0 2 ", "reduce 0 2 ",
    "word 0 2 1 ", "occurrence 0 2 6 ", "count 0 2 1 2 ",
    "profile 0 2 0 ", "summary 0 2 ", "control forward_leak ",
    "control finite_alias ", "refusal 3 ", "total ",
))
def test_complete_packet_checks_every_record_family(prefix):
    def change(line):
        tokens = line.split()
        tokens[-1] = str(int(tokens[-1]) + 1)
        return " ".join(tokens) + "\n"
    with pytest.raises(residue.InvalidCertificate, match="inventory differs"):
        residue.validate_native(_change_line(residue.expected_packet(), prefix, change))


@pytest.mark.parametrize("mutation", ("omitted", "repeated", "address_alias", "cyclic", "conserved_wrong_class"))
def test_packet_rejects_incomplete_or_aggregate_only_authentication(mutation):
    text = residue.expected_packet()
    if mutation == "omitted":
        text = _change_line(text, "occurrence 0 2 6 ", lambda _: "")
    elif mutation == "repeated":
        text = _change_line(text, "occurrence 0 2 6 ", lambda line: line + line)
    elif mutation == "address_alias":
        text = _change_line(text, "occurrence 0 2 6 ",
                            lambda _: "occurrence 0 2 6 1 6 1 3 2 1 0 0 0 2\n")
    elif mutation == "cyclic":
        for i in range(4):
            text = _change_line(text, f"add 0 2 {i} ",
                                lambda _, i=i: residue.record("add", 0, 2, i,
                                                               *((i + j) % 4 for j in range(4))) + "\n")
    else:
        # Preserve every source/letter total while moving one literal mark's
        # residue count.  Conservation alone would accept this false table.
        text = _change_line(text, "count 0 2 0 0 ", lambda _: "count 0 2 0 0 0 1 1\n")
        text = _change_line(text, "count 0 2 0 1 ", lambda _: "count 0 2 0 1 1 0 0\n")
    with pytest.raises(residue.InvalidCertificate, match="inventory differs"):
        residue.validate_native(text)


def test_certificate_object_rejects_boolean_integer_alias():
    unit = residue.reference(2)
    with pytest.raises(residue.InvalidCertificate, match="inventory changed"):
        residue.validate_certificate(replace(unit, determinant=True))


def test_optimized_packet_verifier_still_rejects_false_action(tmp_path):
    text = _change_line(residue.expected_packet(), "action 0 2 ", lambda _: "action 0 2 0 1 2 3\n")
    path = tmp_path / "false-action.txt"
    path.write_text(text)
    result = subprocess.run(
        [sys.executable, "-O", "-c",
         "import sys; sys.path.insert(0, sys.argv[1]); import c4_madic_residue as r; "
         "r.validate_native(open(sys.argv[2]).read())",
         str(ROOT / "oracles/python"), str(path)], text=True, capture_output=True, check=False)
    assert result.returncode != 0 and "InvalidCertificate" in result.stderr


@pytest.mark.parametrize("mutation", ("no_newline", "extra_line", "spacing"))
def test_packet_framing_is_exact(mutation):
    text = residue.expected_packet()
    if mutation == "no_newline":
        text = text[:-1]
    elif mutation == "extra_line":
        text += "unknown 1\n"
    else:
        text = text.replace("limits ", "limits  ", 1)
    with pytest.raises(residue.InvalidCertificate):
        residue.validate_native(text)


def test_real_native_packet_when_supplied(tmp_path):
    path = os.environ.get("C4_MADIC_RESIDUE_NATIVE")
    if not path:
        pytest.skip("canonical Mojo packet not supplied; oracle-only checks are not native evidence")
    result = residue.validate_native(Path(path).read_text())
    assert result["named_depth_two_smith"] == [1, 2, 2]
    assert result["physical_forward_leak"] == [4, 2, 2]
    assert result["bytes"] == 49431 and result["lines"] == 1341
    receipt = tmp_path / "madic-residue-receipt.json"
    subprocess.run([sys.executable, "-O", str(ROOT / "oracles/python/c4_madic_residue.py"),
                    "--native-output", path, "--output", str(receipt)], check=True,
                   text=True, capture_output=True)
    assert receipt.is_file()
