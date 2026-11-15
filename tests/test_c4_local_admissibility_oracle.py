"""Finite mathematical controls and refusal of altered occurrence evidence."""

from dataclasses import replace
from pathlib import Path
import os
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "oracles/python"))
import c4_local_admissibility as local


EXPECTED = (
    (2, 2, 2, 2, 2, 0, 0, 1, 1, 1, 2, 0),
    (2, 8, 8, 2, 2, 6, 0, 0, 0, 1, 0, 0),
    (2, 8, 8, 0, 0, 8, 0, 0, 0, 0, 0, 0),
    (2, 2, 2, 2, 0, 0, 2, 1, 0, 0, 3, 0),
    (2, 4, 4, 4, 2, 0, 2, 1, 0, 1, 3, 0),
    (6, 6, 4, 2, 2, 2, 0, 1, 1, 1, 2, 2),
)


@pytest.mark.parametrize("index", range(6))
def test_full_raw_pairs_keep_three_different_cover_contracts(index):
    value = local.reference(index)
    assert value.summary() == EXPECTED[index]
    assert all(row[1] == row[2] for row in value.rows)
    assert len({(p[0], p[1], p[2]) for p in value.pairs}) == len(value.pairs)
    assert all(row[15] == row[16] for row in value.rows)
    # A literal pair's nonintegral flag prevents zero sentinels being read as a lift.
    assert all(p[9:13] == (0, 0, 0, 0) and p[16:19] == (0, 0, 0)
               for p in value.pairs if not p[6])


def test_local_lifting_can_hold_despite_explicit_global_reflection_failure():
    value = local.reference(0)
    e0 = value.basis[0]
    assert e0 == (1, 0, 0, 0, 0, 0, 0, 0, 0)
    # A(0)=star(e0)=0, but diag(2,1,1)*y=e0 has no integral solution.
    assert local.inverse_integer(value.matrix, (1, 0, 0)) is None
    assert value.summary()[7:10] == (1, 1, 1)


def test_nonintegral_nonempty_pairs_can_be_redundant_without_being_deleted():
    value = local.reference(1)
    for source in range(2):
        pairs = tuple(p for p in value.pairs if p[0] == source)
        assert len(pairs) == 4 and sum(p[6] for p in pairs) == 1
        assert {p[15] for p in pairs} == {7}
        assert value.rows[source][13:17] == (0, 0, 1, 1)
        assert value.rows[source][18] == 3


def test_omitted_integral_only_condition_is_vacuous_when_cover_actually_fails():
    value = local.reference(2)
    assert all(not p[6] for p in value.pairs)
    assert all(not p[6] or p[12] for p in value.pairs)  # Vague stronger claim passes vacuously.
    assert all(row[1:5] == (7, 7, 0, 0) for row in value.rows)
    assert all(row[13:17] == (0, 0, 0, 0) for row in value.rows)


def test_integral_lifting_does_not_supply_finite_domain_representation():
    value = local.reference(3)
    assert all(row[13:16] == (1, 0, 0) for row in value.rows)
    assert value.pairs[0][7:12] == (2, 0, 0, 0, 0)
    assert all(p[15] and not p[12] for p in value.pairs)


def test_nonempty_outside_integral_piece_need_not_be_necessary_for_set_cover():
    value = local.reference(4)
    assert all(row[13:17] == (1, 0, 1, 1) for row in value.rows)
    assert all(row[12] == row[18] == 1 for row in value.rows)


def test_equal_ancestor_and_equal_set_do_not_identify_two_actual_occurrences():
    model = local.fixture(1)
    root = ((0, 0, 0, 0, 0),)
    value = local.construct(replace(model, sources=root, domain=root))
    retained = tuple(p for p in value.pairs if p[12])
    assert len(retained) == 2
    assert {p[7:12] for p in retained} == {(0, 0, 0, 0, 0)}
    assert {p[18] for p in retained} == {7}
    assert {(p[1], p[2]) for p in retained} == {(0, 0), (1, 1)}
    assert value.rows[0][17] == 1


def test_profile_exclusion_is_sound_only_on_checked_enclosed_pieces():
    value = local.reference(5)
    assert all(p[15] == p[21] == 0 and not p[6] for p in value.pairs[:2])
    assert value.summary()[7:10] == (1, 1, 1)
    # Two queried packets outside S show why this cannot be promoted to all sources.
    assert all(row[0] == 0 and row[11] == 1 and row[13] == 0 for row in value.rows[-2:])
    assert all(p[15] != 0 and p[21] != 0 and not p[6] for p in value.pairs[-2:])
    # A valid coarse enclosure is inconclusive even where the actual pair is empty.
    coarse = replace(value.model, profiles=(frozenset(range(3)),)*3)
    enlarged = local.construct(coarse)
    assert enlarged.summary()[7:10] == (1, 1, 1)
    assert all(p[15] == 0 and p[21] != 0 for p in enlarged.pairs[:2])
    assert enlarged.summary()[-1] == 0


def test_singular_incidence_requires_some_lift_and_all_lifts_to_stay_distinct():
    model, lifts, summary = local.singular_control()
    assert summary == (1, 2, 1)
    assert lifts[0][-2:] == (7, 1) and lifts[1][-2:] == (7, 0)
    assert lifts[0][2:5] != lifts[1][2:5]
    assert lifts[0][5:8] == lifts[1][5:8] == (0, 0, 0)
    with pytest.raises(local.InvalidCertificate, match="singular"):
        local.construct(model)


def test_mandatory_inverse_closed_domain_still_has_positive_physical_forward_exit():
    assert local.forward_leak() == (4, 2, 2)
    value = local.reference(1)
    assert all(p[12] for p in value.pairs if p[6])
    assert (0, 1, 1, -1, 0) not in value.model.domain
    assert sum((1, -1, 0)) == 0  # Positive physical length 1, not compact measure.


@pytest.mark.parametrize("mutation,match", (
    ("tile", "tile equation"), ("commutation", "does not commute"),
    ("injectivity", "not injective"), ("enclosure", "enclosure"),
    ("quotient", "not additive"), ("modulus", "modulus"),
    ("source", "duplicate sources"), ("domain", "duplicate domain"),
    ("unchecked", "lacks checked source"), ("coordinate", "coordinate budget"),
    ("letter", "literal images"), ("word", "literal images"),
    ("star", "normalized star"), ("tile_point", "tile outside"),
))
def test_false_geometric_model_premises_cannot_be_certified(mutation, match):
    model = local.fixture(0)
    if mutation == "tile":
        model = replace(local.fixture(3), tiles=(frozenset(),) + model.tiles[1:])
    elif mutation == "commutation":
        model = replace(model, star=(1, 1, 1))
    elif mutation == "injectivity":
        model = replace(model, action=0)
    elif mutation == "enclosure":
        model = replace(local.fixture(5), profiles=(frozenset((0,)), frozenset(), frozenset((2,))))
    elif mutation == "quotient":
        model = replace(model, profile_modulus=2)
    elif mutation == "modulus":
        model = replace(model, modulus=16)
    elif mutation == "source":
        model = replace(model, sources=model.sources + model.sources[:1])
    elif mutation == "domain":
        model = replace(model, domain=model.domain + model.domain[:1])
    elif mutation == "unchecked":
        model = replace(model, domain=((0, 0, 0, 0, 0),))
    elif mutation == "coordinate":
        model = replace(model, sources=((1, 2, 65, 0, 0),), domain=())
    elif mutation == "letter":
        model = replace(model, words=((3,), (1,), (2,)))
    elif mutation == "word":
        model = replace(model, words=((0,)*28, (1,), (2,)))
    elif mutation == "star":
        model = replace(model, star=(3, 1, 1))
    else:
        model = replace(model, tiles=(frozenset((3,)),) + model.tiles[1:])
    with pytest.raises(local.InvalidCertificate, match=match):
        local.construct(model)


@pytest.mark.parametrize("cap", (0, 1, 200001))
def test_budget_exhaustion_is_refusal_not_geometric_exclusion(cap):
    with pytest.raises(local.InvalidCertificate, match="budget"):
        local.construct(local.fixture(1), candidate_cap=cap)


@pytest.mark.parametrize("words", (
    ((0,), (0,)*25+(1,), (1,)*26+(2,)),
    ((0,), (0,)*6+(1,), (1,)*4+(0,)+(1,)*4+(2,)),
))
def test_basis_probe_bounds_apply_to_full_candidate_rows_not_only_declared_sources(words):
    model = local.fixture(0)
    roots = ((0, 0, 0, 0, 0),)
    model = replace(model, words=words,
                    sources=roots, domain=roots, star=(0, 0, 0))
    # The first e2 solution is (650,-26,1). In the second model every
    # individual basis solution is in bounds, but another actual e2 probe
    # pair has rhs=e2-4e1 and solution (71,-12,1). Both must refuse.
    with pytest.raises(local.InvalidCertificate, match="coordinate budget"):
        local.construct(model)


@pytest.mark.parametrize("mutation", (
    "drop_pair", "duplicate_pair", "nonintegral_pair", "prefix", "rhs", "ancestor",
    "piece", "profile", "union", "basis", "input", "singular", "forward", "extra", "summary",
))
def test_entire_packet_rejects_incomplete_or_substituted_evidence(mutation):
    lines = local.expected_packet().splitlines()
    victim = next(i for i, line in enumerate(lines) if line.startswith("pair 1 1 "))
    if mutation == "drop_pair":
        del lines[victim]
    elif mutation == "duplicate_pair":
        lines[victim] = lines[victim-1]
    elif mutation == "nonintegral_pair":
        # This deletes an empty-lift record, not an integer ancestor record.
        assert lines[victim].split()[3+6] == "0"
        del lines[victim]
    elif mutation in ("rhs", "ancestor", "piece", "profile"):
        fields = lines[victim].split()
        field = {"rhs": 3, "ancestor": 9, "piece": 15, "profile": 21}[mutation]
        fields[3+field] = str(int(fields[3+field])+1)
        lines[victim] = " ".join(fields)
    elif mutation == "extra":
        lines.insert(-1, "control undeclared 1")
    else:
        prefix = {"prefix": "digit 1 1 ", "union": "row 2 0 ", "basis": "basis 0 0 ",
                  "input": "tiles 5 ", "singular": "singular_lift 6 1 ",
                  "forward": "control forward_leak ", "summary": "summary 0 "}[mutation]
        i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
        fields = lines[i].split()
        fields[-1] = str(int(fields[-1])+1)
        lines[i] = " ".join(fields)
    with pytest.raises(local.InvalidCertificate, match="inventory differs"):
        local.validate_native("\n".join(lines)+"\n")


def test_complete_native_packet_is_required_for_native_replay_credit():
    native = os.environ.get("PSC_LOCAL_ADMISSIBILITY_NATIVE_OUTPUT")
    if native is None:
        pytest.skip("canonical native packet not supplied; no native replay credited")
    result = local.validate_native(Path(native).read_text())
    assert len(result["models"]) == 6 and result["singular_control"] == [1, 2, 1]
    assert result["no_governed_claim_promoted"]


def test_oracle_rejection_remains_active_under_python_optimization(tmp_path):
    packet = tmp_path / "altered.txt"
    packet.write_text(local.expected_packet().replace("summary 0 2 2", "summary 0 1 2"))
    result = subprocess.run([sys.executable, "-O", str(ROOT / "oracles/python/c4_local_admissibility.py"),
                             "--native", str(packet)], capture_output=True, text=True)
    assert result.returncode != 0 and "inventory differs" in result.stderr
