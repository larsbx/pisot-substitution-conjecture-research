import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import audit_manuscript  # noqa: E402


def write(root: Path, rel: str, text: str) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def test_audit_accepts_current_correct_formulations(tmp_path: Path) -> None:
    write(
        tmp_path,
        "paper.tex",
        """
        The synthetic algebraic solution is $N_C=M_\\sigma^\\top$ with $P=I$.
        The matrix acts on an invariant subspace as a similar copy of $M_\sigma$.
        Then, conditional on the SCC Producer Theorem, the associated tiling
        dynamical system has pure discrete spectrum.
        """,
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


def test_audit_rejects_untransposed_synthetic_countermodel(tmp_path: Path) -> None:
    write(tmp_path, "bad.md", "The synthetic countermodel is N_C = M_sigma with P = I.")
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


def test_audit_rejects_old_cycle_exclusion_target(tmp_path: Path) -> None:
    write(tmp_path, "bad.tex", "We prove there is no recurrent noncoincident cycle.")
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


def test_audit_rejects_unconditional_pds_claim(tmp_path: Path) -> None:
    write(
        tmp_path,
        "bad.tex",
        "Then the associated tiling dynamical system has pure discrete spectrum.",
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


def test_audit_rejects_loose_subblock_language(tmp_path: Path) -> None:
    write(tmp_path, "bad.md", "N_C contains M_sigma as an invariant sub-block.")
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


def test_audit_accepts_parikh_intertwiner(tmp_path: Path) -> None:
    write(
        tmp_path,
        "paper.md",
        "The proved identity is P_C N_C = M_sigma P_C with rank(P_C)=3.",
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


def test_audit_accepts_transpose_guidance_that_quotes_bad_form(tmp_path: Path) -> None:
    write(
        tmp_path,
        "guide.md",
        "No stale N_C = M_sigma synthetic-countermodel language; it must be "
        "N_C = M_sigma^T, P = I.",
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


def test_audit_accepts_historical_cycle_exclusion_rejection(tmp_path: Path) -> None:
    write(
        tmp_path,
        "history.tex",
        'The earlier target "no recurrent noncoincident cycle" is false.',
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


def test_audit_accepts_no_longer_cycle_target_wording(tmp_path: Path) -> None:
    write(
        tmp_path,
        "ledger.md",
        'The target is no longer "there are no recurrent noncoincident cycles".',
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


def test_audit_rejects_bad_assignment_beside_intertwiner(tmp_path: Path) -> None:
    write(
        tmp_path,
        "bad.md",
        "P_C N_C = M_sigma P_C holds, but the synthetic countermodel sets "
        "N_C = M_sigma with P = I.",
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


def test_audit_accepts_latex_transpose_guidance(tmp_path: Path) -> None:
    write(
        tmp_path,
        "guide.tex",
        r"The stale N_C = M_sigma must instead be N_C = M_sigma^\top.",
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


def test_audit_rejects_affirmative_earlier_cycle_claim(tmp_path: Path) -> None:
    write(
        tmp_path,
        "bad.md",
        "Earlier work proves there is no recurrent noncoincident cycle.",
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


def test_audit_accepts_wrapped_cycle_rejection(tmp_path: Path) -> None:
    write(
        tmp_path,
        "history.tex",
        'The old target was "no recurrent noncoincident cycle"\nand is false.',
    )
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


@pytest.mark.parametrize(
    "text",
    [
        "Project premise: the general Pisot Substitution Conjecture is treated as closed.",
        "This is a post-PSC research programme.",
        "# Tier 2: post-PSC Growth Bridge research programme",
        "Since PSC is now proved, Tier 2 builds on it.",
        "The PSC has been settled for all Pisot substitutions.",
    ],
)
def test_audit_rejects_psc_closed_premise(tmp_path: Path, text: str) -> None:
    write(tmp_path, "bad.md", text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


@pytest.mark.parametrize(
    "text",
    [
        "Never describe overlap productivity, SCC Producer, or PSC as proved.",
        'The earlier premise that PSC is closed is withdrawn.',
        "PSC remains open; Tier 2 does not assume it.",
        "See `archive/tier2-post-psc-draft.md` for the old path.",
    ],
)
def test_audit_accepts_psc_open_framing(tmp_path: Path, text: str) -> None:
    write(tmp_path, "ok.md", text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


# Meta-text exemptions are scoped to the matched occurrence, never to a
# keyword elsewhere on the line or in the paragraph.
@pytest.mark.parametrize(
    "text",
    [
        # Synthetic countermodel: "stale"/transpose present, but not marking the match.
        "The synthetic countermodel is N_C = M_sigma with P = I. "
        "No stale wording remains, unlike N_C = M_sigma^T drafts.",
        "The synthetic countermodel is N_C = M_sigma; replace nothing, N_C = M_sigma^T is a typo.",
        # Cycle target: negation governs another clause, or is not a framing negation.
        "Do not cite this note; we prove no recurrent noncoincident cycle.",
        "Do not cite this note, we prove there is no recurrent noncoincident cycle.",
        "It is not hard to see there is no recurrent noncoincident cycle.",
        "We prove no recurrent noncoincident cycle; the old target is false.",
        "There is no recurrent noncoincident cycle, and the old bridge is false.",
        # PSC premise: negation or retraction elsewhere in the paragraph.
        "Do not cite this note; PSC is now proved.",
        "PSC is proved, which is not surprising.",
        "PSC is closed, and the old bridge is withdrawn.",
        "Never mind the drafts.\nPSC is settled for all Pisot substitutions.",
        # Unconditional PDS claim: "unconditionally" is not a conditional.
        "Then the associated tiling dynamical system has pure discrete spectrum unconditionally.",
    ],
)
def test_audit_rejects_claim_beside_unrelated_meta_text(tmp_path: Path, text: str) -> None:
    write(tmp_path, "bad.md", text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


@pytest.mark.parametrize(
    "text",
    [
        "The synthetic countermodel is not N_C = M_sigma but N_C = M_sigma^T.",
        r"The proved identity is P_C\,N_C = M_sigma\,P_C.",
        "Do not cite BD/BK as proving no recurrent noncoincident cycles.",
        "We don't claim there is no recurrent noncoincident cycle.",
        "Earlier drafts targeted no recurrent noncoincident cycle. That target is retired.",
        "- Never describe overlap productivity, G1b-2, concentration, general wedge "
        "productivity, realization G0–G6, SCC Producer, or PSC as proved.",
        "An earlier draft rested on the premise that PSC is closed; that premise is "
        "withdrawn, since it contradicts the source map, which forbids describing PSC\n"
        "as proved.",
    ],
)
def test_audit_accepts_meta_text_governing_the_match(tmp_path: Path, text: str) -> None:
    write(tmp_path, "ok.md", text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


KNOWN_AUDIT_LINE = (
    "| issue #151 | “General PSC is treated as closed for this project.” |"
)


def test_audit_accepts_exact_known_meta_line(tmp_path: Path) -> None:
    write(tmp_path, "docs/audit-2026-09-27.md", KNOWN_AUDIT_LINE + "\n")
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


@pytest.mark.parametrize(
    ("rel", "text"),
    [
        ("docs/audit-2026-09-27.md", KNOWN_AUDIT_LINE + " Hence PSC is proved.\n"),
        ("docs/audit-2026-09-27.md", KNOWN_AUDIT_LINE + "\nPSC is proved.\n"),
        ("docs/other.md", KNOWN_AUDIT_LINE + "\n"),
    ],
)
def test_audit_known_meta_line_is_exact(tmp_path: Path, rel: str, text: str) -> None:
    write(tmp_path, rel, text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1
