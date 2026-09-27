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


def audit(tmp_path: Path, text: str, rel: str = "doc.md") -> int:
    write(tmp_path, rel, text)
    return audit_manuscript.main(["--root", str(tmp_path)])


@pytest.mark.parametrize(
    "text",
    [
        "P_C N_C = M_sigma P_C holds; the countermodel sets N_C = M_sigma with P = I.",
        r"P_C\,N_C = M_sigma\,P_C, whereas the synthetic model has N_C = M_sigma.",
        "N_C = M_sigma P_C is not the intertwiner.",
        "P_C N_C = M_sigma, P = I.",
    ],
)
def test_parikh_exemption_is_tied_to_the_matched_identity(tmp_path: Path, text: str) -> None:
    assert audit(tmp_path, text) == 1


@pytest.mark.parametrize("sep", [" ", r"\,", r"\;", "  "])
def test_parikh_exemption_accepts_latex_spacing(tmp_path: Path, sep: str) -> None:
    assert audit(tmp_path, f"We use P_C{sep}N_C = M_sigma{sep}P_C.") == 0


@pytest.mark.parametrize("t", ["^T", r"\top", r"^\top", r"^\T", r"^{\top}", r"^{T}"])
def test_transpose_guidance_accepts_every_supported_spelling(tmp_path: Path, t: str) -> None:
    assert audit(tmp_path, f"The stale N_C = M_sigma must instead be N_C = M_sigma{t}.") == 0
    assert audit(tmp_path, f"The countermodel is N_C = M_sigma{t} with P = I.") == 0


@pytest.mark.parametrize(
    "text",
    [
        # replacement present, but the bad occurrence is not the one marked stale
        "The stale N_C = M_sigma must instead be N_C = M_sigma^T; we set N_C = M_sigma.",
        # replacement in a different sentence
        "The countermodel is N_C = M_sigma. Elsewhere N_C = M_sigma^T should hold.",
        # guidance vocabulary without a transposed replacement
        "The stale N_C = M_sigma must be kept.",
    ],
)
def test_transpose_guidance_is_tied_to_the_matched_occurrence(tmp_path: Path, text: str) -> None:
    assert audit(tmp_path, text) == 1


@pytest.mark.parametrize(
    "text",
    [
        "Earlier work proves there is no recurrent noncoincident cycle.",
        "Earlier drafts attempted it; we prove there is no recurrent noncoincident cycle.",
        "Earlier work proves there is no recurrent noncoincident cycle, and we do not need BK.",
        "The old claim is false. Earlier work proves there is no recurrent noncoincident cycle.",
        'The target "no recurrent noncoincident cycle" is false; hence there is no '
        "recurrent noncoincident cycle.",
        "We prove there is no recurrent noncoincident cycle, which is why the naive bound is false.",
        "We prove there is no recurrent noncoincident cycle. The proof is false-proof.",
    ],
)
def test_cycle_exemption_requires_negation_of_the_matched_claim(tmp_path: Path, text: str) -> None:
    assert audit(tmp_path, text) == 1


@pytest.mark.parametrize(
    "text",
    [
        "Do not cite BD/BK as proving no recurrent noncoincident cycles.",
        'The target is no longer "there are no recurrent noncoincident cycles".',
        "The cycle-exclusion target (``no recurrent noncoincident cycle in $B$''), pursued in "
        "earlier drafts, is false as a general theorem.",
        "Hence ``no recurrent noncoincident cycle'' and ``noncoincident cycles have nonzero "
        "displacement'' are false as general statements.",
        "Earlier formulations attempted to prove that no recurrent noncoincident cycle exists "
        "in $B$, with more content. That target is false as a general theorem.",
        "The retired target ``no recurrent noncoincident cycle'' is replaced by SCC Producer.",
    ],
)
def test_cycle_exemption_accepts_explicit_retirement(tmp_path: Path, text: str) -> None:
    assert audit(tmp_path, text) == 0
