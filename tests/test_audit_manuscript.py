import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

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
        The matrix acts on an invariant subspace as a similar copy of $M_\\sigma$.
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
        "Results:\n\n- PSC is closed.\n- The corpus is finite.",
        "Avoid overclaiming.\n\n- PSC is closed.",
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
        "Avoid these formulations unless a proof justifies them:\n\n- \"PSC is closed.\"\n- \"BPA finiteness is solved.\"",
    ],
)
def test_audit_accepts_psc_open_framing(tmp_path: Path, text: str) -> None:
    write(tmp_path, "ok.md", text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


@pytest.mark.parametrize(
    "text",
    [
        "C1 <=> C4.",
        "We prove C4 ⇔ C1.",
        "C1 is equivalent to C4.",
        r"The manuscript asserts $C_1 \Longleftrightarrow C_{4}$.",
        "Earlier work proves C4 iff C1.",
        "The old argument is false, but C1 <=> C4.",
        "The old argument is false, BUT C1 <=> C4.",
        "The old argument is withdrawn. C1 <=> C4.",
        "Unlike the withdrawn predecessor argument, C1 <=> C4.",
        "C1 <=> C4, while the older argument is false.",
        "It is not false that C1 <=> C4.",
        "Do not reject C1 <=> C4.",
        "- The old argument is withdrawn\n- C1 <=> C4.",
        "The normalized transfer is Q2 N_C = Lambda^2(M) Q2.",
        "The normalized transfer is Q3 N_C = Phi3 Q3.",
        r"For normalized states, $Q_{2} N_{C} = \Lambda^{2}(M) Q_{2}$.",
        r"Earlier work proves $Q_3 N_C = \Phi_3 Q_3$.",
        "Predecessor contraction proves G1.",
        "Predecessor-contraction argument implies BPA finiteness.",
        r"Predecessor contraction \Rightarrow G_1.",
        "Earlier work supplies a predecessor contraction proof of G1.",
        "Fibonacci defeats an earlier argument, and we prove there is no recurrent noncoincident cycle.",
    ],
)
def test_audit_rejects_missing_issue3_controls(tmp_path: Path, text: str) -> None:
    write(tmp_path, "bad.md", text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


@pytest.mark.parametrize(
    "text",
    [
        "With G1 for extraction, C4 => C3-local => C2 => C1 is the sufficient direction.",
        r"Under G1, $C_4 \Rightarrow C_1$ does not supply the converse.",
        "The false equivalence C1 <=> C4 is retired.",
        "The earlier claim C4 iff C1 is not established.",
        "The claim C1 <=> C4 is not true.",
        "Do not infer C1 <=> C4.",
        r"The claim $C_1 \Leftrightarrow C_4$ is \emph{false}.",
        "Q2 S = Lambda^2(M) Q2 and Q3 S = Phi3 Q3, where S=A-B.",
        "The correct identity is Q2 N_C = Lambda^2(M) Q2 + 2 Q2 B, since N_C = S + 2B.",
        "The correct identity is Q3 N_C = Phi3 Q3 + 2 Q3 B, since N_C = S + 2B.",
        "The unsigned formula Q2 N_C = Lambda^2(M) Q2 is withdrawn.",
        "The false normalized identity Q3 N_C = Phi3 Q3 must use S instead.",
        "Predecessor contraction does not prove G1.",
        "The withdrawn predecessor-contraction proof of G1 needs replacement.",
        "The claim that predecessor contraction proves G1 is false.",
        'The historical chain "finite BPA -> no recurrent noncoincident cycle -> PDS" is not established.',
        'Fibonacci defeats the historical claim "there are no recurrent noncoincident cycles".',
        "Human review is post-PSC.",
        "Human validation remains post-PSC. PSC remains open.",
    ],
)
def test_audit_accepts_scoped_results_and_explicit_retractions(tmp_path: Path, text: str) -> None:
    write(tmp_path, "ok.md", text)
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0


def test_review_timing_does_not_exempt_psc_closure_claim(tmp_path: Path) -> None:
    write(tmp_path, "bad.md", "Human review is post-PSC. PSC is proved.")
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


@pytest.mark.parametrize("path", ["manuscripts/paper.tex", "docs/verification-architecture.md"])
def test_default_scan_checks_live_manuscripts_and_verification_architecture(tmp_path: Path, path: str, capsys) -> None:
    write(tmp_path, path, "C1 <=> C4.")
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1
    assert path in capsys.readouterr().err


def test_historical_allowlist_is_explicit_and_reported_separately(tmp_path: Path, capsys) -> None:
    for directory in audit_manuscript.HISTORICAL_ROOTS:
        write(tmp_path, f"{directory}/old.md", "C1 <=> C4.")
    write(tmp_path, "README.md", "C4 => C1.")

    assert audit_manuscript.main(["--root", str(tmp_path)]) == 0
    assert "old.md" not in capsys.readouterr().out
    assert audit_manuscript.main(["--root", str(tmp_path), "--report-history"]) == 0
    output = capsys.readouterr()
    assert "Historical manuscript/source findings (nonblocking): 3" in output.out
    for directory in audit_manuscript.HISTORICAL_ROOTS:
        assert f"{directory}/old.md" in output.out
    assert not output.err


def test_dated_live_documents_are_not_implicitly_historical(tmp_path: Path) -> None:
    write(tmp_path, "docs/audit-2026-09-10.md", "C1 <=> C4.")
    assert audit_manuscript.main(["--root", str(tmp_path)]) == 1


def test_live_failure_stays_fatal_with_historical_report(tmp_path: Path, capsys) -> None:
    write(tmp_path, "archive/old.md", "C1 <=> C4.")
    write(tmp_path, "README.md", "Predecessor contraction proves G1.")
    assert audit_manuscript.main(["--root", str(tmp_path), "--report-history"]) == 1
    output = capsys.readouterr()
    assert "Historical manuscript/source findings (nonblocking): 1" in output.out
    assert "README.md" in output.err
    assert "archive/old.md" not in output.err


def test_scan_order_is_deterministic_and_ignores_dependency_trees(tmp_path: Path) -> None:
    for name in ["docs/z.md", "a.md", "docs/a.md", ".lake/old.md", ".pixi/old.md"]:
        write(tmp_path, name, "C1 <=> C4.")
    paths = [str(p.relative_to(tmp_path)) for p in audit_manuscript.iter_text_files(tmp_path)]
    assert paths == ["a.md", "docs/a.md", "docs/z.md"]


def test_strict_current_keeps_its_compatibility_scope(tmp_path: Path) -> None:
    write(tmp_path, "docs/proof-ladder.md", "C4 => C1.")
    write(tmp_path, "manuscripts/paper.tex", "C1 <=> C4.")
    assert audit_manuscript.main(["--root", str(tmp_path), "--strict-current"]) == 0
