"""Regressions for the exact-arithmetic hook.

Specification: docs/rational-interval-arithmetic-spec.md. The first group checks
that every wire of the hook (section 7) is present; the second executes the
spec's laws against the secondary Python oracle ``psc_research.rational_interval``.
"""

from fractions import Fraction
from pathlib import Path
import subprocess
import sys

import pytest

from psc_research.rational_interval import Interval, filter_then_exact, horner

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from audit_exact_arithmetic import (  # noqa: E402
    ALLOWLIST,
    REQUIRED_SECTIONS,
    SPEC,
    SPEC_REL,
    allowlisted,
    audit,
    binding_rows,
)


def text(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


# --- section 7: hook wiring -------------------------------------------------


def test_spec_exists_with_required_sections():
    body = SPEC.read_text(encoding="utf-8")
    assert all(section in body for section in REQUIRED_SECTIONS)


def test_audit_passes_on_current_tree():
    assert audit() == []


def test_audit_script_is_executable_and_green():
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "audit_exact_arithmetic.py")],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_binding_table_covers_the_canonical_kernel():
    by_class = {}
    for cls, paths in binding_rows():
        by_class.setdefault(cls, set()).update(paths)
    assert {
        "mojo/psc/rational_interval.mojo",
        "mojo/psc/perron_interval.mojo",
        "mojo/psc/overlap_interval_audit.mojo",
    } <= by_class["CONFORMS-CHECKED"]
    assert "mojo/psc/rational.mojo" in by_class["DEMO"]
    assert "src/psc_research/rational_interval.py" in by_class["CONFORMS"]
    assert by_class.get("QUARANTINED", set()) == allowlisted() == set()
    assert ALLOWLIST.exists()


def test_audit_rejects_a_float_outside_the_allowlist(tmp_path, monkeypatch):
    import audit_exact_arithmetic as mod

    kernel = tmp_path / "mojo"
    kernel.mkdir()
    (kernel / "leak.mojo").write_text("var x = 2.0 * y\n", encoding="utf-8")
    monkeypatch.setattr(mod, "SCAN_ROOTS", [kernel])
    monkeypatch.setattr(mod, "ROOT", tmp_path)
    monkeypatch.setattr(mod, "binding_rows", lambda text=None: [])
    monkeypatch.setattr(mod, "allowlisted", lambda: set())
    errors = mod.audit()
    assert any("leak.mojo:1" in e and "C1" in e for e in errors)


def test_policy_surfaces_point_at_the_spec():
    for rel in ["README.md", "AGENTS.md", "docs/verification-architecture.md"]:
        assert SPEC_REL in text(rel), rel
    assert SPEC.name in text("docs/README.md")  # the docs index links by basename
    assert "scripts/audit_exact_arithmetic.py" in text(".github/workflows/ci.yml")
    assert "audit_exact_arithmetic.py" in text("scripts/verify_all.sh")


def test_mojo_law_tests_are_wired_into_the_canonical_suite():
    suite = text("mojo/tests/test_rational_interval.mojo")
    for name in [
        "test_rational_field_laws_are_exact",
        "test_interval_dependency_and_subdistributivity",
        "test_reversed_interval_fails_closed",
        "test_filter_never_contradicts_exact_oracle",
    ]:
        assert f"def {name}()" in suite
        assert f"    {name}()" in suite


# --- sections 1 to 3: executable laws against the Fraction oracle -----------


def iv(lo, hi) -> Interval:
    return Interval(Fraction(lo), Fraction(hi))


def test_rational_equality_is_decidable_and_cancellation_lossless():
    assert Fraction(1, 10) + Fraction(2, 10) == Fraction(3, 10)
    a, b, c = Fraction(1, 3), Fraction(1, 7), Fraction(-2, 9)
    assert (a + b) + c == a + (b + c)
    assert a * (b + c) == a * b + a * c
    assert (a + b) - b == a


def test_floats_violate_the_laws_the_spec_is_replacing():
    assert 0.1 + 0.2 != 0.3
    assert (1e16 + 1.0) - 1e16 != 1.0


@pytest.mark.parametrize("px", [Fraction(1), Fraction(5, 2), Fraction(3)])
@pytest.mark.parametrize("py", [Fraction(-1), Fraction(1, 3), Fraction(2)])
def test_inclusion_theorem_on_a_sample(px, py):
    x, y = iv(1, 3), iv(-1, 2)
    assert px + py in x + y
    assert px - py in x - y
    assert px * py in x * y
    assert px * px in x.square()
    assert horner([-2, 0, 1], Interval.point(px)) == Interval.point(px * px - 2)
    assert px * px - 2 in horner([-2, 0, 1], x)


def test_dependency_problem_and_subdistributivity():
    x, y, z = iv(1, 3), iv(-1, 2), iv(2, 5)
    assert x - x == iv(-2, 2)
    assert (x - x).contains_zero()
    assert (x * (y + z)).subset_of(x * y + x * z)
    w = iv(-1, 2)
    assert w.square().subset_of(w * w) and not (w * w).subset_of(w.square())


def test_three_valued_sign_and_fail_closed_construction():
    assert iv(1, 2).strict_sign() == 1
    assert iv(-2, -1).strict_sign() == -1
    assert iv(-1, 1).strict_sign() == 0
    with pytest.raises(ValueError):
        iv(2, 1)
    with pytest.raises(ZeroDivisionError):
        iv(1, 2) / iv(-1, 1)


def test_filter_then_exact_obeys_r1_and_r2():
    calls = []

    def oracle() -> int:
        calls.append(1)
        return -1

    assert filter_then_exact(iv(1, 2), oracle) == (1, True)
    assert calls == []
    assert filter_then_exact(iv(-1, 1), oracle) == (-1, False)
    assert calls == [1]
