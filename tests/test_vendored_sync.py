"""Every vendored package matches the commit pinned in vendored.toml."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_vendored_sync as sync  # noqa: E402

PACKAGES = {
    "finite_exact": ("larsbx/finite-math-kernels", "mojo"),
    "substitution_dynamics": ("larsbx/finite-math-kernels", "mojo"),
    "finite_linear_algebra": ("larsbx/finite-math-kernels", "mojo"),
    "claim_governance": ("larsbx/finite-math-kernels", "tools"),
    "proof_records": ("larsbx/finite-math-kernels", "tools"),
}


def test_vendored_packages_match_their_pins():
    assert sync.check() == []
    packages = {p["name"]: p for p in sync.load()}
    assert {n: (p["repository"], p["root"]) for n, p in packages.items()} == PACKAGES
    assert len({pkg["commit"] for pkg in packages.values()}) == 1, "every package is pinned to one upstream commit"
    for name, pkg in packages.items():
        assert pkg["repository"] == "larsbx/finite-math-kernels"
        assert all(rel.startswith(name + "/") for rel in pkg["files"])
    assert set(packages["proof_records"]["files"]) == {"proof_records/__init__.py", "proof_records/records.py", "proof_records/generate_ledgers.py"}


def test_local_patch_is_detected(tmp_path, monkeypatch):
    for pkg in sync.load():
        for rel in pkg["files"]:
            target = tmp_path / pkg["root"] / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / pkg["root"] / rel).read_bytes())
    manifest = tmp_path / "vendored.toml"
    manifest.write_text((ROOT / "vendored.toml").read_text(encoding="utf-8"), encoding="utf-8")
    assert sync.check(tmp_path, manifest) == []
    target = tmp_path / "mojo" / "finite_exact" / "rat_q.mojo"
    target.write_text(target.read_text(encoding="utf-8") + "\n# local patch\n", encoding="utf-8")
    (tmp_path / "mojo" / "finite_exact" / "extra.mojo").write_text("", encoding="utf-8")
    (tmp_path / "tools" / "claim_governance" / "local_rule.py").write_text("", encoding="utf-8")
    errors = sync.check(tmp_path, manifest)
    assert any("rat_q.mojo differs" in e for e in errors)
    assert any("finite_exact/extra.mojo is not pinned" in e for e in errors)
    assert any("claim_governance/local_rule.py is not pinned" in e for e in errors)


def test_no_second_arithmetic_or_kernel_lives_beside_the_packages():
    psc = ROOT / "mojo" / "psc"
    for retired in ["rational.mojo", "rational_interval.mojo", "mat3.mojo", "qlinalg.mojo", "tensor3.mojo"]:
        assert not (psc / retired).exists(), retired
    for path in psc.glob("*.mojo"):
        body = path.read_text(encoding="utf-8")
        assert "struct Rat" not in body and "struct Mat3" not in body, path.name
