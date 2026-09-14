"""The vendored finite_exact package must match its pinned upstream exactly."""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import check_finite_exact_sync as sync  # noqa: E402


def test_vendored_files_match_upstream_digests():
    assert sync.check() == []


def test_unrewrite_restores_flat_imports_only_on_import_lines():
    text = "from finite_exact.bigint_z import BigZ\nfrom finite_exact.rat_q import Q\n# finite_exact.rat_q stays\n"
    assert sync.unrewrite(text) == "from bigint_z import BigZ\nfrom rat_q import Q\n# finite_exact.rat_q stays\n"


def test_local_patch_is_detected(tmp_path, monkeypatch):
    package = tmp_path / "mojo" / "finite_exact"
    package.mkdir(parents=True)
    for name in ["bigint_z", "rat_q", "interval_q"]:
        (package / f"{name}.mojo").write_text((sync.PACKAGE / f"{name}.mojo").read_text(encoding="utf-8"), encoding="utf-8")
    (package / "UPSTREAM.md").write_text(sync.PIN.read_text(encoding="utf-8"), encoding="utf-8")
    monkeypatch.setattr(sync, "ROOT", tmp_path)
    monkeypatch.setattr(sync, "PACKAGE", package)
    monkeypatch.setattr(sync, "PIN", package / "UPSTREAM.md")
    assert sync.check() == []
    target = package / "rat_q.mojo"
    target.write_text(target.read_text(encoding="utf-8") + "\n# local patch\n", encoding="utf-8")
    assert any("rat_q.mojo" in e for e in sync.check())
