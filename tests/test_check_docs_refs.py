"""Behaviour of scripts/check_docs_refs.py, and the repository's own compliance."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_docs_refs.py"


def run(root: Path) -> tuple[int, str]:
    r = subprocess.run([sys.executable, str(SCRIPT), str(root)], capture_output=True, text=True)
    return r.returncode, r.stdout


@pytest.fixture
def repo(tmp_path: Path) -> Path:
    """A minimal tree that passes both invariants."""
    (tmp_path / "docs").mkdir()
    (tmp_path / "docs" / "README.md").write_text("# Index\n\n- `note.md` — a note\n", encoding="utf-8")
    (tmp_path / "docs" / "note.md").write_text("# A note\n\nNothing to resolve here.\n", encoding="utf-8")
    return tmp_path


def test_repository_passes():
    code, out = run(ROOT)
    assert code == 0 and out.startswith("OK"), out


def test_minimal_tree_passes(repo: Path):
    assert run(repo)[0] == 0


def test_note_missing_from_the_index_fails(repo: Path):
    (repo / "docs" / "orphan.md").write_text("# Orphan\n", encoding="utf-8")
    code, out = run(repo)
    assert code == 1 and "orphan.md" in out, out


def test_unresolved_reference_fails(repo: Path):
    (repo / "docs" / "note.md").write_text("# A note\n\nSee `src/absent.py`.\n", encoding="utf-8")
    code, out = run(repo)
    assert code == 1 and "src/absent.py does not resolve" in out, out


def test_reference_resolves_relative_to_the_mentioning_file(repo: Path):
    (repo / "docs" / "sub").mkdir()
    (repo / "docs" / "sub" / "deep.mojo").write_text("", encoding="utf-8")
    (repo / "docs" / "note.md").write_text("# A note\n\nSee `sub/deep.mojo`.\n", encoding="utf-8")
    assert run(repo)[0] == 0


def test_reference_resolves_relative_to_the_repository_root(repo: Path):
    (repo / "src").mkdir()
    (repo / "src" / "present.py").write_text("", encoding="utf-8")
    (repo / "docs" / "note.md").write_text("# A note\n\nSee `src/present.py`.\n", encoding="utf-8")
    assert run(repo)[0] == 0


@pytest.mark.parametrize("qualified", ["NLAP: src/absent.py", "finite-math-kernels:src/absent.py"])
def test_a_reference_qualified_by_its_repository_passes(repo: Path, qualified: str):
    (repo / "docs" / "note.md").write_text(f"# A note\n\nSee `{qualified}`.\n", encoding="utf-8")
    assert run(repo)[0] == 0, qualified


def test_a_url_is_not_a_path(repo: Path):
    (repo / "docs" / "note.md").write_text(
        "# A note\n\nSee https://example.invalid/a/b/c.json for the schema.\n", encoding="utf-8")
    assert run(repo)[0] == 0


def test_a_declared_exempt_path_is_allowed_to_be_absent(repo: Path):
    (repo / "docs" / "note.md").write_text(
        "# A note\n\nThe former `scripts/gone.py` was deleted.\n\n"
        "<!-- check-docs-refs: exempt scripts/gone.py -->\n", encoding="utf-8")
    assert run(repo)[0] == 0


def test_declaring_a_path_that_exists_fails(repo: Path):
    (repo / "scripts").mkdir()
    (repo / "scripts" / "here.py").write_text("", encoding="utf-8")
    (repo / "docs" / "note.md").write_text(
        "# A note\n\nSee `scripts/here.py`.\n\n"
        "<!-- check-docs-refs: exempt scripts/here.py -->\n", encoding="utf-8")
    code, out = run(repo)
    assert code == 1 and "declared exempt but exists" in out, out


def test_an_exemption_does_not_leak_into_another_file(repo: Path):
    (repo / "docs" / "note.md").write_text(
        "# A note\n\n`scripts/gone.py`\n\n<!-- check-docs-refs: exempt scripts/gone.py -->\n", encoding="utf-8")
    (repo / "docs" / "other.md").write_text("# Other\n\n`scripts/gone.py`\n", encoding="utf-8")
    (repo / "docs" / "README.md").write_text(
        "# Index\n\n- `note.md`\n- `other.md`\n", encoding="utf-8")
    code, out = run(repo)
    assert code == 1 and "other.md" in out, out


def test_vendored_and_archived_files_are_not_checked(repo: Path):
    (repo / "archive").mkdir()
    (repo / "archive" / "old.md").write_text("# Old\n\n`src/absent.py`\n", encoding="utf-8")
    (repo / "vendor_root").mkdir()
    (repo / "vendor_root" / "vendored.md").write_text("# Vendored\n\n`src/absent.py`\n", encoding="utf-8")
    (repo / "vendored.toml").write_text(
        '[[package]]\nname = "p"\nrepository = "o/r"\ncommit = "0"\nroot = "vendor_root"\n\n'
        '[package.files]\n"vendored.md" = "0"\n', encoding="utf-8")
    assert run(repo)[0] == 0
