"""Recorded data is pinned: every SHA256SUMS verifies, and an evidence packet lists every file it holds.

evidence/ holds recorded run outputs, sources/ imported external material, archive/ superseded
records; all are verbatim, so a checksum mismatch is a modified record, never a refresh.
"""

from __future__ import annotations

import hashlib
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SUMS = sorted(p for plane in ("evidence", "sources", "archive") for p in (ROOT / plane).glob("**/SHA256SUMS"))


def entries(sums: Path) -> dict[Path, str]:
    """``./x`` and a bare name are packet-relative; any other path is repository-relative (``sha256sum -c`` from the root)."""
    # These historical packets use GNU checksum paths relative to their own
    # directories even for nested records. Preserve their original manifests.
    packet_relative = sums in {
        ROOT / 'evidence/class-b-step2c-2026-10-27/SHA256SUMS',
        ROOT / 'evidence/c4-named-overlap-balance-2026-11-11/SHA256SUMS',
        ROOT / 'evidence/c4-finite-fibre-obligations-2026-11-21/SHA256SUMS',
    }
    rows = (line.split(maxsplit=1) for line in sums.read_text(encoding="utf-8").splitlines() if line.strip())
    rels = ((digest, rel.strip()) for digest, rel in rows)
    return {(ROOT if "/" in rel and not rel.startswith("./") and not packet_relative else sums.parent) / rel: digest for digest, rel in rels}


def test_every_evidence_packet_is_pinned():
    packets = [p for p in (ROOT / "evidence").iterdir() if p.is_dir()]
    assert packets and all((p / "SHA256SUMS").is_file() for p in packets)


def verify_packet(sums: Path) -> set[Path]:
    pinned = entries(sums)
    assert pinned
    for path, digest in pinned.items():
        assert path.is_file(), path.relative_to(ROOT)
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, path.relative_to(ROOT)
    covered = set(pinned)
    # The original zero-fibre manifest predates this separately pinned packet.
    # Preserve both manifests: verify the named child, then require exact union
    # coverage. No other nested directory or additional file is exempted.
    if sums == ROOT / 'evidence/c4-zero-fibre-witnesses-2026-11-21/SHA256SUMS':
        nested = sums.parent / 'integration/SHA256SUMS'
        assert nested.is_file(), nested.relative_to(ROOT)
        covered |= {nested} | verify_packet(nested)
    if sums.is_relative_to(ROOT / "evidence"):
        held = {p for p in sums.parent.rglob("*") if p.is_file() and p != sums}
        assert held == covered, "an evidence packet pins exactly the files it holds"
    return covered


@pytest.mark.parametrize("sums", SUMS, ids=lambda p: p.relative_to(ROOT).as_posix())
def test_checksums_verify(sums):
    verify_packet(sums)


def test_pinned_records_are_tracked_for_clean_checkout():
    tracked = set(subprocess.check_output(
        ["git", "ls-files", "-z"], cwd=ROOT, text=True
    ).split("\0"))
    required = {path.relative_to(ROOT).as_posix() for sums in SUMS
                for path in (sums, *entries(sums))}
    assert required <= tracked, "pinned evidence omitted from Git: " + repr(sorted(required - tracked))


@pytest.mark.parametrize("mutation", ["corrupt", "missing", "uncovered", "unknown-packet", "untracked"])
def test_nested_packet_still_refuses_invalid_evidence(tmp_path, monkeypatch, mutation):
    monkeypatch.setitem(globals(), "ROOT", tmp_path)
    parent = tmp_path / "evidence/c4-zero-fibre-witnesses-2026-11-21"
    child = parent / "integration"
    child.mkdir(parents=True)
    for folder in (parent, child):
        payload = folder / "receipt.json"
        payload.write_bytes(b'{"result":"recorded"}\n')
        (folder / "SHA256SUMS").write_text(
            f"{hashlib.sha256(payload.read_bytes()).hexdigest()}  receipt.json\n"
        )
    sums = parent / "SHA256SUMS"
    payload = child / "receipt.json"
    verify_packet(sums)
    if mutation == "untracked":
        monkeypatch.setitem(globals(), "SUMS", [sums, child / "SHA256SUMS"])
        tracked = "\0".join(p.relative_to(tmp_path).as_posix()
                            for p in parent.rglob("*") if p.is_file() and p != payload)
        monkeypatch.setattr(subprocess, "check_output", lambda *args, **kwargs: tracked)
        with pytest.raises(AssertionError, match="pinned evidence omitted from Git"):
            test_pinned_records_are_tracked_for_clean_checkout()
        return
    if mutation == "corrupt":
        payload.write_bytes(b'{"result":"altered"}\n')
    elif mutation == "missing":
        payload.unlink()
    elif mutation == "uncovered":
        (child / "unlisted.log").write_text("unlisted record\n")
    else:
        unknown = parent / "unreviewed"
        unknown.mkdir()
        (unknown / "SHA256SUMS").write_text((child / "SHA256SUMS").read_text())
        (unknown / "receipt.json").write_bytes(payload.read_bytes())
    with pytest.raises(AssertionError):
        verify_packet(sums)
