"""Source pins hold at the revision that recorded them; drift since then is declared.

A manifest line ``<sha256>  <path>`` certifies the bytes of ``path`` at the
revision ``R`` the manifest was recorded at, not the bytes of today's tree.
`verify_pins_at_revision` checks exactly that, and turns every later change
to a pinned file into an attributable entry of ``source_pins.toml``:

  1. ``R`` is a full commit id, present, and an ancestor of ``HEAD``;
  2. the manifest is byte-identical to its copy at ``R`` (no re-pinning);
  3. every pin ``(d, p)`` holds at ``R``: ``sha256(R:p) = d``;
  4. the observed drift ``{p ↦ sha256(p) | sha256(p) ≠ d}`` (``absent`` for a
     deleted file) equals the declared drift, entry for entry.

Fail closed means refuse the run: each failure raises `PinViolation`.
Nothing is rewritten; a declared drift records that the current file is no
longer the recorded source, so replaying the recorded evidence means checking
out ``R``. Requires full history (Actions checkout ``fetch-depth: 0``).
"""
from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib
from types import MappingProxyType

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = 'source_pins.toml'
MANIFEST_GLOBS = ('evidence/*/source-sha256.txt', 'evidence/*/SOURCE_SHA256SUMS')
ABSENT = 'absent'
SHA256 = re.compile(r'[0-9a-f]{64}')
COMMIT = re.compile(r'[0-9a-f]{40}')


class PinViolation(Exception):
    """A source pin, its revision, or its drift declaration does not hold."""


@dataclass(frozen=True)
class Drift:
    current: str  # sha256 of the current file, or ABSENT
    reason: str


@dataclass(frozen=True)
class PinRecord:
    manifest: str
    revision: str
    drift: Mapping[str, Drift]


def require(condition: object, *message: object) -> None:
    if not condition:
        raise PinViolation(' '.join(map(str, message)))


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_ok(root: Path, *args: str) -> bool:
    return subprocess.run(['git', *args], cwd=root, capture_output=True).returncode == 0


def blob_at(root: Path, revision: str, path: str) -> bytes | None:
    done = subprocess.run(['git', 'cat-file', 'blob', f'{revision}:{path}'], cwd=root, capture_output=True)
    return done.stdout if done.returncode == 0 else None


def current_digest(root: Path, path: str) -> str:
    file = root / path
    return sha256(file.read_bytes()) if file.is_file() else ABSENT


def parse_manifest(text: str) -> tuple[tuple[str, str], ...]:
    """``(digest, path)`` rows of a ``sha256sum`` manifest; paths are repository-relative."""
    rows = tuple((d, p.strip().lstrip('*')) for d, p in
                 (line.split(maxsplit=1) for line in text.splitlines() if line.strip()))
    require(rows, 'empty manifest')
    require(all(SHA256.fullmatch(d) for d, _ in rows), 'malformed digest in manifest')
    require(len({p for _, p in rows}) == len(rows), 'path pinned twice in manifest')
    return rows


def verify_pins_at_revision(record: PinRecord, root: Path = ROOT) -> dict:
    """Check one manifest at its recorded revision and its drift against the declaration."""
    where = f'{record.manifest} @ {record.revision}:'
    revision = record.revision
    require(COMMIT.fullmatch(revision), where, 'revision must be a full 40-hex commit id')
    require(git_ok(root, 'cat-file', '-e', f'{revision}^{{commit}}'), where,
            'revision unavailable (a shallow clone needs fetch-depth: 0)')
    require(git_ok(root, 'merge-base', '--is-ancestor', revision, 'HEAD'), where, 'revision is not an ancestor of HEAD')
    manifest = root / record.manifest
    require(manifest.is_file(), where, 'manifest missing')
    require(blob_at(root, revision, record.manifest) == manifest.read_bytes(), where,
            'manifest differs from its copy at revision; re-pinning an archived manifest is refused')
    pins = parse_manifest(manifest.read_text())
    for digest, path in pins:
        recorded = blob_at(root, revision, path)
        require(recorded is not None and sha256(recorded) == digest, where, 'pin does not hold at revision:', path)
    observed = {p: c for d, p in pins if (c := current_digest(root, p)) != d}
    declared = {p: x.current for p, x in record.drift.items()}
    undeclared = sorted(observed.keys() - declared.keys())
    stale = sorted(declared.keys() - observed.keys())
    moved = sorted(p for p in observed.keys() & declared.keys() if observed[p] != declared[p])
    require(not undeclared, where, 'undeclared drift:', undeclared, '; declare in', REGISTRY, ':',
            ''.join(f'\n[[manifest.drift]]\npath = "{p}"\ncurrent = "{observed[p]}"\nreason = "..."' for p in undeclared))
    require(not stale, where, 'stale drift declaration (file matches its pin or is not pinned):', stale)
    require(not moved, where, 'drift digest differs from declaration (re-declare the new edit):',
            {p: observed[p] for p in moved})
    return {'manifest': record.manifest, 'revision': revision, 'pins': len(pins), 'drift': sorted(observed)}


def _keys(table: Mapping, allowed: set[str], where: str) -> None:
    require(table.keys() <= allowed, where, 'unexpected keys:', sorted(table.keys() - allowed))
    require(table.keys() >= allowed - {'drift'}, where, 'missing keys:', sorted(allowed - {'drift'} - table.keys()))


def _drift(rows: list[Mapping], where: str) -> Mapping[str, Drift]:
    out: dict[str, Drift] = {}
    for row in rows:
        _keys(row, {'path', 'current', 'reason'}, where)
        path, current, reason = row['path'], row['current'], row['reason']
        require(path not in out, where, 'drift declared twice:', path)
        require(current == ABSENT or SHA256.fullmatch(current), where, path, 'current must be a sha256 or "absent"')
        require(reason.strip(), where, path, 'needs a reason')
        out[path] = Drift(current, reason)
    return MappingProxyType(out)


def load_registry(path: Path) -> tuple[PinRecord, ...]:
    require(path.is_file(), 'registry missing:', path)
    tables = tomllib.loads(path.read_text()).get('manifest', [])
    records = []
    for table in tables:
        where = f'{path.name}: {table.get("path")}:'
        _keys(table, {'path', 'revision', 'drift'}, where)
        records.append(PinRecord(table['path'], table['revision'], _drift(table.get('drift', []), where)))
    names = [r.manifest for r in records]
    require(len(set(names)) == len(names), path.name, 'manifest registered twice')
    return tuple(records)


def check_all(root: Path = ROOT) -> list[dict]:
    """Every source manifest is registered, and every registered manifest holds."""
    records = load_registry(root / REGISTRY)
    found = {str(p.relative_to(root)) for g in MANIFEST_GLOBS for p in root.glob(g)}
    registered = {r.manifest for r in records}
    require(found <= registered, 'unregistered source manifests:', sorted(found - registered))
    return [verify_pins_at_revision(r, root) for r in records]


if __name__ == '__main__':
    try:
        print(json.dumps(check_all(), indent=2))
    except PinViolation as violation:
        sys.exit(f'source pins: {violation}')
