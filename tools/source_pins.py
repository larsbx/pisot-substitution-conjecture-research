"""Source pins hold at the revision that recorded them; drift since then is declared.

A manifest line ``<sha256>  <path>`` certifies the bytes of ``path`` at the
revision ``R`` the manifest was recorded at, not the bytes of today's tree.
`verify_pins_at_revision` checks exactly that, and turns every later change
to a pinned file into an attributable entry of ``source_pins.toml``:

  1. ``R`` is a full commit id, present, and an ancestor of ``HEAD``;
  2. the manifest is byte-identical to its copy at ``R`` (no re-pinning);
  3. every pin ``(d, p)`` holds at ``R``: ``sha256(R:p) = d``;
  4. the observed drift ``{p ↦ sha256(p) | sha256(p) ≠ d}`` (``absent`` for a
     deleted file) equals the declared drift, entry for entry;
  5. a drift entry with a ``kind`` is that edit and nothing else:
     ``KINDS[kind](sha256⁻¹ at R, current bytes)`` holds.

A ``reason`` alone makes a drift attributable; a ``kind`` makes it machine
-checked as non-mathematical.

Fail closed means refuse the run: each failure raises `PinViolation`.
Nothing is rewritten; a declared drift records that the current file is no
longer the recorded source, so replaying the recorded evidence means checking
out ``R``. Requires full history (Actions checkout ``fetch-depth: 0``).
"""
from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib
from types import MappingProxyType

from check_class_d_integration_ci import additive_pixi_tasks_only

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = 'source_pins.toml'
MANIFEST_GLOBS = ('evidence/*/source-sha256.txt', 'evidence/*/SOURCE_SHA256SUMS')
ABSENT = 'absent'
SHA256 = re.compile(r'[0-9a-f]{64}')
COMMIT = re.compile(r'[0-9a-f]{40}')
CHECKOUT = b'- uses: actions/checkout@v4\n'
FULL_HISTORY_CHECKOUT = CHECKOUT + (b'        with:\n          ref: ${{ github.event.pull_request.head.sha || github.sha }}\n'
                                    b'          fetch-depth: 0\n')
MANIFEST_CHECK = rb'sha256sum -c (evidence/\S+/(?:source-sha256\.txt|SOURCE_SHA256SUMS))'


class PinViolation(Exception):
    """A source pin, its revision, or its drift declaration does not hold."""


@dataclass(frozen=True)
class Drift:
    current: str  # sha256 of the current file, or ABSENT
    reason: str
    kind: str | None = None


@dataclass(frozen=True)
class PinRecord:
    manifest: str
    revision: str
    drift: Mapping[str, Drift]


def workflow_metadata(before: bytes, after: bytes) -> bool:
    """Checkouts pinned to the PR head with full history; ``sha256sum -c`` of a manifest replaced by this tool."""
    wanted = re.sub(MANIFEST_CHECK, rb'python3 tools/source_pins.py \1', before.replace(CHECKOUT, FULL_HISTORY_CHECKOUT))
    return wanted != before and after == wanted


def receipt_declaration(before: bytes, after: bytes) -> bool:
    """``require_claim`` imported and appended after the assertions; nothing else changes."""
    widened = before.replace(b'import require_contract\n', b'import require_claim, require_contract\n')
    return after.startswith(widened) and re.fullmatch(rb'(    require_claim\("\w+"\)\n)+', after[len(widened):]) is not None


def additive_pixi_tasks(before: bytes, after: bytes) -> bool:
    """New pixi task names only; unparsable bytes are not this edit."""
    try:
        return additive_pixi_tasks_only(before, after)
    except (UnicodeDecodeError, ValueError):  # tomllib.TOMLDecodeError is a ValueError
        return False


KINDS = MappingProxyType({
    'workflow-metadata': workflow_metadata,
    'receipt-declaration': receipt_declaration,
    'additive-pixi-tasks': additive_pixi_tasks,
})


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
    recorded = {path: blob_at(root, revision, path) for _, path in pins}
    for digest, path in pins:
        require(recorded[path] is not None and sha256(recorded[path]) == digest, where,
                'pin does not hold at revision:', path)
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
    for path, drift in record.drift.items():
        if drift.kind is None:
            continue
        file = root / path
        require(file.is_file() and KINDS[drift.kind](recorded[path], file.read_bytes()), where, path,
                f'is not a {drift.kind} edit of its recorded bytes')
    return {'manifest': record.manifest, 'revision': revision, 'pins': len(pins), 'drift': sorted(observed)}


def _keys(table: Mapping, allowed: set[str], where: str, optional: set[str]) -> None:
    require(table.keys() <= allowed, where, 'unexpected keys:', sorted(table.keys() - allowed))
    require(table.keys() >= allowed - optional, where, 'missing keys:', sorted(allowed - optional - table.keys()))


def _drift(rows: list[Mapping], where: str) -> Mapping[str, Drift]:
    out: dict[str, Drift] = {}
    for row in rows:
        _keys(row, {'path', 'current', 'reason', 'kind'}, where, optional={'kind'})
        path, current, reason, kind = row['path'], row['current'], row['reason'], row.get('kind')
        require(path not in out, where, 'drift declared twice:', path)
        require(current == ABSENT or SHA256.fullmatch(current), where, path, 'current must be a sha256 or "absent"')
        require(reason.strip(), where, path, 'needs a reason')
        require(kind is None or kind in KINDS, where, path, 'unknown kind:', kind)
        out[path] = Drift(current, reason, kind)
    return MappingProxyType(out)


def load_registry(path: Path) -> tuple[PinRecord, ...]:
    require(path.is_file(), 'registry missing:', path)
    tables = tomllib.loads(path.read_text()).get('manifest', [])
    records = []
    for table in tables:
        where = f'{path.name}: {table.get("path")}:'
        _keys(table, {'path', 'revision', 'drift'}, where, optional={'drift'})
        records.append(PinRecord(table['path'], table['revision'], _drift(table.get('drift', []), where)))
    names = [r.manifest for r in records]
    require(len(set(names)) == len(names), path.name, 'manifest registered twice')
    return tuple(records)


def check_all(root: Path = ROOT, manifests: Sequence[str] = ()) -> list[dict]:
    """Every source manifest is registered, and the named (default: every) registered manifest holds."""
    records = {r.manifest: r for r in load_registry(root / REGISTRY)}
    found = {str(p.relative_to(root)) for g in MANIFEST_GLOBS for p in root.glob(g)}
    require(found <= records.keys(), 'unregistered source manifests:', sorted(found - records.keys()))
    named = [m.removeprefix('./') for m in manifests] or list(records)
    require(set(named) <= records.keys(), 'manifest not registered in', REGISTRY, ':', sorted(set(named) - records.keys()))
    return [verify_pins_at_revision(records[m], root) for m in named]


def main(manifests: Sequence[str], root: Path = ROOT) -> int:
    try:
        print(json.dumps(check_all(root, manifests), indent=2))
        return 0
    except PinViolation as violation:
        print(f'source pins: {violation}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
