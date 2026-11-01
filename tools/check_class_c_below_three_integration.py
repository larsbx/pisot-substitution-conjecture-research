"""Provenance-only integration guard for PR #394; no mathematical verdict.

Current #394 pins are checked against the working tree. Historical #392
pins are checked against their original Git objects, and every current
source drift must be explicitly inventoried. No packet is re-pinned here.
Requires full Git history (Actions checkout fetch-depth: 0).
"""
from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/class-c-below-three-integration-2026-11-01'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_bytes(ref: str, path: str) -> bytes:
    return subprocess.check_output(['git', 'show', f'{ref}:{path}'], cwd=ROOT)


def check() -> dict:
    audit = json.loads((PACKET / 'audit.json').read_text())
    for path, digest in audit['integration_source_sha256'].items():
        assert sha((ROOT / path).read_bytes()) == digest, path
    original = audit['inspected_head']
    base = audit['inspected_main']
    subprocess.run(['git', 'merge-base', '--is-ancestor', base, 'HEAD'], cwd=ROOT, check=True)
    paths = set(subprocess.check_output(
        ['git', 'diff', '--name-only', f'{base}...{original}'], cwd=ROOT, text=True).splitlines())
    assert len(paths) == 142
    assert {r['path'] for r in audit['files']} == paths
    assert len(audit['files']) == len(paths)
    for row in audit['files']:
        actual = subprocess.check_output(
            ['git', 'rev-parse', f"{original}:{row['path']}"], cwd=ROOT, text=True).strip()
        assert actual == row['blob_sha'], row['path']
    # All original evidence bytes, including README, plan, provenance and
    # checksums, survive unchanged. Historical source drift is separate.
    for path, digest in audit['immutable_packet_sha256'].items():
        assert sha((ROOT / path).read_bytes()) == digest, path
    archived = ROOT / audit['archived_workflow']
    assert archived.read_bytes() == git_bytes(original, '.github/workflows/class-c-slope-three.yml')
    assert not (ROOT / '.github/workflows/class-c-slope-three.yml').exists()
    current = json.loads((ROOT / 'evidence/class-c-below-three-2026-10-29/provenance.json').read_text())
    for path, digest in current['sources'].items():
        assert sha((ROOT / path).read_bytes()) == digest, path
    historical = json.loads((ROOT / 'evidence/class-c-slope-three-2026-10-29/provenance.json').read_text())
    drift = {}
    for path, digest in historical['sources'].items():
        assert sha(git_bytes(audit['historical_392_head'], path)) == digest, path
        actual = sha((ROOT / path).read_bytes())
        if actual != digest:
            drift[path] = {'historical_sha256': digest, 'current_sha256': actual}
    assert drift == audit['historical_source_drift'], drift
    # Accepted theorem source identities and ancestry, without claiming a
    # human review or inferring hosted acceptance from Git ancestry.
    for dep in audit['upper_region_dependencies']:
        subprocess.run(['git', 'merge-base', '--is-ancestor', dep['main_merge'], base], cwd=ROOT, check=True)
        assert sha((ROOT / dep['path']).read_bytes()) == dep['sha256'], dep['path']
    return {'inspected_diff_files': len(paths),
            'categories': dict(sorted(Counter(r['category'] for r in audit['files']).items())),
            'immutable_packet_files': len(audit['immutable_packet_sha256']),
            'current_source_pins': len(current['sources']),
            'historical_source_pins': len(historical['sources']),
            'historical_source_drifts': sorted(drift),
            'archived_workflow_identical': True,
            'scope': 'source provenance only; no hosted or independent proof certification'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2, sort_keys=True))
