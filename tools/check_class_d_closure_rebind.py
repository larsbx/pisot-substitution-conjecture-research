#!/usr/bin/env python3
"""Rebind accepted class-D sources whose bytes changed after acceptance.

Provenance only, never a mathematical verdict. The class-D acceptance of
2026-10-21 froze its sources byte for byte. A later edit to one of them is
admitted only when a dated rebind packet pins the edited bytes and justifies
each one:

- ``native-replay``: the file is in the plus-chamber import closure, and the
  complete native plus-chamber aggregate passed in CI on a commit carrying
  exactly these bytes. The raw job log is archived and must contain the native
  receipt, so a shell command alone is not a receipt.
- ``provenance-tool``: a provenance checker extended to consult this rebind.
  Its exact new bytes are pinned. It asserts no mathematics.

Any other change, or any later edit to a rebound file, still refuses. The
packets of 2026-10-21 remain unchanged.
"""
from __future__ import annotations

from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/class-d-closure-rebind-2026-10-26'
FORMAT = 'class-d-closure-rebind-v1'
ACCEPTED_HEAD = 'a9457d9a08e971d57a635e68086a558fcff88e11'
PLUS_ENTRY = 'kernel/class_d_plus_positive_b_chambers.mojo'
PLUS_MARKER = ('CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 '
               'boundary_lines= 73 finite_prefix_pip= 952 max_symbolic_vertices= 164')
REPLAY_JOB = 'chambers'
REPLAY_STEPS = ('Install pixi', 'Check exact lattice partition', 'Certify all plus chambers and boundary strips')
TOOLS = frozenset({'tools/check_class_d_assembly_evidence.py'})


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_bytes(revision: str, path: str) -> bytes:
    return subprocess.check_output(['git', 'show', f'{revision}:{path}'], cwd=ROOT, stderr=subprocess.DEVNULL)


def validate(packet: Path = PACKET, root: Path = ROOT) -> dict[str, str]:
    """The rebound paths and their admitted digests; raises unless every
    justification holds."""
    manifest = json.loads((packet/'manifest.json').read_text())
    if (manifest.get('format'), manifest.get('accepted_head'), manifest.get('independent_human_review')) != (FORMAT, ACCEPTED_HEAD, False):
        raise ValueError('wrong rebind format, accepted head or review status')
    head, merge = manifest['rebind_head'], manifest['tested_merge']
    commit = (packet/'tested-merge.commit').read_bytes()
    if hashlib.sha1(b'commit '+str(len(commit)).encode()+b'\0'+commit).hexdigest() != merge:
        raise ValueError('tested merge commit object does not match its id')
    if b'parent '+head.encode() not in commit.splitlines():
        raise ValueError('the tested merge does not contain the rebind head')
    paths = manifest['paths']
    if not paths:
        raise ValueError('empty rebind')
    from check_class_d_assembly_evidence import import_closure  # lazy: that module imports this one
    closure = import_closure(PLUS_ENTRY, head)
    for path, entry in paths.items():
        if entry['kind'] == 'native-replay':
            if path not in closure:
                raise ValueError(f'not exercised by the plus-chamber replay: {path}')
        elif entry['kind'] == 'provenance-tool':
            if path not in TOOLS:
                raise ValueError(f'not a provenance tool: {path}')
        else:
            raise ValueError(f'unknown rebind kind: {path}')
        if sha256(git_bytes(head, path)) != entry['sha256']:
            raise ValueError(f'rebind head does not carry the pinned bytes: {path}')
        if sha256((root/path).read_bytes()) != entry['sha256']:
            raise ValueError(f'rebound bytes changed again: {path}')
        if sha256(git_bytes(ACCEPTED_HEAD, path)) == entry['sha256']:
            raise ValueError(f'nothing to rebind: {path}')
    jobs = json.loads((packet/'jobs.json').read_text())
    replay = [j for j in jobs if j['name'] == REPLAY_JOB]
    if len(replay) != 1 or set(manifest['log_sha256']) != {f"{replay[0]['id']}.log"}:
        raise ValueError('exactly one archived plus-chamber replay job is required')
    job = replay[0]
    if (job['head_sha'], job['status'], job['conclusion']) != (head, 'completed', 'success'):
        raise ValueError('the plus-chamber replay did not pass at the rebind head')
    steps = {s['name']: s for s in job['steps']}
    if any(name not in steps or steps[name]['conclusion'] != 'success' for name in REPLAY_STEPS):
        raise ValueError('required replay work was skipped or failed')
    name = f"{job['id']}.log"
    raw = gzip.decompress((packet/(name+'.gz')).read_bytes())
    if sha256(raw) != manifest['log_sha256'][name]:
        raise ValueError('archived raw job log changed')
    log = raw.decode()
    if not any(line.endswith('Z '+PLUS_MARKER) for line in log.splitlines()):
        raise ValueError('missing native plus-chamber receipt (a shell command is not a receipt)')
    if merge not in log:
        raise ValueError('job log does not bind the tested merge')
    return {path: entry['sha256'] for path, entry in paths.items()}


@lru_cache(maxsize=1)
def _rebound() -> dict[str, str]:
    return validate() if (PACKET/'manifest.json').is_file() else {}


def rebound(path: str, digest: str) -> bool:
    """True only for a path the valid rebind packet admits at exactly this digest."""
    return _rebound().get(path) == digest


def main():
    print(json.dumps(dict(rebound=validate(), authority='provenance only; independent human review pending'), indent=2))


if __name__ == '__main__':
    main()
