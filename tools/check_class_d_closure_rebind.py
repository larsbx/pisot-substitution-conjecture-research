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

Packets are listed explicitly in ``PACKETS``, oldest first, and admit
disjoint paths. Format v1 tested a merge commit and carries the 2026-10-26
receipt. Format v2 tested the rebind head itself (a ``workflow_dispatch`` run)
and pins its own receipt line, because an engine change may move the
aggregate's finite-prefix and boundary-line counts. Its wedge and explicit-line
counts stay fixed.
"""
from __future__ import annotations

from functools import lru_cache
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/class-d-closure-rebind-2026-10-26'
PACKETS = (PACKET, ROOT / 'evidence/class-d-closure-rebind-2026-10-30')
FORMAT = 'class-d-closure-rebind-v1'
FORMATS = (FORMAT, 'class-d-closure-rebind-v2')
ACCEPTED_HEAD = 'a9457d9a08e971d57a635e68086a558fcff88e11'
PLUS_ENTRY = 'kernel/class_d_plus_positive_b_chambers.mojo'
PLUS_MARKER = ('CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 '
               'boundary_lines= 73 finite_prefix_pip= 952 max_symbolic_vertices= 164')
PLUS_RECEIPT = re.compile(r'CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 '
                          r'boundary_lines= \d+ finite_prefix_pip= \d+ max_symbolic_vertices= \d+')
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
    fmt = manifest.get('format')
    if fmt not in FORMATS or (manifest.get('accepted_head'), manifest.get('independent_human_review')) != (ACCEPTED_HEAD, False):
        raise ValueError('wrong rebind format, accepted head or review status')
    head = manifest['rebind_head']
    if fmt == FORMAT:
        merge, marker = manifest['tested_merge'], PLUS_MARKER
        commit = (packet/'tested-merge.commit').read_bytes()
        if hashlib.sha1(b'commit '+str(len(commit)).encode()+b'\0'+commit).hexdigest() != merge:
            raise ValueError('tested merge commit object does not match its id')
        if b'parent '+head.encode() not in commit.splitlines():
            raise ValueError('the tested merge does not contain the rebind head')
    else:
        merge, marker = head, manifest['plus_receipt']
        if subprocess.run(['git', 'cat-file', '-e', head+'^{commit}'], cwd=ROOT, capture_output=True).returncode:
            raise ValueError('the rebind head is not a commit of this repository')
        if not PLUS_RECEIPT.fullmatch(marker):
            raise ValueError('the pinned plus-chamber receipt has the wrong shape')
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
    if not any(line.endswith('Z '+marker) for line in log.splitlines()):
        raise ValueError('missing native plus-chamber receipt (a shell command is not a receipt)')
    if merge not in log:
        raise ValueError('job log does not bind the tested merge')
    return {path: entry['sha256'] for path, entry in paths.items()}


@lru_cache(maxsize=1)
def _rebound() -> dict[str, str]:
    admitted: dict[str, str] = {}
    for packet in PACKETS:
        if (packet/'manifest.json').is_file():
            paths = validate(packet)
            if admitted.keys() & paths.keys():
                raise ValueError('a later rebind packet re-admits an already rebound path')
            admitted |= paths
    return admitted


def rebound(path: str, digest: str) -> bool:
    """True only for a path the valid rebind packet admits at exactly this digest."""
    return _rebound().get(path) == digest


def main():
    print(json.dumps(dict(rebound=_rebound(), authority='provenance only; independent human review pending'), indent=2))


if __name__ == '__main__':
    main()
