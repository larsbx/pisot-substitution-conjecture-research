"""Source pins hold at their recorded revision; every later change is declared.

Each negative control below is a way the old current-tree check could be
satisfied or bypassed wrongly; each must make `verify_pins_at_revision` refuse.
"""
from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from source_pins import (  # noqa: E402
    ABSENT, KINDS, Drift, PinRecord, PinViolation, check_all, load_registry, main, verify_pins_at_revision)

MANIFEST = 'evidence/packet/source-sha256.txt'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(repo: Path, *args: str) -> str:
    return subprocess.run(['git', *args], cwd=repo, check=True, capture_output=True, text=True).stdout.strip()


def commit(repo: Path, files: dict[str, bytes | None], message: str = 'c') -> str:
    for path, data in files.items():
        target = repo / path
        if data is None:
            target.unlink()
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    git(repo, 'add', '-A')
    git(repo, 'commit', '-q', '--allow-empty', '-m', message)
    return git(repo, 'rev-parse', 'HEAD')


def manifest(pins: dict[str, bytes]) -> bytes:
    return ''.join(f'{sha(data)}  {path}\n' for path, data in pins.items()).encode()


@pytest.fixture
def repo(tmp_path: Path) -> tuple[Path, str]:
    """A repository whose manifest pins two sources at revision R."""
    git(tmp_path, 'init', '-q', '-b', 'main')
    git(tmp_path, 'config', 'user.email', 't@t')
    git(tmp_path, 'config', 'user.name', 't')
    sources = {'src/a.mojo': b'a\n', 'src/b.py': b'b\n'}
    revision = commit(tmp_path, {**sources, MANIFEST: manifest(sources)})
    return tmp_path, revision


def drift_of(path: str, data: bytes | None, kind: str | None = None) -> dict[str, Drift]:
    return {path: Drift(ABSENT if data is None else sha(data), 'test edit', kind)}


def test_unchanged_sources_hold(repo):
    root, revision = repo
    commit(root, {'unrelated.txt': b'x'})
    report = verify_pins_at_revision(PinRecord(MANIFEST, revision, {}), root)
    assert report == {'manifest': MANIFEST, 'revision': revision, 'pins': 2, 'drift': []}


def test_undeclared_drift_is_refused(repo):
    root, revision = repo
    commit(root, {'src/a.mojo': b'refactored\n'})
    with pytest.raises(PinViolation, match='undeclared drift.*src/a.mojo'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, {}), root)


def test_declared_drift_is_admitted(repo):
    root, revision = repo
    commit(root, {'src/a.mojo': b'refactored\n'})
    report = verify_pins_at_revision(PinRecord(MANIFEST, revision, drift_of('src/a.mojo', b'refactored\n')), root)
    assert report['drift'] == ['src/a.mojo']


def test_declared_drift_binds_the_current_bytes(repo):
    """A declaration admits one edit, not every later one."""
    root, revision = repo
    commit(root, {'src/a.mojo': b'refactored\n'})
    commit(root, {'src/a.mojo': b'refactored again\n'})
    with pytest.raises(PinViolation, match='drift digest differs.*src/a.mojo'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, drift_of('src/a.mojo', b'refactored\n')), root)


def test_stale_declaration_is_refused(repo):
    root, revision = repo
    with pytest.raises(PinViolation, match='stale drift.*src/a.mojo'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, drift_of('src/a.mojo', b'never happened\n')), root)


def test_declaration_outside_the_manifest_is_refused(repo):
    root, revision = repo
    with pytest.raises(PinViolation, match='stale drift.*src/c.mojo'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, drift_of('src/c.mojo', b'c\n')), root)


def test_deletion_is_drift_and_must_be_declared(repo):
    root, revision = repo
    commit(root, {'src/b.py': None})
    with pytest.raises(PinViolation, match='undeclared drift.*src/b.py'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, {}), root)
    report = verify_pins_at_revision(PinRecord(MANIFEST, revision, drift_of('src/b.py', None)), root)
    assert report['drift'] == ['src/b.py']


def test_pin_false_at_its_revision_is_refused(repo):
    """The wrong revision cannot vouch for a manifest it did not produce."""
    root, _ = repo
    later = commit(root, {'src/a.mojo': b'edited\n'})  # manifest unchanged, so only the pin is false at `later`
    with pytest.raises(PinViolation, match='pin does not hold at revision.*src/a.mojo'):
        verify_pins_at_revision(PinRecord(MANIFEST, later, drift_of('src/a.mojo', b'edited\n')), root)


def test_repinned_manifest_is_refused(repo):
    """Rewriting an archived manifest is refused, even to digests that hold now."""
    root, revision = repo
    commit(root, {'src/a.mojo': b'refactored\n'})
    commit(root, {MANIFEST: manifest({'src/a.mojo': b'refactored\n', 'src/b.py': b'b\n'})})
    with pytest.raises(PinViolation, match='manifest differs from its copy at revision'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, {}), root)


def test_revision_off_the_history_is_refused(repo):
    root, _ = repo
    git(root, 'checkout', '-q', '-b', 'side')
    side = commit(root, {'side.txt': b's'})
    git(root, 'checkout', '-q', 'main')
    with pytest.raises(PinViolation, match='not an ancestor of HEAD'):
        verify_pins_at_revision(PinRecord(MANIFEST, side, {}), root)


@pytest.mark.parametrize('revision, pattern', [
    ('0' * 40, 'revision unavailable'),
    ('HEAD', 'full 40-hex commit'),
    ('abc123', 'full 40-hex commit'),
])
def test_unresolvable_revision_is_refused(repo, revision, pattern):
    root, _ = repo
    with pytest.raises(PinViolation, match=pattern):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, {}), root)


def registry(tmp: Path, body: str) -> Path:
    path = tmp / 'source_pins.toml'
    path.write_text(body)
    return path


@pytest.mark.parametrize('body, pattern', [
    ('[[manifest]]\npath = "m"\nrevision = "r"\nextra = 1\n', 'unexpected keys'),
    ('[[manifest]]\npath = "m"\nrevision = "r"\n[[manifest]]\npath = "m"\nrevision = "r"\n', 'registered twice'),
    ('[[manifest]]\npath = "m"\nrevision = "r"\n[[manifest.drift]]\npath = "p"\ncurrent = "absent"\nreason = " "\n',
     'reason'),
    ('[[manifest]]\npath = "m"\nrevision = "r"\n[[manifest.drift]]\npath = "p"\ncurrent = "beef"\nreason = "x"\n',
     'sha256 or "absent"'),
    ('[[manifest]]\npath = "m"\nrevision = "r"\n' + '[[manifest.drift]]\npath = "p"\ncurrent = "absent"\nreason = "x"\n' * 2,
     'declared twice'),
])
def test_malformed_registry_is_refused(tmp_path, body, pattern):
    with pytest.raises(PinViolation, match=pattern):
        load_registry(registry(tmp_path, body))


def test_unregistered_manifest_is_refused(repo):
    root, revision = repo
    commit(root, {'evidence/other/source-sha256.txt': b''})
    registry(root, f'[[manifest]]\npath = "{MANIFEST}"\nrevision = "{revision}"\n')
    with pytest.raises(PinViolation, match='unregistered.*evidence/other/source-sha256.txt'):
        check_all(root)


def test_repository_pins_hold_at_their_revisions():
    """Every source manifest of this repository, against its registered revision."""
    reports = check_all(ROOT)
    assert len(reports) == len(load_registry(ROOT / 'source_pins.toml'))
    assert all(r['pins'] > 0 for r in reports)


WORKFLOW = (b'    steps:\n      - uses: actions/checkout@v4\n      - run: |\n'
            b'          sha256sum -c evidence/a/source-sha256.txt\n          replay mathematical-certificate\n')
MIGRATED = WORKFLOW.replace(
    b'- uses: actions/checkout@v4\n',
    b'- uses: actions/checkout@v4\n        with:\n          ref: ${{ github.event.pull_request.head.sha || github.sha }}\n'
    b'          fetch-depth: 0\n').replace(b'sha256sum -c evidence/a/source-sha256.txt',
                                       b'python3 tools/source_pins.py evidence/a/source-sha256.txt')
TEST = b'from mojo_smoke.claims import require_contract\ndef main():\n    assert_true(proof())\n'
DECLARED = TEST.replace(b'import require_contract', b'import require_claim, require_contract') + b'    require_claim("Named")\n'


@pytest.mark.parametrize('kind, before, after, admitted', [
    ('workflow-metadata', WORKFLOW, MIGRATED, True),
    ('workflow-metadata', WORKFLOW, WORKFLOW, False),
    ('workflow-metadata', WORKFLOW, MIGRATED.replace(b'replay mathematical-certificate', b'true'), False),
    ('workflow-metadata', WORKFLOW, MIGRATED + b'          skip-the-proof\n', False),
    ('workflow-metadata', WORKFLOW, MIGRATED.replace(b'fetch-depth: 0', b'fetch-depth: 1'), False),
    ('receipt-declaration', TEST, DECLARED, True),
    ('receipt-declaration', TEST, DECLARED + b'    require_claim("Other")\n', True),
    ('receipt-declaration', TEST, DECLARED.replace(b'proof()', b'True'), False),
    ('receipt-declaration', TEST, DECLARED + b'    run_more()\n', False),
    ('receipt-declaration', TEST, TEST, False),
    ('additive-pixi-tasks', b'[tasks]\na = "x"\n', b'[tasks]\na = "x"\nb = "y"\n', True),
    ('additive-pixi-tasks', b'[tasks]\na = "x"\n', b'[tasks]\na = "changed"\n', False),
    ('additive-pixi-tasks', b'[deps]\nm = "1"\n', b'[deps]\nm = "2"\n', False),
    ('additive-pixi-tasks', WORKFLOW, MIGRATED, False),
    ('additive-pixi-tasks', b'\xff', b'[tasks]\n', False),
])
def test_drift_kinds_admit_only_their_edit(kind, before, after, admitted):
    assert bool(KINDS[kind](before, after)) is admitted


def test_kinded_drift_is_checked_against_the_recorded_bytes(repo):
    root, _ = repo
    sources = {'.github/workflows/w.yml': WORKFLOW}
    revision = commit(root, {**sources, MANIFEST: manifest(sources)})
    commit(root, {'.github/workflows/w.yml': MIGRATED})
    ok = PinRecord(MANIFEST, revision, drift_of('.github/workflows/w.yml', MIGRATED, 'workflow-metadata'))
    assert verify_pins_at_revision(ok, root)['drift'] == ['.github/workflows/w.yml']
    tampered = MIGRATED + b'          skip-the-proof\n'
    commit(root, {'.github/workflows/w.yml': tampered})
    with pytest.raises(PinViolation, match='not a workflow-metadata edit'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, drift_of('.github/workflows/w.yml', tampered,
                                                                       'workflow-metadata')), root)


def test_kinded_deletion_is_refused(repo):
    root, revision = repo
    commit(root, {'src/b.py': None})
    with pytest.raises(PinViolation, match='not a receipt-declaration edit'):
        verify_pins_at_revision(PinRecord(MANIFEST, revision, drift_of('src/b.py', None, 'receipt-declaration')), root)


def test_unknown_kind_is_refused(tmp_path):
    body = ('[[manifest]]\npath = "m"\nrevision = "r"\n'
            '[[manifest.drift]]\npath = "p"\ncurrent = "absent"\nreason = "x"\nkind = "trust-me"\n')
    with pytest.raises(PinViolation, match='unknown kind'):
        load_registry(registry(tmp_path, body))


def test_cli_checks_named_manifests_only_if_registered(repo, capsys):
    root, revision = repo
    registry(root, f'[[manifest]]\npath = "{MANIFEST}"\nrevision = "{revision}"\n')
    assert main([MANIFEST], root) == 0
    assert main(['evidence/other/source-sha256.txt'], root) == 1
    assert 'not registered' in capsys.readouterr().err
