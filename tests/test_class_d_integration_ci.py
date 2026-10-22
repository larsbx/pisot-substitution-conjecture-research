"""An incomplete CI record cannot discharge the scoped integration gate."""
import copy
import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import check_class_d_integration_ci as ci


def packet():
    return (json.loads((ci.PACKET/'manifest.json').read_text()),
            json.loads((ci.PACKET/'check-runs.json').read_text()),
            json.loads((ci.PACKET/'repository-jobs.json').read_text())['jobs']
            + json.loads((ci.PACKET/'component-jobs.json').read_text()))


def test_accepted_tree_keeps_review_and_universal_obligations_open():
    out = ci.validate(*packet())
    assert out['class_d_project_accepted'] and out['all_checks_successful'] == 64
    assert not out['independent_human_review'] and not out['universal_139_closed']


@pytest.mark.parametrize('conclusion', ['failure', 'cancelled', None])
def test_unsuccessful_check_cannot_accept(conclusion):
    manifest, checks, jobs = packet()
    checks['check_runs'][0]['conclusion'] = conclusion
    with pytest.raises(ValueError, match='pending, failed'):
        ci.validate(manifest, checks, jobs)


def test_wrong_head_and_missing_check_cannot_accept():
    manifest, checks, jobs = packet()
    incomplete = copy.deepcopy(checks)
    incomplete['check_runs'].pop()
    with pytest.raises(ValueError, match='incomplete check'):
        ci.validate(manifest, incomplete, jobs)
    checks['check_runs'][0]['head_sha'] = '0'*40
    with pytest.raises(ValueError, match='wrong-head'):
        ci.validate(manifest, checks, jobs)


@pytest.mark.parametrize('step', ['Independent rational calibration and receipt agreement',
                                  'Run prefix-dev/setup-pixi@v0.9.1'])
def test_skipped_calibration_or_environment_cannot_accept(step):
    manifest, checks, jobs = packet()
    job = next(j for j in jobs if j['id'] == 119058204076)
    next(s for s in job['steps'] if s['name'] == step)['conclusion'] = 'skipped'
    with pytest.raises(ValueError, match='required work was skipped'):
        ci.validate(manifest, checks, jobs)


def test_source_and_receipt_scope_cannot_shrink():
    manifest, checks, jobs = packet()
    bad = copy.deepcopy(manifest)
    bad['source_sha256'].pop('kernel/pixi.lock')
    with pytest.raises(ValueError, match='incomplete accepted source'):
        ci.validate(bad, checks, jobs)
    bad = copy.deepcopy(manifest)
    bad['source_sha256']['kernel/pixi.lock'] = '0'*64
    with pytest.raises(ValueError, match='source, lock or workflow changed'):
        ci.validate(bad, checks, jobs)
    manifest['log_sha256']['119058204076.log'] = '0'*64
    with pytest.raises(ValueError, match='raw job log changed'):
        ci.validate(manifest, checks, jobs)


def test_scope_is_historical_not_a_current_workflow_directory_scan(monkeypatch):
    original = Path.glob
    def no_current_workflow_scan(path, pattern):
        if path == ROOT / '.github/workflows':
            raise AssertionError('historical acceptance cannot depend on current workflow listing')
        return original(path, pattern)
    monkeypatch.setattr(Path, 'glob', no_current_workflow_scan)
    assert ci.validate(*packet())['class_d_project_accepted']
    manifest, checks, jobs = packet()
    manifest['source_sha256']['.github/workflows/later-unrelated.yml'] = '0'*64
    with pytest.raises(ValueError, match='incomplete accepted source'):
        ci.validate(manifest, checks, jobs)


def test_changed_accepted_workflow_bytes_still_refuse(monkeypatch):
    manifest, checks, jobs = packet()
    workflow = next(p for p in manifest['source_sha256'] if p.startswith('.github/workflows/'))
    original = Path.read_bytes
    def damaged(path):
        return b'changed accepted workflow' if path == ROOT / workflow else original(path)
    monkeypatch.setattr(Path, 'read_bytes', damaged)
    with pytest.raises(ValueError, match='source, lock or workflow changed'):
        ci.validate(manifest, checks, jobs)


def test_only_additional_pixi_task_names_preserve_accepted_execution():
    accepted = b'[workspace]\nplatforms=["linux-64"]\n[dependencies]\nmodular="locked"\n[tasks]\ntest="bash run_tests.sh"\n'
    extension = accepted + b'new-experiment="mojo run experiment.mojo"\n'
    assert ci.additive_pixi_tasks_only(accepted, extension)
    assert not ci.additive_pixi_tasks_only(accepted, extension.replace(b'bash run_tests.sh', b'true'))
    assert not ci.additive_pixi_tasks_only(accepted, extension.replace(b'modular="locked"', b'modular="*"'))
    assert not ci.additive_pixi_tasks_only(accepted, extension.replace(b'platforms=["linux-64"]', b'platforms=["osx-arm64"]'))
    assert not ci.additive_pixi_tasks_only(accepted, extension.replace(b'test="bash run_tests.sh"\n', b''))
    assert not ci.additive_pixi_tasks_only(accepted, extension + b'\n[activation]\nscripts=["changed.sh"]\n')
    assert not ci.additive_pixi_tasks_only(b'[workspace]\nflag=1\n[tasks]\na="a"\n', b'[workspace]\nflag=true\n[tasks]\na="a"\nb="b"\n')


def test_changed_accepted_pixi_task_still_refuses_in_full_audit(monkeypatch):
    manifest, checks, jobs = packet()
    original = Path.read_bytes
    def changed_task(path):
        data = original(path)
        if path == ROOT / 'kernel/pixi.toml':
            return data.replace(b'test = "bash run_tests.sh"', b'test = "true"')
        return data
    monkeypatch.setattr(Path, 'read_bytes', changed_task)
    with pytest.raises(ValueError, match='source, lock or workflow changed'):
        ci.validate(manifest, checks, jobs)


def test_only_an_added_concurrency_block_preserves_an_accepted_workflow():
    accepted = b'name: X\non:\n  push:\n\njobs:\n  a:\n    runs-on: ubuntu-latest\n'
    block = (b'concurrency:\n  # supersede older commits\n'
             b'  group: x-${{ github.ref }}\n  cancel-in-progress: true\n\n')
    current = accepted.replace(b'jobs:', block + b'jobs:')
    assert ci.added_concurrency_block_only(accepted, current)
    # Any other change, a second block, or an accepted workflow that already had one refuses.
    assert not ci.added_concurrency_block_only(accepted, current.replace(b'ubuntu-latest', b'self-hosted'))
    assert not ci.added_concurrency_block_only(accepted, current.replace(b'jobs:', block + b'jobs:'))
    assert not ci.added_concurrency_block_only(current, current)
    assert not ci.added_concurrency_block_only(accepted, current + b'  extra: true\n')
