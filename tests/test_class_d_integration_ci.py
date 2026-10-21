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
