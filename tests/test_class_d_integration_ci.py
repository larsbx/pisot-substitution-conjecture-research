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


def test_only_added_trigger_paths_preserve_an_accepted_workflow():
    accepted = (b"name: X\non:\n  pull_request:\n    paths:\n      - 'a.mojo'\n\n"
                b"jobs:\n  a:\n    runs-on: ubuntu-latest\n    steps:\n      - run: certify a\n")
    current = accepted.replace(b"      - 'a.mojo'\n", b"      - 'a.mojo'\n      - 'pins.txt'\n")
    assert ci.added_trigger_paths_only(accepted, current)
    block = b'concurrency:\n  group: x\n  cancel-in-progress: true\n\n'
    assert ci.added_trigger_paths_only(accepted, current.replace(b'jobs:', block + b'jobs:'))
    # A removed path, a changed command, an unchanged file or any other insertion refuses.
    assert not ci.added_trigger_paths_only(accepted, accepted.replace(b"      - 'a.mojo'\n", b''))
    assert not ci.added_trigger_paths_only(accepted, current.replace(b'certify a', b'true'))
    assert not ci.added_trigger_paths_only(accepted, accepted)
    assert not ci.added_trigger_paths_only(accepted, current + b'      - run: extra\n')


def test_a_plus_receipt_pin_moves_only_to_a_rebound_receipt():
    new = ('CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 '
           'boundary_lines= 51 finite_prefix_pip= 287 max_symbolic_vertices= 164')
    accepted = (b"name: X\non:\n  pull_request:\n    paths:\n      - 'a.mojo'\n\njobs:\n  a:\n    steps:\n"
                b"      - run: grep -Fx '" + ci.PLUS.encode() + b"' residual-plus.log\n")
    current = accepted.replace(ci.PLUS.encode(), new.encode())
    assert ci.rebound_receipt_pin_only(accepted, current, {new})
    # Composes with the other admitted additions.
    block = b'concurrency:\n  group: x\n  cancel-in-progress: true\n\n'
    widened = current.replace(b"      - 'a.mojo'\n", b"      - 'a.mojo'\n      - 'b.mojo'\n")
    assert ci.rebound_receipt_pin_only(accepted, widened.replace(b'jobs:', block + b'jobs:'), {new})
    # A receipt no rebind packet pins, an unchanged pin, a dropped pin or any other edit refuses.
    forged = new.replace('51', '50')
    assert not ci.rebound_receipt_pin_only(accepted, accepted.replace(ci.PLUS.encode(), forged.encode()), {new})
    assert not ci.rebound_receipt_pin_only(accepted, current, set())
    assert not ci.rebound_receipt_pin_only(accepted, accepted, {new})
    assert not ci.rebound_receipt_pin_only(accepted, current.replace(b'grep -Fx', b'true ||'), {new})
    assert not ci.rebound_receipt_pin_only(accepted, current + b'      - run: extra\n', {new})


def test_the_live_plus_workflow_pins_the_rebound_receipt_not_the_accepted_one():
    """The fit-first rebind (2026-10-30) moved the replayed plus receipt; a
    workflow still grepping the accepted 73/952 line fails on every replay."""
    from check_class_d_closure_rebind import rebound_plus_receipts
    workflow = (ROOT/'.github/workflows/class-d-positive-b-evidence.yml').read_text()
    assert ci.PLUS not in workflow
    assert sum(receipt in workflow for receipt in rebound_plus_receipts()) == 1


def test_only_appended_dev_extras_preserve_the_accepted_pyproject():
    accepted = (b'[project]\nname = "p"\ndependencies = []\n\n[project.optional-dependencies]\n'
                b'dev = ["pytest>=7.0", "pypdf==6.19.0"]\n\n[tool.pytest.ini_options]\npythonpath = ["."]\n')
    current = accepted.replace(b'"pypdf==6.19.0"]', b'"pypdf==6.19.0", "sympy==1.14.0"]')
    assert ci.appended_dev_extras_only(accepted, current)
    # A runtime dependency, a changed or reordered or dropped dev pin, a new extra,
    # a pytest-option change, or an unchanged file each refuse.
    assert not ci.appended_dev_extras_only(accepted, current.replace(b'dependencies = []', b'dependencies = ["sympy"]'))
    assert not ci.appended_dev_extras_only(accepted, current.replace(b'pypdf==6.19.0', b'pypdf==6.20.0'))
    assert not ci.appended_dev_extras_only(accepted, current.replace(b'"pytest>=7.0", "pypdf==6.19.0"', b'"pypdf==6.19.0", "pytest>=7.0"'))
    assert not ci.appended_dev_extras_only(accepted, current.replace(b'"pytest>=7.0", ', b''))
    assert not ci.appended_dev_extras_only(accepted, current.replace(b'dev = [', b'lab = ["x"]\ndev = ['))
    assert not ci.appended_dev_extras_only(accepted, current.replace(b'pythonpath = ["."]', b'pythonpath = [".", "x"]'))
    assert not ci.appended_dev_extras_only(accepted, accepted)
