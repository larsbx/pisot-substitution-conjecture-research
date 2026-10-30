"""A rebind admits exactly the pinned, justified bytes and nothing else."""
import gzip
import json
from pathlib import Path
import shutil
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import check_class_d_closure_rebind as rebind


@pytest.fixture
def packet(tmp_path):
    copy = tmp_path/'packet'
    shutil.copytree(rebind.PACKET, copy)
    return copy


def edit(packet, change):
    manifest = json.loads((packet/'manifest.json').read_text())
    change(manifest)
    (packet/'manifest.json').write_text(json.dumps(manifest))


def test_the_rebind_admits_the_driver_by_native_replay_and_the_checker_as_a_tool():
    paths = json.loads((rebind.PACKET/'manifest.json').read_text())['paths']
    assert paths['kernel/symbolic_line_certificate.mojo']['kind'] == 'native-replay'
    assert paths['tools/check_class_d_assembly_evidence.py']['kind'] == 'provenance-tool'
    assert set(rebind.validate()) == set(paths)
    for path, digest in rebind.validate().items():
        assert rebind.rebound(path, digest)
        assert not rebind.rebound(path, '0'*64)
    assert not rebind.rebound('kernel/pixi.lock', rebind.sha256((ROOT/'kernel/pixi.lock').read_bytes()))


@pytest.mark.parametrize('change, message', [
    (lambda m: m.update(independent_human_review=True), 'review status'),
    (lambda m: m.update(accepted_head='0'*40), 'accepted head'),
    (lambda m: m.update(rebind_head='0'*40), 'does not contain the rebind head'),
    (lambda m: m['paths']['kernel/symbolic_line_certificate.mojo'].update(sha256='0'*64), 'pinned bytes'),
    (lambda m: m['paths']['kernel/symbolic_line_certificate.mojo'].update(kind='provenance-tool'), 'not a provenance tool'),
    (lambda m: m['paths']['tools/check_class_d_assembly_evidence.py'].update(kind='native-replay'), 'not exercised'),
    (lambda m: m['paths'].update({'kernel/pixi.lock': dict(kind='native-replay', sha256='0'*64)}), 'not exercised'),
    (lambda m: m.update(paths={}), 'empty rebind'),
])
def test_a_tampered_manifest_refuses(packet, change, message):
    edit(packet, change)
    with pytest.raises(ValueError, match=message):
        rebind.validate(packet)


def test_a_failed_or_skipped_replay_refuses(packet):
    jobs = json.loads((packet/'jobs.json').read_text())
    next(s for s in jobs[0]['steps'] if s['name'] == 'Certify all plus chambers and boundary strips')['conclusion'] = 'skipped'
    (packet/'jobs.json').write_text(json.dumps(jobs))
    with pytest.raises(ValueError, match='skipped or failed'):
        rebind.validate(packet)
    jobs[0]['conclusion'] = 'failure'
    (packet/'jobs.json').write_text(json.dumps(jobs))
    with pytest.raises(ValueError, match='did not pass'):
        rebind.validate(packet)


def test_a_log_without_the_native_receipt_refuses(packet):
    log = next(packet.glob('*.log.gz'))
    raw = gzip.decompress(log.read_bytes()).replace(b'CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED', b'echo CERTIFIED')
    log.write_bytes(gzip.compress(raw))
    with pytest.raises(ValueError, match='raw job log changed'):
        rebind.validate(packet)
    edit(packet, lambda m: m['log_sha256'].update({log.name[:-3]: rebind.sha256(raw)}))
    with pytest.raises(ValueError, match='native plus-chamber receipt'):
        rebind.validate(packet)


def test_a_rebound_file_edited_again_refuses(packet, monkeypatch):
    original = Path.read_bytes
    def edited(path):
        data = original(path)
        return data + b'\n# later edit\n' if path == ROOT/'kernel/symbolic_line_certificate.mojo' else data
    monkeypatch.setattr(Path, 'read_bytes', edited)
    with pytest.raises(ValueError, match='changed again'):
        rebind.validate(packet)


V2 = rebind.PACKETS[1]


@pytest.fixture
def packet_v2(tmp_path):
    copy = tmp_path/'packet-v2'
    shutil.copytree(V2, copy)
    return copy


def test_the_fit_first_rebind_admits_the_engine_by_a_head_replay():
    paths = json.loads((V2/'manifest.json').read_text())['paths']
    assert set(paths) == {'kernel/psc/symbolic_line.mojo'}
    assert paths['kernel/psc/symbolic_line.mojo']['kind'] == 'native-replay'
    assert set(rebind.validate(V2)) == set(paths)
    admitted = rebind._rebound()
    assert set(admitted) == set(paths) | set(rebind.validate())
    assert rebind.rebound('kernel/psc/symbolic_line.mojo', paths['kernel/psc/symbolic_line.mojo']['sha256'])


@pytest.mark.parametrize('change, message', [
    (lambda m: m.update(plus_receipt='CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 5 explicit_lines= 6 '
                                     'boundary_lines= 51 finite_prefix_pip= 287 max_symbolic_vertices= 164'), 'wrong shape'),
    (lambda m: m.update(plus_receipt=m['plus_receipt'].replace('287', '288')), 'native plus-chamber receipt'),
    (lambda m: m.update(rebind_head='0'*40), 'not a commit'),
    (lambda m: m.update(format='class-d-closure-rebind-v3'), 'wrong rebind format'),
])
def test_a_tampered_v2_manifest_refuses(packet_v2, change, message):
    edit(packet_v2, change)
    with pytest.raises(ValueError, match=message):
        rebind.validate(packet_v2)


def test_a_v2_replay_on_another_head_refuses(packet_v2):
    jobs = json.loads((packet_v2/'jobs.json').read_text())
    jobs[0]['head_sha'] = rebind.ACCEPTED_HEAD
    (packet_v2/'jobs.json').write_text(json.dumps(jobs))
    with pytest.raises(ValueError, match='did not pass at the rebind head'):
        rebind.validate(packet_v2)


def test_a_later_packet_cannot_re_admit_a_rebound_path(monkeypatch):
    monkeypatch.setattr(rebind, 'PACKETS', (rebind.PACKET, rebind.PACKET))
    rebind._rebound.cache_clear()
    try:
        with pytest.raises(ValueError, match='re-admits'):
            rebind._rebound()
    finally:
        monkeypatch.undo()
        rebind._rebound.cache_clear()
