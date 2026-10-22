"""Provenance refusal controls; mathematical case algebra is canonical Mojo."""
import copy
import importlib.util
import json
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('class_d_evidence',ROOT/'tools/check_class_d_assembly_evidence.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def test_complete_pinned_packet_retains_pending_acceptance():
    manifest=json.loads((ROOT/checker.PACKET/'manifest.json').read_text())
    out=checker.validate(manifest)
    assert out['provenance_valid']
    assert out['plus_import_files']==47
    assert not out['current_head_ci_accepted']
    assert not out['independent_human_review']
    bad=copy.deepcopy(manifest)
    bad['plus_source_sha256'].pop('kernel/psc/overlap_seed_patch.mojo')
    with pytest.raises(ValueError,match='import closure'):
        checker.validate(bad)
    bad=copy.deepcopy(manifest)
    bad['evidence_sha256'][checker.PLUS_LOG]='0'*64
    with pytest.raises(ValueError,match='bytes changed'):
        checker.validate(bad)
    bad=copy.deepcopy(manifest)
    bad['replay_source_sha256'].pop('kernel/psc/class_d_minus_seed_cover.mojo')
    with pytest.raises(ValueError,match='fresh replay import closure'):
        checker.validate(bad)
    bad=copy.deepcopy(manifest)
    bad['evidence_sha256'].pop(checker.PACKET+'/minus-complete.log')
    with pytest.raises(ValueError,match='evidence pin set'):
        checker.validate(bad)
    bad=copy.deepcopy(manifest)
    bad['current_head_ci_accepted']=True
    with pytest.raises(ValueError,match='does not supply'):
        checker.validate(bad)


def test_changed_source_cannot_reuse_receipts(tmp_path):
    source=tmp_path/'source.mojo'
    source.write_text('changed import')
    with pytest.raises(ValueError,match='bytes changed'):
        checker.check_hashes({'source.mojo':checker.digest(b'certified import')},tmp_path)
