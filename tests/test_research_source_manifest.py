"""Historical hash checks cannot silently admit changed replay commands."""
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from check_research_source_manifest import check, workflow_metadata_only, receipt_declaration_only


def test_all_historical_manifests_survive_with_explicit_metadata_guards():
    for p in [*(ROOT/'evidence').glob('*/source-sha256.txt'), *(ROOT/'evidence').glob('*/SOURCE_SHA256SUMS')]:
        check(p)


def test_changed_replay_command_cannot_be_metadata_only():
    before=b'      - uses: actions/checkout@v4\n          sha256sum -c evidence/a/source-sha256.txt\n          replay mathematical-certificate\n'
    after=before.replace(b'- uses: actions/checkout@v4\n',b'- uses: actions/checkout@v4\n        with:\n          ref: ${{ github.event.pull_request.head.sha || github.sha }}\n').replace(b'sha256sum -c evidence/a/source-sha256.txt',b'python3 tools/check_research_source_manifest.py evidence/a/source-sha256.txt')
    assert workflow_metadata_only(before,after)
    assert not workflow_metadata_only(before,after.replace(b'replay mathematical-certificate',b'true'))
    assert not workflow_metadata_only(before,after+b'          skip-the-proof\n')


def test_receipt_addition_cannot_change_assertions():
    before=b'from mojo_smoke.claims import require_contract\nassert_true(proof())\n'
    after=before.replace(b'import require_contract',b'import require_claim, require_contract')+b'    require_claim("ClassABoundaryHittingHighGaps")\n'
    assert receipt_declaration_only(before,after)
    assert not receipt_declaration_only(before,after.replace(b'proof()',b'True'))
