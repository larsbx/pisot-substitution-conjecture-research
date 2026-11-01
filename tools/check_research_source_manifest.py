"""Preserve historical source pins while admitting exact metadata-only edits.

No archive is rewritten and no changed mathematical source is accepted.
Fail closed means refuse the run. Historical files are content-addressed by
what the original manifest pins; fresh hosted replay is still required.
"""
import hashlib
from pathlib import Path
import re
import sys
from check_class_d_integration_ci import additive_pixi_tasks_only

ROOT=Path(__file__).resolve().parents[1]
ARCHIVE=ROOT/'archive/research-integration-sources-2026-11-01'


def workflow_metadata_only(before,current):
    wanted=before.replace(b'- uses: actions/checkout@v4\n',
        b'- uses: actions/checkout@v4\n        with:\n          ref: ${{ github.event.pull_request.head.sha || github.sha }}\n')
    wanted=re.sub(rb'sha256sum -c (evidence/[^\s]+/source-sha256.txt)',
        rb'python3 tools/check_research_source_manifest.py \1',wanted)
    wanted=re.sub(rb'sha256sum -c (evidence/[^\s]+/SOURCE_SHA256SUMS)',
        rb'python3 tools/check_research_source_manifest.py \1',wanted)
    return wanted!=before and current==wanted


def receipt_declaration_only(before,current):
    wanted=before.replace(b'from mojo_smoke.claims import require_contract\n',
        b'from mojo_smoke.claims import require_claim, require_contract\n')
    wanted+=b'    require_claim("ClassABoundaryHittingHighGaps")\n'
    return current==wanted


def check(manifest):
    known={hashlib.sha256(p.read_bytes()).hexdigest():p.read_bytes()
           for p in ARCHIVE.iterdir() if p.is_file() and p.name!='SHA256SUMS'}
    checked=0;admitted=[]
    for line in manifest.read_text().splitlines():
        if not line.strip():continue
        digest,path=line.split(maxsplit=1);path=path.lstrip('*')
        data=(ROOT/path).read_bytes();checked+=1
        if hashlib.sha256(data).hexdigest()==digest:continue
        assert digest in known,('historical source unavailable',path)
        before=known[digest]
        good=(path=='kernel/pixi.toml' and additive_pixi_tasks_only(before,data))
        good=good or (path.startswith('.github/workflows/') and workflow_metadata_only(before,data))
        good=good or (path=='kernel/tests/test_class_a_gap_theorem.mojo' and receipt_declaration_only(before,data))
        assert good,('changed mathematical source or unrecognized metadata edit',path)
        admitted.append(path)
    return {'manifest':str(manifest.relative_to(ROOT)),'checked':checked,'metadata_only_changes':admitted}


if __name__=='__main__':
    import json
    print(json.dumps(check((ROOT/sys.argv[1]).resolve()),indent=2,sort_keys=True))
