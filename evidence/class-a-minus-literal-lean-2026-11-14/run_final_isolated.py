"""Run the unchanged source-isolated gate using disk-backed temporary storage."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path('/workspace/scratch/7dc9ab659e7f/psc')
BASE = ROOT.parent
LOG = BASE / 'fresh-isolated-attempt3.log'
RECEIPT = BASE / 'fresh-isolated-attempt3.json'
TMP = BASE / 'fresh-isolated-disk'

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot():
    project = ROOT / 'proof/PscVerif'
    files = [ROOT / p for p in ('tools/check_class_a_literal_entry.sh', '.github/workflows/class-a-literal-entry.yml', 'proof/proof-bank.json', 'docs/proof-bank.md')]
    files += [project / p for p in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')]
    files += sorted(project.glob('*.lean')) + sorted((project / 'PscVerif').rglob('*.lean'))
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in files}

if LOG.exists() or RECEIPT.exists():
    raise SystemExit('refusing to overwrite a prior isolated attempt')
TMP.mkdir(exist_ok=True)
env = os.environ.copy()
env['PATH'] = '/home/agent/.elan/bin:' + env['PATH']
env['TMPDIR'] = str(TMP)
command = ['./tools/check_class_a_literal_entry.sh']
receipt = {'scope': 'fresh copied sources, fresh pinned dependency clones and fixed upstream Mathlib cache; disk-backed TMPDIR; no local artifact reuse',
           'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
           'command': command, 'cwd': str(ROOT), 'TMPDIR': str(TMP), 'started_utc': now(), 'source_before': snapshot()}
RECEIPT.write_text(json.dumps(receipt, indent=2) + '\n')
with LOG.open('wb') as stream:
    try:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=1200)
        receipt['exit_code'] = result.returncode
    except subprocess.TimeoutExpired:
        receipt['exit_code'] = None
        receipt['timeout_seconds'] = 1200
receipt['ended_utc'] = now()
receipt['source_after'] = snapshot()
receipt['source_unchanged'] = receipt['source_before'] == receipt['source_after']
receipt['log_sha256'] = digest(LOG)
RECEIPT.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ('source_before', 'source_after')}, indent=2), flush=True)
raise SystemExit(0 if receipt['exit_code'] == 0 and receipt['source_unchanged'] else 1)
