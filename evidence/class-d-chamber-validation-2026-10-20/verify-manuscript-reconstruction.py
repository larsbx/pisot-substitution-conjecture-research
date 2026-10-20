"""Verify, without writing the manuscript, the reused byte-level repair."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
r = json.loads((HERE/'manuscript-reconstruction.json').read_text())
before = subprocess.check_output(['git','show','e17aef51f6773a97d04201d73b77a4354651b5bb:'+r['path']],cwd=ROOT)
after = (ROOT/r['path']).read_bytes()
sha = lambda data: hashlib.sha256(data).hexdigest()
assert sha(before) == r['before_sha256']
assert sha(after) == r['after_sha256']
start = next(i for i in range(min(len(before),len(after))) if before[i] != after[i])
block = before[start:start+r['repeated_block_bytes']]
assert sha(block) == r['repeated_block_sha256']
assert before.count(block) == 3
assert before.replace(block,b"$'",2) == after
assert after.count(block) == 1
print('Verified: exactly two duplicate-tail injections replaced; third copy retained; corrected source hash matches PR #290.')
