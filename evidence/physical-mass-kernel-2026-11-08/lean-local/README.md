# Local Lean physical-mass receipt

This directory records the successful local development compile and compiled-declaration audit of `proof/PscVerif/PscVerif/PhysicalMass.lean`, identified by SHA-256 `6578043c87ca7da4be96673630ae5d2d2e2356a681b1b2401c39bd9e9b036a36`. It is source-scoped evidence, not hosted exact-revision acceptance.

## Result

- Compile exit status: **0**, with an empty `compile.log` (no warnings or errors).
- Compiled audit exit status: **0**.
- Completion: `PSC_AUDIT_COMPLETE 65 40`.
- Authored, explicitly named source `theorem` statements: **26**.
- Compiled theorem declarations: **40**, including **14 generated theorem declarations**.
- Total compiled declarations: **65**. The total includes definitions, structure machinery, and generated helpers.
- Allowed axiom dependencies: `propext`, `Classical.choice`, `Quot.sound`. The audit rejects local axioms and any dependency outside that set.

`lean-receipt.json` records the exact source, compiler, shim, harness, and log hashes; version output; command argument vectors; environment overrides; and all 26 named source theorems. The source file has not been changed since the successful compile.

## Actual compilation and audit invocation

The successful run used Python `subprocess.run` from `/workspace/scratch/3ac1674060b1/psc`, inheriting the ambient environment and overriding only `LD_PRELOAD` and `LEAN_PATH`. These are the actual subprocess calls, with the same environment construction:

```python
import os
import subprocess
from pathlib import Path

base = Path('/tmp/psc-nov8-tools')
artifacts = Path('/tmp/psc-physical-mass-audit')
(artifacts / 'PscVerif').mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['LD_PRELOAD'] = str(base / 'proc.so')
env['LEAN_PATH'] = ':'.join(
    [str(artifacts)] +
    [str(p / '.lake/build/lib/lean')
     for p in (base / 'lake/packages').iterdir() if p.is_dir()]
)
lean = str(base / 'lean-4.34.0-rc2-linux/bin/lean')
source = Path('proof/PscVerif/PscVerif/PhysicalMass.lean')
compiled = subprocess.run(
    [lean, '-DautoImplicit=false', '-o',
     str(artifacts / 'PscVerif/PhysicalMass.olean'), str(source)],
    env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
(artifacts / 'compile.log').write_text(compiled.stdout)
assert compiled.returncode == 0

audit = Path('proof/PscVerif/ProofBankAudit.lean').read_text().replace(
    'import PscVerif\n', 'import PscVerif.PhysicalMass\n'
)
auditpath = artifacts / 'PhysicalMassAudit.lean'
auditpath.write_text(audit)
audited = subprocess.run(
    [lean, str(auditpath)], env=env, text=True,
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
)
(artifacts / 'audit.log').write_text(audited.stdout)
assert audited.returncode == 0
```

The archived `PhysicalMassAudit.lean` is the exact harness from this run. It applies the repository's generic audit to the compiled module, including generated declarations; it does not limit its inspection to a hand-picked theorem list. For replay against a later checkout, copy this archived harness rather than silently accepting changes to the generic audit.

The local paths and complete expanded `LEAN_PATH` are recorded in `lean-receipt.json`. They describe this environment and are not portable installation instructions. The normal project reproduction path is the repository's pinned `tools/setup_lean.sh` and isolated `tools/check_lean.sh`, as used by hosted CI.

## Versions and local trust boundary

The compiler reports Lean **4.34.0-rc2**, release commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`, on `x86_64-unknown-linux-gnu`. The toolchain pin is `leanprover/lean4:v4.34.0-rc2`. The Mathlib checkout reports `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`, matching the repository pin, and its tracked worktree was clean when this receipt was recorded. The exact outputs are archived.

This run reused pre-existing local compiled dependency caches. This receipt does not establish that every dependency `.olean` was rebuilt from, or separately authenticated against, the recorded source revision. The PhysicalMass module itself was freshly compiled before its compiled audit. This local result does not replace the isolated hosted build and full proof-bank audit.

The local launcher otherwise failed to locate its application. `LD_PRELOAD=/tmp/psc-nov8-tools/proc.so` applied a small compatibility shim which changes only `readlink` calls for the process's own `/proc/<pid>/exe` path to `/proc/self/exe`. Its exact source is archived as `local-proc.c`, and both source and shared-library hashes appear in the receipt. Hosted acceptance must use the standard toolchain setup without this shim.

No concrete PR #515 graph or mass packet is instantiated by this module. Authentication of complete occurrence multiplicities, exact physical masses, and the geometric overlap recurrence remain separate refinement obligations. No C4, PSC, uniform strict-PIP, or complete-branch acceptance follows from this local receipt.
