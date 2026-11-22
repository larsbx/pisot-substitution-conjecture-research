#!/usr/bin/env python3
"""Recompile the seven local candidate modules against the fresh PR643 closure."""
from pathlib import Path
import hashlib, json, os, subprocess, time

ROOT = Path('/workspace/scratch/23e6cbb0c6d9/psc-zero-fibre/proof/PscVerif')
EVIDENCE = Path(__file__).resolve().parent
BUILD = EVIDENCE / 'candidate-olean'
BASE_BUILD = EVIDENCE.parent / 'source/proof/PscVerif/.lake/build/lib/lean'
# Lean resolves the PscVerif namespace in one search root. Link the freshly
# rebuilt baseline artifacts into this otherwise-new candidate output root.
BUILD.mkdir(parents=True, exist_ok=True)
for dependency in BASE_BUILD.rglob('*'):
    target = BUILD / dependency.relative_to(BASE_BUILD)
    if dependency.is_dir():
        target.mkdir(parents=True, exist_ok=True)
    elif not target.exists():
        target.symlink_to(dependency)
LEAN = '/workspace/scratch/0fbd89250233/c4-lean-4.34-rc2/bin/lean'
PATHS = [str(BUILD), str(BASE_BUILD)] + [str(p / '.lake/build/lib/lean') for p in (ROOT / '.lake/packages').iterdir()
                        if (p / '.lake/build/lib/lean').is_dir()]
ENV = dict(os.environ, LEAN_PATH=':'.join(PATHS))
MODULES = ['PscVerif.PeriodicPartnerProximal', 'PscVerif.PeriodicPartnerPeriodicZero',
           'PscVerif.C4ParameterFamilyZeroFibreControls', 'PscVerif.C4ParameterFamilyInteriorSeed',
           'PscVerif.C4ParameterFamilyZeroFibreWitnesses', 'PscVerif.C4ParameterFamilyInteriorProximal',
           'PscVerif.C4ParameterFamilyInteriorZero', 'C4ZeroFibreWitnessAudit']
snapshot = {m: hashlib.sha256((ROOT / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest()
            for m in MODULES}
(EVIDENCE / 'candidate-source-sha256.json').write_text(json.dumps(snapshot, indent=2) + '\n')
receipts = []
for module in MODULES:
    source = Path(module.replace('.', '/') + '.lean')
    output = BUILD / (module.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    argv = [LEAN, '-DautoImplicit=false', '-Dpp.unicode.fun=true', '-j', '2', '-o', str(output), str(source)]
    start = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, env=ENV, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = EVIDENCE / ('candidate-' + module + '.log')
    log.write_text(result.stdout)
    receipt = dict(module=module, command=argv, exit_code=result.returncode,
                   seconds=time.monotonic() - start, source_sha256=snapshot[module], log=str(log))
    receipts.append(receipt)
    (EVIDENCE / 'candidate-build-receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
for module, digest in snapshot.items():
    assert hashlib.sha256((ROOT / (module.replace('.', '/') + '.lean')).read_bytes()).hexdigest() == digest, module
print('CANDIDATE_CLOSURE_ACCEPTED 8', flush=True)
