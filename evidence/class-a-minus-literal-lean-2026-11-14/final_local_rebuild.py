"""Local source-only rebuild, explicitly retaining cached upstream packages."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path('/workspace/scratch/7dc9ab659e7f/psc')
OUT = Path('/workspace/scratch/7dc9ab659e7f/final-local-source-rebuild')
PROJECT = ROOT / 'proof/PscVerif'
LEAN = '/workspace/scratch/f53f64a9a0d0/runtime-cache/lean-4.34.0-rc2/bin/lean'
PACKAGES = Path('/workspace/scratch/psc-next/psc/proof/PscVerif/.lake/packages')

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def sources(project):
    paths = [project / n for n in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')]
    paths += sorted(project.glob('*.lean')) + sorted((project / 'PscVerif').rglob('*.lean'))
    return {p.relative_to(project).as_posix(): digest(p) for p in paths}

if OUT.exists():
    raise SystemExit('refusing to overwrite prior receipt directory')
OUT.mkdir()
fresh = OUT / 'proof/PscVerif'
build = OUT / 'build'
before = sources(PROJECT)
for relative in before:
    target = fresh / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(PROJECT / relative, target)
assert sources(fresh) == before
encoded = json.dumps(before, sort_keys=True, separators=(',', ':')).encode()
(OUT / 'source-bindings.json').write_bytes(encoded)
modules = []
seen = set()

def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = fresh / (module.replace('.', '/') + '.lean')
    for dependency in re.findall(r'^import\s+(PscVerif\.[A-Za-z0-9_.]+)', path.read_text(), re.M):
        visit(dependency)
    modules.append(module)

for target in ('PscVerif.ClassAMinusCentralBridge', 'PscVerif.ClassAMinusDensity', 'PscVerif.ClassAMinusRootSpectrum'):
    visit(target)
env = {k: v for k, v in os.environ.items() if not k.startswith(('LEAN_', 'LAKE_', 'MATHLIB_CACHE_'))}
env['LEAN_PATH'] = ':'.join([str(build)] + [str(p / '.lake/build/lib/lean') for p in sorted(PACKAGES.iterdir()) if p.is_dir()])
receipt = {
    'scope': 'all transitive local modules rebuilt from copied source with autoImplicit=false; cached pinned upstream dependency objects; not fresh-dependency acceptance',
    'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'source_manifest_sha256': hashlib.sha256(encoded).hexdigest(),
    'source_count': len(before),
    'started_utc': now(),
    'lean_version': subprocess.check_output([LEAN, '--version'], text=True).strip(),
    'LEAN_PATH': env['LEAN_PATH'],
    'commands': [],
}
for module in modules + ['ClassAMinusLiteralEntryAudit']:
    command = [LEAN, '-DautoImplicit=false', module.replace('.', '/') + '.lean']
    if module.startswith('PscVerif.'):
        target = build / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        command += ['-o', str(target)]
    log = OUT / (module + '.log')
    started = now()
    with log.open('wb') as stream:
        result = subprocess.run(command, cwd=fresh, env=env, stdout=stream, stderr=subprocess.STDOUT)
    entry = {'module': module, 'command': command, 'cwd': str(fresh), 'started_utc': started,
             'ended_utc': now(), 'exit_code': result.returncode, 'log_sha256': digest(log)}
    receipt['commands'].append(entry)
    print(module, result.returncode, flush=True)
    (OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    if result.returncode:
        break
receipt.update(ended_utc=now(), modules_rebuilt=len([x for x in receipt['commands'] if x['module'].startswith('PscVerif.')]),
               source_unchanged=sources(PROJECT) == before == sources(fresh),
               all_commands_passed=len(receipt['commands']) == len(modules)+1 and all(x['exit_code'] == 0 for x in receipt['commands']))
(OUT / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
raise SystemExit(0 if receipt['all_commands_passed'] and receipt['source_unchanged'] else 1)
