#!/usr/bin/env python3
"""Fresh local source-closure replay for existing PR643 family audit."""
from pathlib import Path
import concurrent.futures, hashlib, json, os, subprocess, time

ROOT = Path('/workspace/scratch/23e6cbb0c6d9/baseline-verification/source/proof/PscVerif')
EVIDENCE = Path(__file__).resolve().parent
LEAN = Path('/workspace/scratch/0fbd89250233/c4-lean-4.34-rc2/bin/lean')
BUILD = ROOT / '.lake/build/lib/lean'
PATHS = [str(BUILD)] + [str(p / '.lake/build/lib/lean') for p in (ROOT / '.lake/packages').iterdir()
                        if (p / '.lake/build/lib/lean').is_dir()]
ENV = dict(os.environ, LEAN_PATH=':'.join(PATHS))
graph = {}

def visit(module):
    if module in graph:
        return
    source = ROOT / (module.replace('.', '/') + '.lean')
    if not source.is_file():
        return
    imports = [part for line in source.read_text().splitlines() if line.startswith('import ')
               for part in line.split()[1:]]
    graph[module] = imports
    for other in imports:
        visit(other)

visit('C4ParameterFamilyAudit')
snapshot = {m: hashlib.sha256((ROOT / (m.replace('.', '/') + '.lean')).read_bytes()).hexdigest()
            for m in graph}
(EVIDENCE / 'source-sha256.json').write_text(json.dumps(snapshot, indent=2) + '\n')
(EVIDENCE / 'import-closure.json').write_text(json.dumps(graph, indent=2) + '\n')
def compile_one(module):
    source = Path(module.replace('.', '/') + '.lean')
    output = BUILD / (module.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    argv = [str(LEAN), '-DautoImplicit=false', '-Dpp.unicode.fun=true', '-j', '2', '-o', str(output), str(source)]
    started = time.monotonic()
    result = subprocess.run(argv, cwd=ROOT, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True)
    elapsed = time.monotonic() - started
    log = EVIDENCE / (module + '.log')
    log.write_text(result.stdout)
    receipt = dict(module=module, command=argv, exit_code=result.returncode,
                   seconds=elapsed, source_sha256=snapshot[module], log=str(log))
    print(json.dumps(receipt), flush=True)
    return receipt

pending = set(graph)
done = set()
running = {}
receipts = []
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
    while pending or running:
        for module in sorted(list(pending)):
            if len(running) >= 3:
                break
            if all(n not in graph or n in done for n in graph[module]):
                running[pool.submit(compile_one, module)] = module
                pending.remove(module)
        if not running:
            raise RuntimeError('Unresolved import dependency: ' + str(pending))
        completed, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
        for future in completed:
            module = running.pop(future)
            receipt = future.result()
            receipts.append(receipt)
            (EVIDENCE / 'build-receipts.json').write_text(json.dumps(receipts, indent=2) + '\n')
            if receipt['exit_code']:
                raise RuntimeError('Compilation failed: ' + module)
            done.add(module)
for module, expected in snapshot.items():
    actual = hashlib.sha256((ROOT / (module.replace('.', '/') + '.lean')).read_bytes()).hexdigest()
    if actual != expected:
        raise RuntimeError('Source changed during replay: ' + module)
print('FRESH_CLOSURE_ACCEPTED ' + str(len(done)), flush=True)
