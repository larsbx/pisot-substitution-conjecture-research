"""Static local-import provenance audit; no graph/theorem certification.

Mojo uses the Python-style import syntax checked here. Python's tokenizer
is used only to exclude strings/comments; no Mojo program is executed by
this guard. Unknown external roots or missing source pins fail closed.
"""
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parents[1]


def import_modules(source):
    lines = source.splitlines(keepends=True)
    for token in tokenize.generate_tokens(io.StringIO(source).readline):
        if token.type in (tokenize.STRING, tokenize.COMMENT):
            for row in range(token.start[0]-1, token.end[0]):
                lo = token.start[1] if row == token.start[0]-1 else 0
                hi = token.end[1] if row == token.end[0]-1 else len(lines[row])
                blank = ''.join('\n' if c == '\n' else ' ' for c in lines[row][lo:hi])
                lines[row] = lines[row][:lo] + blank + lines[row][hi:]
    return [a or b for a,b in re.findall(
        r'^\s*(?:from\s+([\w.]+)\s+import|import\s+([\w.]+))', ''.join(lines), re.M)]


def check():
    todo = ['kernel/class_c_below_three.mojo', 'kernel/tests/test_class_c_below_three.mojo']
    seen, external = {}, set()
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        source = (ROOT / name).read_bytes()
        seen[name] = hashlib.sha256(source).hexdigest()
        for module in import_modules(source.decode()):
            path = ROOT / 'kernel' / module.replace('.', '/')
            candidates = [path.with_suffix('.mojo'), path / '__init__.mojo']
            found = next((p for p in candidates if p.is_file()), None)
            if found:
                todo.append(str(found.relative_to(ROOT)))
            else:
                external.add(module.split('.')[0])
    pins = json.loads((ROOT / 'evidence/class-c-below-three-2026-10-29/provenance.json').read_text())['sources']
    assert external == {'std', 'max'}, external
    assert all(pins.get(p) == h for p,h in seen.items()), 'missing or stale local-import pin'
    # Python initializes its package before loading overlap_graph. The
    # original record pins the explicit oracle files but omits these two
    # implicitly executed files. Bind them in the validation supplement.
    probe = r"""
import hashlib,json,pathlib,runpy,sys
root=pathlib.Path(sys.argv[1])
sys.path.insert(0,str(root/'oracles/python'))
entry=root/'oracles/python/check_class_c_below_three.py'
runpy.run_path(str(entry),run_name='__provenance_audit__')
found={str(entry.relative_to(root)):hashlib.sha256(entry.read_bytes()).hexdigest()}
for module in list(sys.modules.values()):
    filename=getattr(module,'__file__',None)
    if not filename:continue
    path=pathlib.Path(filename).resolve()
    if path.is_relative_to(root/'reference/psc_research') or path==root/'oracles/python/class_c_lower_strip.py':
        found[str(path.relative_to(root))]=hashlib.sha256(path.read_bytes()).hexdigest()
print(json.dumps(found))
"""
    python_sources = json.loads(subprocess.check_output([sys.executable, '-c', probe, str(ROOT)], text=True))
    supplemental = {p:h for p,h in python_sources.items() if p not in pins}
    assert set(supplemental) == {'reference/psc_research/__init__.py', 'reference/psc_research/bpa.py'}, supplemental
    assert all(pins[p] == h for p,h in python_sources.items() if p in pins)
    return {'local_source_count': len(seen), 'sources': dict(sorted(seen.items())),
            'observed_python_entry_import_sources': dict(sorted(python_sources.items())),
            'supplemental_implicit_python_sources': dict(sorted(supplemental.items())),
            'external_roots': sorted(external), 'missing_or_stale_pins': [],
            'scope': 'static import provenance; compiler/runtime remain trust inputs'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2, sort_keys=True))
