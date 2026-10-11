"""Replay provenance guards must refuse mismatches even under python -O."""
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize('mode,message', [('ast', 'unrelated semantic change'),
                                         ('corpus', 'ordered warm-up corpus mismatch')])
def test_optimized_replay_refuses_corruption(mode, message):
    code = '''
import ast
import runpy
import subprocess
from pathlib import Path
ns = runpy.run_path('oracles/python/pip_mul_benchmark.py')
mode = MODE

def corrupt(*args, **kwargs):
    source = Path('reference/psc_research/pip_screen.py').read_text()
    if mode == 'ast':
        return source + '\\ndef unrelated(): return 0\\n'
    tree = ast.parse(source)
    tree.body = [ast.parse('def mul(A,B): return [[0]*3 for _ in range(3)]').body[0]
                 if isinstance(n, ast.FunctionDef) and n.name == 'mul' else n
                 for n in tree.body]
    return ast.unparse(tree)
subprocess.check_output = corrupt
ns['main']()
'''.replace('MODE', repr(mode))
    result = subprocess.run([sys.executable, '-O', '-c', code], cwd=ROOT,
                            text=True, capture_output=True)
    assert result.returncode != 0
    assert message in result.stderr
    assert not result.stdout
