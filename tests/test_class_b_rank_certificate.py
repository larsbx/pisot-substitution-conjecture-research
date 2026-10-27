"""Independent oracle: the toy rank passes, each tampering refuses, the packet passes."""
import importlib.util
from pathlib import Path
import pytest
ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('b_rank', ROOT/'oracles/python/class_b_rank_certificate_oracle.py')
m = importlib.util.module_from_spec(SPEC); SPEC.loader.exec_module(m)

# Same toy as kernel/tests/test_class_b_rank_certificate.mojo: X = |k|, laps translate by 2.
TOY = """C plus 1 0 1
P 0 1 0 0 -1 -2 0 -1 0 -1 0 0
P 0 1 0 0 0 0 0 0 0 0 0 1
P 0 1 0 0 0 1 1 2 0 1 0 0
E 0 1 -1 0 -1 0 -1
E 0 2 -1 -1 -2 0 -2
E 2 1 1 0 1 0 1
E 2 0 1 0 2 1 2
"""


def test_toy_passes():
    assert m.check(m.parse(TOY)) == (3, 4)


@pytest.mark.parametrize('old,new,reason', [
    ('P 0 1 0 0 0 1 1 2 0 1 0 0', 'P 0 1 0 0 0 1 1 2 0 1 -1 0', 'does not decrease'),
    ('P 0 1 0 0 0 1 1 2 0 1 0 0', 'P 0 1 0 0 0 1 1 2 1 0 0 0', 'does not decrease'),
    ('E 2 1 1 0 1 0 1\n', '', 'uncovered'),
    ('E 2 0 1 0 2 1 2', 'E 2 0 -1 0 2 1 2', 'domain/image'),
    ('P 0 1 0 0 -1 -2 0 -1 0 -1 0 0', 'P 0 1 0 0 -1 -2 0 -1 0 -1 -2 0', 'negative potential'),
    ('P 0 1 0 0 0 0 0 0 0 0 0 1', 'P 0 1 0 0 0 0 0 0 0 0 0 0', 'uncovered'),
])
def test_tampering_refuses(old, new, reason):
    with pytest.raises(ValueError, match=reason):
        m.check(m.parse(TOY.replace(old, new)))


def test_committed_certificate_passes():
    cert = m.parse((ROOT/'evidence/class-b-rank-certificate-2026-10-27/plus-g1-r0.cert').read_text())
    assert m.check(cert) == (1787, 2302)


def test_replay_refuses_missing_edge_and_stray_vertex(tmp_path):
    cert = m.parse(TOY)
    # t=1 (q=2): wings [-3,-1] and [1,3]; one actual edge per non-target vertex.
    lab = lambda k: (0, 1, k, 3*k, -6*k)
    V = [lab(k) for k in range(-3, 4)]
    E = [lab(-1) + lab(0), lab(-2) + lab(1), lab(-3) + lab(2), lab(1) + lab(0), lab(2) + lab(-1), lab(3) + lab(-2)]
    def export(vs, es):
        p = tmp_path/'m.edges'
        p.write_text(f'M 2 {len(vs)} 3\n' + ''.join('V ' + ' '.join(map(str, v)) + ' 0\n' for v in vs)
                     + ''.join('E ' + ' '.join(map(str, e)) + '\n' for e in es))
        return p
    assert m.replay(cert, export(V, E)) == (2, 7, 6, 0)
    with pytest.raises(ValueError, match='not an actual edge'):
        m.replay(cert, export(V, E[1:]))
    with pytest.raises(ValueError, match='outside every piece'):
        m.replay(cert, export(V + [lab(4)], E))
