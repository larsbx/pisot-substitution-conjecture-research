"""Independent finite label fits reject equal-count substitutions and late drift."""
import importlib.util
from pathlib import Path
import pytest
SPEC=importlib.util.spec_from_file_location('b_labels',Path(__file__).resolve().parents[1]/'oracles/python/class_b_label_rays.py')
m=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(m)


def test_compression_exact_and_order_independent():
    raw=[(0,1,k,3*k+2,1-6*k-2,4) for k in [1,2,4]]
    rows=m.intervals(raw)
    assert rows==[(0,1,1,2,1,2),(0,1,1,2,4,4)]
    assert m.intervals(raw[::-1])==rows
    assert m.expand(rows)=={r[:5] for r in raw}


def test_same_count_wrong_labels():
    a=[(0,1,1,2,1,2)];b=[(0,1,1,2,1,3)]
    predicted=m.predict(a,b,2)
    mutated=[(0,1,1,2,2,5)]
    assert sum(r[5]-r[4]+1 for r in predicted)==sum(r[5]-r[4]+1 for r in mutated)
    assert m.expand(predicted)!=m.expand(mutated)
    assert predicted!=mutated


def test_topology_mutation_refuses():
    with pytest.raises(ValueError):m.predict([(0,1,1,2,1,2)],[(0,1,1,3,1,3)],2)


def test_count_affine_does_not_force_affine_endpoints():
    a=[(0,1,1,2,1,2)];b=[(0,1,1,2,1,3)]
    assert m.predict(a,b,2)==[(0,1,1,2,1,4)]
    # Same +1 count increment but a translated interval at the third member.
    assert m.predict(a,b,2)!=[(0,1,1,2,2,5)]


@pytest.mark.parametrize('bad',['M 1 2 1\nV 0 1 1 2 3 1\n','M 1 2 1\nV 0 1 1 2 3 1\nV 0 1 1 2 3 1\n','M 1 1 1\nV 0 1 0 0 0 1\n'])
def test_malformed_exports_refuse(tmp_path,bad):
    p=tmp_path/'bad.labels';p.write_text(bad)
    with pytest.raises(ValueError):m.read(p)


def test_real_graph_count_false_positive():
    root=Path(__file__).resolve().parents[1]/'evidence/class-b-label-rays-2026-10-23/labels'
    raw=[m.read(root/f'plus-g2-q{q}.labels')[1] for q in (9,11,13)]
    assert list(map(len,raw))==[1461,1573,1685]
    typ=(0,2,-1,-3)
    selected=[[r[4:] for r in m.intervals(v) if r[:4]==typ] for v in raw]
    assert selected==[[(-6,0)],[(-7,-3),(-1,0)],[(-8,-4),(-1,0)]]
    # A hole appears while total graph counts continue at exactly +112.
    assert (0,2,-2,-9,14) in {r[:5] for r in raw[0]}
    assert (0,2,-2,-9,14) not in {r[:5] for r in raw[1]}


def test_recorded_ray_models_have_independent_holdouts():
    import json
    p=Path(__file__).resolve().parents[1]/'evidence/class-b-label-rays-2026-10-23/carriers.json'
    report=json.loads(p.read_text())
    assert len(report)==21
    for entry in report:
        assert entry['floor']<=entry['trainmax']
        assert len(entry['holdouts'])>=2 and min(entry['holdouts'])>entry['trainmax']
        assert not entry['holdout_failures']
        assert entry['slope']==112
        assert entry['tail_partition_ok']


def test_recorded_input_manifest_is_well_formed():
    import json,re
    root=Path(__file__).resolve().parents[1]
    inputs=json.loads((root/'evidence/class-b-label-rays-2026-10-23/inputs.json').read_text())
    # Historical execution digests are immutable evidence, not a prohibition
    # on future edits to unrelated kernel modules. Replay checks fresh outputs.
    assert inputs['base_commit']=='e5b73c2ad3424bc5fe14ae9fed4e881d73a3f6da'
    assert 'kernel/class_b_label_rays.mojo' in inputs['sha256']
    for path,digest in inputs['sha256'].items():
        assert not Path(path).is_absolute() and '..' not in Path(path).parts
        assert (root/path).is_file(),path
        assert re.fullmatch('[0-9a-f]{64}',digest),path
