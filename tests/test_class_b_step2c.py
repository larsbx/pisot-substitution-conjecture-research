"""Independent exact geometry, finite reconstruction, and adversarial controls."""
import importlib.util
import sys
from pathlib import Path
import pytest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'oracles/python'))
import class_b_core_exact as core
import class_b_middle_geometry as middle
import class_b_middle_tables as tables


def test_exact_core_matches_native_calibrations():
    for branch,g,q,n in [('plus',16,98,2299),('minus',12,78,2275)]:
        path=ROOT/f'evidence/class-b-step2c-2026-10-27/core-labels/{branch}-g{g}-q{q}.labels'
        assert core.check(path,branch,g,q)['states']==n


def test_invalid_core_and_incomplete_closure_refuse():
    with pytest.raises(ValueError,match='outside open'):
        core.ExactMember('plus',16,10)
    with pytest.raises(ValueError,match='cap'):
        core.ExactMember('minus',12,78).build(cap=1)
    adj={(0,0,(1,0,0)):()}
    with pytest.raises(ValueError,match='without target'):
        core.depths(adj)


def test_rational_sign_checker_rejects_interior_and_included_face_zeros():
    side={}
    # 1-2x changes sign in the interior; y-1 vanishes on included y=1.
    with pytest.raises(ValueError):
        middle.direct_sign(middle.poly(((0,0),1),((0,1),-8)),side,4,16,4)
    with pytest.raises(ValueError):
        middle.direct_sign(middle.poly(((1,0),16),((0,1),-1)),side,4,16,4)
    assert middle.direct_sign(middle.poly(((1,0),1)),side,4,16)==1


def test_middle_candidates_reproduce_from_native_exports():
    entries=tables.candidates(tables.PACKET/'core-labels')
    assert all(len(e['rows'])==529 for e in entries)
    assert tables.render(entries)==tables.OUT.read_text()


def test_invalid_middle_carrier_is_not_strict():
    entries=tables.candidates(tables.PACKET/'core-labels')
    e=entries[0]
    row=e['rows'][0]
    rh=middle.poly(((1,0),2))
    # Replace k=-2 by k=+100 on the first (x,x,u=-3,d=-6) slice.
    signs=[middle.sign(p,1,4,16) for p in middle.margins(1,*row[:4],0,100,rh)]
    assert signs != [1,1]


def test_uniform_descent_and_exception_use_actual_occurrences():
    import json
    from class_b_middle_descent import descent
    from class_b_ray_certificate import certify,Ray
    entries=tables.candidates(tables.PACKET/'core-labels')
    pots=json.loads((tables.PACKET/'middle-potentials.json').read_text())
    plus=descent(entries[0],pots[0],16)
    minus=descent(entries[1],pots[1],13)
    assert (plus['descent_intervals'],minus['descent_intervals'])==(1468,1456)
    with pytest.raises(ValueError,match='row=0'):
        descent(entries[1],pots[1],12)
    for e,p,g0 in [(entries[0],pots[0],16),(entries[1],pots[1],13)]:
        zero={**p,'potential':[r[:5]+[0] for r in p['potential']]}
        with pytest.raises(ValueError,match='NO_DESCENT'):
            descent(e,zero,g0)
    rows=[r[:4]+[r[5],r[6],r[9],r[10]] for r in entries[1]['rows']]
    pot={tuple(r[:5]):r[5] for r in pots[1]['potential']}
    assert certify(Ray(-1,12,6),54,rows,pot)['descent_intervals']==1456


def test_potential_table_render_is_current():
    import json
    from class_b_middle_potentials import render
    assert render(json.loads((tables.PACKET/'middle-potentials.json').read_text()))==(ROOT/'kernel/psc/class_b_middle_potential_tables.mojo').read_text()


def test_middle_carrier_does_not_extend_to_boundary_residues():
    import json
    from class_b_middle_closure import Geometry
    entries=tables.candidates(tables.PACKET/'core-labels')
    controls=json.loads((tables.PACKET/'negative-controls/middle-outside-regime.json').read_text())
    assert len(controls)==2
    for control in controls:
        m=core.ExactMember(control['branch'],control['g'],control['q'])
        parent=(*control['parent'][:2],tuple(control['parent'][2:]))
        child=(*control['child'][:2],tuple(control['child'][2:]))
        assert m.strict(parent) and child in m.children(parent)
        entry=next(e for e in entries if e['branch']==control['branch'])
        rows=Geometry(entry).rows;l=control['l']
        def inside(v):
            t,b,(k,c,y)=v;u=3*k+c+y;d=c-3*k
            return any(r[:4]==[t,b,u,d] and r[4]*l+r[5]<=k<=r[6]*l+r[7] for r in rows)
        assert inside(parent) and not inside(child)
