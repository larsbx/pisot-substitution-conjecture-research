"""Typed cross-strip entrances: exact literal replay and boundary refusals."""
import json
from pathlib import Path
import runpy
import pytest

ROOT=Path(__file__).resolve().parents[1]
M=runpy.run_path(str(ROOT/'oracles/python/class_a_x_cross_strip.py'))
S=runpy.run_path(str(ROOT/'oracles/python/class_a_x_cross_strip_symbolic.py'))
PACKET=ROOT/'evidence/class-a-x-cross-strip-2026-10-31'


def test_full_independent_replay_and_finite_coverage():
 actual=dict(paths=M['replay'](),finite_profile=M['profile'](),
             endpoint_control=M['endpoint_control']())
 assert json.loads(json.dumps(actual))==json.loads((PACKET/'probe.json').read_text())
 r=actual['paths']
 assert (r['specimens'],r['oriented_paths'],r['selected_edges'])==(120,7574,243888)
 assert (r['native_entrance_checks'],r['native_shared_suffix_checks'])==(7574,42234)
 assert r['native_total_indexed_checks']==49808
 row=next(v for v in actual['finite_profile']['members'] if (v['k'],v['t'])==(0,8))
 assert row['reached_oriented_sources']==184
 assert row['reached_sources_outside_previous_local_path_carrier']==142
 assert row['finite_u1_xy_sources_outside_sector']
 assert row['parameter_uniform_x_coverage_proved'] is False


def test_unbounded_typed_shear_and_guard_certificates():
 assert S['certify']()==json.loads((PACKET/'symbolic.json').read_text())
 with pytest.raises(ValueError):S['zero'](S['m']*(S['m']-1))
 with pytest.raises(ValueError):S['certificate'](0,{'one':1},{'one':-1})
 with pytest.raises(ValueError):S['certificate'](1,{'one':1},{'one':2})
 # Wrong-sign offset shear does not cancel a positive RUN-index shift.
 wrong=S['transport'](0,2,(S['x'],S['c']+S['m'],S['y']+S['m']),
                      'RUN',S['i']+S['m'],'FIRST',0)
 base=S['transport'](0,2,(S['x'],S['c'],S['y']),'RUN',S['i'],'FIRST',0)
 with pytest.raises(ValueError):S['zero'](wrong[2][0]-base[2][0])


def test_first_last_run_and_low_parameter_controls():
 g=M['Geometry'](-1,0,0)
 lower=M['path'](0,0,2,-3);upper=M['path'](0,0,1,3)
 assert lower[0][1]==1
 assert upper[0][1]==len(g.words[0])-2==8  # final RUN y, not LAST x
 assert g.child(*[upper[0][0],upper[0][1],upper[0][2]])==upper[0][3]
 zero=M['path'](0,0,0,-3)
 assert zero[0][1]==1 and zero[0][3]==M['T']['D'] and len(zero)==2
 c=M['endpoint_control']()
 assert c['source']==(0,2,2,2,-7)
 assert c['actual_first_child']==(0,0,-1,-5,8)
 assert c['both_formal_labels_strict'] is True
 assert len(c['x_to_source_path'])==5
 for k,t,p,s in [(0,2,-2,1),(0,3,-2,-3),(0,8,-1,-3),(32,0,1,3)]:
  M['BASE']['verify_path'](M['Geometry'](-1,k,t),M['path'](k,t,p,s))


def test_domain_full_offset_and_reversal_controls():
 for k,t,p,s in [(-1,0,0,0),(0,-1,0,0),(0,0,0,-4),(0,0,0,4),
                 (0,0,3,0),(0,0,-1,0),(0,2,-1,2)]:
  with pytest.raises(ValueError):M['path'](k,t,p,s)
 with pytest.raises(ValueError):M['path'](0,8,-1,-3,step_cap=2)
 g=M['Geometry'](-1,0,0);packet=M['path'](0,0,1,-3)
 rev=M['path'](0,0,1,-3,True)
 assert rev==[(M['reverse'](a),j,i,M['reverse'](b)) for a,i,j,b in packet]
 M['BASE']['verify_path'](g,rev)
 wrong=[(M['reverse'](a),i,j,M['reverse'](b)) for a,i,j,b in packet]
 with pytest.raises(ValueError):M['BASE']['verify_path'](g,wrong)
 bad=list(packet);a,i,j,b=bad[0];bad[0]=(a,i,j,(*b[:4],b[4]+1))
 with pytest.raises(ValueError):M['BASE']['verify_path'](g,bad)
