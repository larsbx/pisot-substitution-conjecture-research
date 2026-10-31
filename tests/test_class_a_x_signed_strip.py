"""Independent signed-strip replay and refusal of overstrong transfers."""
import json
from pathlib import Path
import runpy
import pytest

ROOT=Path(__file__).resolve().parents[1]
M=runpy.run_path(str(ROOT/'oracles/python/class_a_x_signed_strip.py'))
S=runpy.run_path(str(ROOT/'oracles/python/class_a_x_signed_strip_symbolic.py'))
PACKET=ROOT/'evidence/class-a-x-signed-strip-2026-10-31'

def test_exact_paths_match_receipt_and_completed_graph_profile():
 actual=dict(paths=M['replay'](),finite_profile=M['profile'](),controls=M['controls']())
 assert json.loads(json.dumps(actual))==json.loads((PACKET/'probe.json').read_text())
 assert actual['paths']['oriented_paths']==1464
 assert actual['paths']['selected_edges']==46462
 assert actual['paths']['cases']==dict(cap0=60,cap1=246,high=248,near=58,
   positive=852,two_edge_pump_iterations=4412)
 assert len(actual['finite_profile']['members'])==22
 assert actual['paths']['universal_x_productivity'] is False

def test_coefficient_certificates_and_mutations():
 assert S['certify']()==json.loads((PACKET/'symbolic.json').read_text())
 with pytest.raises(ValueError):S['zero'](S['r']*(S['r']-1))
 with pytest.raises(ValueError):S['nonnegative'](1-S['u'])
 # A polynomially consistent type-blind correction must still be refused.
 with pytest.raises(ValueError):
  S['edge'](S['Q'](-S['r']),'FIRST',0,'LAST',S['A']+1,S['P'](-S['r']-1),
            {S['t']:S['K']*S['r']+1})

def test_all_walls_lowest_faces_and_reversed_occurrences():
 for k,t,p,kind in [(0,0,-1,'near'),(0,0,-2,'high'),(0,1,-1,'cap0'),
                    (0,2,-1,'cap1'),(0,0,0,'positive'),(1,1,-1,'near'),
                    (0,8,-1,'cap1')]:
  g=M['G'](-1,k,t)
  packet,pumps,actual=M['path'](k,t,p)
  assert actual==kind
  if (k,t,p)==(0,8,-1):assert pumps==6
  M['M']['BASE']['verify_path'](g,packet)
  flipped,_,_=M['path'](k,t,p,True)
  assert flipped==[(M['rev'](a),j,i,M['rev'](b)) for a,i,j,b in packet]
  M['M']['BASE']['verify_path'](g,flipped)

def test_occurrence_and_domain_negative_controls():
 M['controls']()
 for k,t,p in [(-1,0,0),(0,-1,0),(0,0,3),(0,0,-3)]:
  with pytest.raises(ValueError):M['path'](k,t,p)
 with pytest.raises(ValueError):M['path'](0,8,-1,step_cap=2)
 g=M['G'](-1,0,2);packet,_,_=M['path'](0,2,-1)
 wrong=[(M['rev'](a),i,j,M['rev'](b)) for a,i,j,b in packet]
 with pytest.raises(ValueError):M['M']['BASE']['verify_path'](g,wrong)
 bad=list(packet);a,i,j,b=bad[2];bad[2]=(a,i,j,(*b[:4],b[4]+1))
 with pytest.raises(ValueError):M['M']['BASE']['verify_path'](g,bad)
