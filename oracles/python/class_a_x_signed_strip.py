"""Independent literal-word replay of the signed unit-strip selected paths.

No graph coverage theorem is assumed. The finite profile checks, but does
not extrapolate, the signed interval in the completed parent certificates.
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import runpy

M=runpy.run_path(str(Path(__file__).with_name('class_a_x_transfer_plane.py')))
G=M['Geometry'];rev=M['reverse'];pos=M['unit_path']
def P(p):return (0,2,p,3*p+1,-6*p)
def Q(p):return (2,0,-p,1-3*p,6*p-3)
def Z(R,s,u):return (0,2,R,3*R+s,u-s-6*R)
def H(R,u):return (0,0,-R,1-3*R,6*R+u-1)
def path(k,t,p,flip=False,step_cap=10000):
 if min(k,t)<0:raise ValueError('negative parameter')
 K=k+1;n=k+t+3;d=k+2*t+5;A=n+d;D=(n-1)//K
 if abs(p)>D or step_cap<1:
  raise ValueError('outside signed strip domain or path budget')
 if p>=0:
  out,pump,kind=pos(k,t,p),0,'positive'
  if len(out)>step_cap:raise ValueError('path budget exhausted')
  if flip:out=[(rev(a),j,i,rev(b)) for a,i,j,b in out]
  return out,pump,kind
 r=-p;out=[];pump=0
 while K*r<=t-2:
  a=K*r;out.extend([(P(-r),n+4+a,0,Q(-r)),(Q(-r),0,2*n+4+a,P(-r-1))]);r+=1;pump+=1
 a=K*r;R=r+1
 if a==t-1:
  out.extend([(P(-r),n+4+a,0,Q(-r)),(Q(-r),0,A+1,H(R,1)),(H(R,1),A+1,t+4,Z(R+1,-2,2)),(Z(R+1,-2,2),t+8,0,rev(P(R)))]);out+=pos(k,t,R,True);kind='cap1'
 elif a==t:
  out.extend([(P(-r),n+4+a,0,Q(-r)),(Q(-r),0,A+1,H(R,0)),(H(R,0),A+1,d+3,Z(R,0,1)),(Z(R,0,1),5,0,Q(R))]);out+=pos(k,t,R)[1:];kind='cap0'
 elif a==t+1:
  out.extend([(P(-r),A+1,n-1,Z(R,-2,1)),(Z(R,-2,1),2,0,Q(R))]);out+=pos(k,t,R)[1:];kind='near'
 else:
  assert a>=t+2
  out.extend([(P(-r),A+1,d-a-1,Z(R,-2,2)),(Z(R,-2,2),2*n+3-K*R,0,rev(P(r)))]);out+=pos(k,t,r,True);kind='high'
 if len(out)>4*D+6:raise AssertionError('proved path bound violated')
 if len(out)>step_cap:raise ValueError('path budget exhausted')
 if flip:out=[(rev(a),j,i,rev(b)) for a,i,j,b in out]
 return out,pump,kind

def replay():
 counts=Counter();edges=0;paths=0;rows=[]
 for k,t in M['MEMBERS']:
  g=G(-1,k,t);D=(g.n-1)//(k+1)
  count=selected=pumps_total=longest=0
  for p in range(-D,D+1):
   for flip in (False,True):
    packet,pumps,kind=path(k,t,p,flip)
    M['BASE']['verify_path'](g,packet)
    counts[kind]+=1;counts['two_edge_pump_iterations']+=pumps
    selected+=len(packet);count+=1;pumps_total+=pumps;longest=max(longest,len(packet))
  rows.append(dict(k=k,t=t,radius=D,oriented_paths=count,selected_edges=selected,
    two_edge_pump_iterations=pumps_total,longest_selected_path=longest,path_bound=4*D+6))
  edges+=selected;paths+=count
 return dict(scope='finite actual-index replay; uniform local argument separate',
  specimens=len(rows),oriented_paths=paths,selected_edges=edges,
  cases=dict(sorted(counts.items())),members=rows,universal_x_productivity=False)

def profile():
 record=M['RECORD'];data=json.loads(record.read_text());rows=[]
 for old in data['members']:
  k,t,n=old['k'],old['t'],old['n'];D=(n-1)//(k+1)
  states=set(map(tuple,old['certificate']['states']))-set(map(tuple,old['exceptions']))
  ps=sorted(w[2] for w in states if w[:2]==(0,2) and w==P(w[2]))
  if ps!=list(range(-D,D+1)):raise AssertionError('finite signed interval mismatch')
  for p in ps:
   if rev(P(p)) not in states:raise AssertionError('missing genuine reversal')
  rows.append(dict(k=k,t=t,p_indices_in_x_closure=ps,
   parameter_uniform_reachable_interval_proved=False))
 return dict(scope='finite 22-graph signed-cell profile only',members=rows,
  certificate_sha256=sha256(record.read_bytes()).hexdigest(),universal_x_productivity=False)

def controls():
 g=G(-1,0,8);w=P(-1);bad=(w,33,19,Z(2,-2,2))
 if not g.interior(w) or not g.interior(bad[3]):
  raise AssertionError('formal sign-fold control labels must both be strict')
 try:M['BASE']['verify_path'](g,[bad])
 except ValueError:pass
 else:raise AssertionError('nonexistent y ordinal accepted')
 g=G(-1,0,2);packet,_,_=path(0,2,-1)
 M['BASE']['verify_path'](g,packet)
 bad_last=(Q(-1),0,15,P(-2))
 try:M['verify_edges'](g,[bad_last])
 except ValueError:pass
 else:raise AssertionError('LAST x replaced by RUN y')
 return dict(immediate_fold=dict(k=0,t=8,refused_edge=bad,
  bottom_ordinal_maximum=11,both_formal_labels_strict=True,
  proposed_rule='high-wall first edge extrapolated outside a>=t+2',
  reason='bottom y ordinal 19 is nonexistent'),
  cap_last=dict(k=0,t=2,refused_edge=bad_last,actual_edge=packet[1]),
  productivity_obstruction_found=False)

if __name__=='__main__':
 print(json.dumps(dict(paths=replay(),finite_profile=profile(),controls=controls()),indent=2,sort_keys=True))
