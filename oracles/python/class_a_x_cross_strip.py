"""Independent literal/Fraction replay of class-A cross-strip entrances.

The suffix is the previously proved signed path, shared mathematically;
all edges of every new oriented path are replayed independently here.
"""
from collections import deque
from hashlib import sha256
import json
from pathlib import Path
import runpy

M=runpy.run_path(str(Path(__file__).with_name('class_a_x_signed_strip.py')))
T=M['M'];BASE=T['BASE'];Geometry=M['G'];reverse=M['rev']
ROOT=Path(__file__).resolve().parents[2]
RECORD=T['RECORD']


def source(p,s):return (0,2,p,3*p+s,1-s-6*p)


def in_domain(k,t,p,s):
 if min(k,t)<0 or not -3<=s<=3:return False
 if p>=0:return (k+1)*p<=k+t+2
 return s<=1 and (k+1)*(-p)<=t


def path(k,t,p,s,flip=False,step_cap=10000):
 if not in_domain(k,t,p,s):raise ValueError('outside proved cross-strip sectors')
 baseline,_,_=M['path'](k,t,p,step_cap=step_cap)
 first=(k+t+3+s+1) if p==0 else (k+t+3+s+3-(k+1)*p)
 target=T['D'] if p==0 else M['Q'](p)
 packet=[(source(p,s),first,0,target)]+baseline[1:]
 if flip:packet=[(reverse(a),j,i,reverse(b)) for a,i,j,b in packet]
 return packet


def replay():
 rows=[];paths=edges=entrances=shared=0
 for k,t in T['MEMBERS']:
  g=Geometry(-1,k,t);K=k+1;D=(g.n-1)//K
  count=total=checked=0
  for p in range(-(t//K),D+1):
   # The native audit verifies one shared suffix per p/orientation, and
   # separately verifies each distinct entrance and exact suffix equality.
   base=M['path'](k,t,p)[0]
   checked+=2*(len(base)-1)
   for s in range(-3,2 if p<0 else 4):
    for flip in (False,True):
     packet=path(k,t,p,s,flip)
     BASE['verify_path'](g,packet)
     if p>=0 and len(packet)!=2*p+2:raise AssertionError('positive length changed')
     if len(packet)>4*D+6:raise AssertionError('cross-strip budget exceeded')
     count+=1;total+=len(packet)
  rows.append(dict(k=k,t=t,oriented_paths=count,selected_edges=total,
   new_entrance_checks=count,shared_suffix_edge_checks=checked))
  paths+=count;edges+=total;entrances+=count;shared+=checked
 return dict(scope='finite actual-index replay of uniformly proved local sectors',
  specimens=len(rows),oriented_paths=paths,selected_edges=edges,
  native_entrance_checks=entrances,native_shared_suffix_checks=shared,
  native_total_indexed_checks=entrances+shared,members=rows,
  universal_x_productivity=False)


def previous_carrier(k,t):
 K=k+1;n=k+t+3;D=(n-1)//K;labels={BASE['X'],BASE['C']}
 packets=[M['path'](k,t,p)[0] for p in range(-D,D+1)]
 packets.extend(T['unit_path'](k,t,p) for p in range((n+3)//K+1))
 packets.append(T['exception_base_path'](k,t))
 if 2*k+t>=2:
  packets.extend(BASE['ladder_path'](k,t,m) for m in range(1,(k+t+6)//K+1))
 for packet in packets:
  for a,_,_,b in packet:labels.update((a,b))
 return labels|{reverse(w) for w in labels}


def profile():
 data=json.loads(RECORD.read_text());rows=[]
 for row in data['members']:
  k,t=row['k'],row['t'];K=k+1;D=(row['n']-1)//K
  states=set(map(tuple,row['certificate']['states']))-set(map(tuple,row['exceptions']))
  labels={source(p,s) for p in range(-(t//K),D+1)
          for s in range(-3,2 if p<0 else 4)}
  labels|={reverse(w) for w in labels}
  reached=labels&states;old=previous_carrier(k,t)
  u1=[w for w in states if w[:2]==(0,2) and 3*w[2]+w[3]+w[4]==1]
  outside=sorted(w for w in u1 if not in_domain(k,t,w[2],w[3]-3*w[2]))
  rows.append(dict(k=k,t=t,reached_oriented_sources=len(reached),
   reached_sources_outside_previous_local_path_carrier=len(reached-old),
   new_reached_labels=sorted(reached-old),finite_u1_xy_sources=len(u1),
   finite_u1_xy_sources_in_sector=sum(w in labels for w in u1),
   finite_u1_xy_sources_outside_sector=outside,
   parameter_uniform_x_coverage_proved=False))
 return dict(scope='finite coverage on the 22 completed parent graphs only',
  certificate_sha256=sha256(RECORD.read_bytes()).hexdigest(),members=rows,
  universal_x_productivity=False)


def endpoint_control():
 g=Geometry(-1,0,0);w=source(2,-4);target=M['Q'](2)
 if not g.interior(w) or not g.interior(target):raise AssertionError('control is not strict')
 # The tempting entrance has i=n+s+3-Kp=0, a real FIRST, not a RUN.
 actual=g.child(w,0,0)
 if actual==target or actual[:2]!=(0,0):raise AssertionError('FIRST calibration changed')
 try:T['verify_edges'](g,[(w,0,0,target)])
 except ValueError:pass
 else:raise AssertionError('FIRST accepted as RUN')
 _,seeds=BASE['swap_sources'](g);states,ids,adj=BASE['complete_graph'](g,seeds)
 start,end=ids[BASE['X']],ids[w];todo=deque([start]);prev={start:None}
 while todo:
  v=todo.popleft()
  for z,i,j in adj[v]:
   if z not in prev:prev[z]=(v,i,j);todo.append(z)
 if end not in prev:raise AssertionError('control not an actual X descendant')
 packet=[];v=end
 while v!=start:
  u,i,j=prev[v];packet.append((states[u],i,j,states[v]));v=u
 packet.reverse();T['verify_edges'](g,packet)
 return dict(k=0,t=0,p=2,s=-4,source=w,formal_entrance=(w,0,0,target),
  actual_first_child=actual,both_formal_labels_strict=True,x_to_source_path=packet,
  conclusion='strict X ancestry does not turn FIRST ordinal zero into a RUN',
  productivity_obstruction_found=False)


if __name__=='__main__':
 print(json.dumps(dict(paths=replay(),finite_profile=profile(),endpoint_control=endpoint_control()),
                  indent=2,sort_keys=True))
