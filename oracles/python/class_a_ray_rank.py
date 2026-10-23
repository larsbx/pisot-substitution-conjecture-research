"""Propose integer affine ranks for fixed class-A residue-ray occurrences.

Usage: python oracles/python/class_a_ray_rank.py D,EPS,R N0
Requires NumPy and SciPy only for synthesis. Linear programming uses floating
arithmetic to propose coefficients; rational reconstruction and integer
scaling produce a candidate. Both exact closure and descent are checked by
the independent Fraction/Sturm oracle BEFORE any table is written. The
canonical Mojo verifier must still accept the table. Optimizer success is
never evidence. A failed optimization or exact check leaves the table intact.

For each affine endpoint j=u*l+v, require the potential's l-slope and its
value at l0 to be nonnegative; for each selected edge impose the same two
conditions on X(parent)-X(child)-1. These linear inequalities quantify over
the entire ray. Targets have rank zero. No graph or occurrence is changed.
"""
import sys,importlib.util,re,math,json
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
root=Path(__file__).resolve().parents[2]
if len(sys.argv) != 3:
    raise SystemExit('usage: class_a_ray_rank.py D,EPS,R N0')
ray=sys.argv[1];n0=int(sys.argv[2]);gap,eps,res=map(int,ray.split(','));sys.argv=['oracle','--ray',ray]
spec=importlib.util.spec_from_file_location('oracle',root/'oracles/python/class_a_carrier_closure.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
R=m.carrier_rows();P=m.pieces();D=m.descents();l0=(n0-res+gap-1)//gap
N=3*len(P);A=[];B=[];cost=np.zeros(N)
def expr(i,u):
 a,b=u
 slope=np.zeros(N);slope[3*i]=1;slope[3*i+1]=a
 const=np.zeros(N);const[3*i+1]=b;const[3*i+2]=1
 return slope,const
for i,p in enumerate(P):
 for u in [(p[1],p[2]),(p[3],p[4])]:
  slope,c=expr(i,u);A.extend([-slope,-l0*slope-c]);B.extend([0,0]);cost+=100*slope+l0*slope+c
for d in D:
 i,la,lb,ha,hb,pt,pb,yp,k=d
 row=R[P[i][0]];crow=R[P[k][0]]
 dx=int(row[1]!=1 and pb>0)-int(row[0]!=1 and pt>0)  # first letters (x,c,x)
 shift=(row[4]-crow[4],row[5]+row[2]+dx-crow[5])
 for u in [(la,lb),(ha,hb)]:
  sa,ca=expr(i,u);sb,cb=expr(k,(u[0]+shift[0],u[1]+shift[1]));ss=sa-sb;cc=ca-cb
  A.extend([-ss,-l0*ss-cc]);B.extend([0,-1])
bounds=[(None,None)]*N
for i,p in enumerate(P):
 row=R[p[0]]
 if row[2]==row[3]==0 and p[1:3]==p[3:5] and row[4]+p[1]==row[5]+p[2]==0:
  bounds[3*i:3*i+3]=[(0,0)]*3
out=linprog(cost,A_ub=np.array(A),b_ub=np.array(B),bounds=bounds,method='highs')
print(ray,out.message,flush=True)
if not out.success:sys.exit(1)
f=[Fraction(float(x)).limit_denominator(10000) for x in out.x];den=math.lcm(*(x.denominator for x in f));ints=[int(x*den) for x in f]
Pnew=[tuple(p[:5])+tuple(ints[3*i:3*i+3]) for i,p in enumerate(P)]
m.verify_closure(R,n0)
print(m.verify_descent(R,Pnew,D,n0),flush=True)
file=root/f'kernel/psc/class_a_ray_d{gap}{"p" if eps==1 else "m"}.mojo';txt=file.read_text();start=txt.index(f'def pieces_r{res}(');end=txt.find('\ndef ',start+1);end=len(txt) if end<0 else end
part=txt[start:end];it=iter(Pnew)
part=re.sub(r'List\[Int\]\(\[(-?\d+(?:,-?\d+){7})\]\)',lambda _: 'List[Int](['+','.join(map(str,next(it)))+'])',part)
part=re.sub(r'    """.*?"""','    """Affine tail rank synthesized from fixed occurrences; exact verifier is the certificate. [carrier row, j_lo l-slope, j_lo constant, j_hi l-slope, j_hi constant, X_l, X_j, X_c]."""',part,count=1)
file.write_text(txt[:start]+part+txt[end:])
