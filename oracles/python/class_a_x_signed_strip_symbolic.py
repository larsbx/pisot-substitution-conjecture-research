"""Coefficient certificates for signed-strip edges and exhaustive guard chambers.

The guard chambers cover integers, rather than a grid interpolation. Geometry
uses inherited root inequalities plus the rational identities checked here;
the complete inequality argument is in the accompanying manuscript.
"""
from pathlib import Path
import runpy
from sympy import Poly, cancel, expand, fraction, symbols

M=runpy.run_path(str(Path(__file__).with_name('class_a_x_transfer_plane_symbolic.py')))
k,t,beta=M['k'],M['t'],M['beta']
n,d,K,A=M['n'],M['d'],M['K'],M['A']
r,u,v,w=symbols('r u v w')
GENS=(k,t,r,beta,u,v,w)

def zero(expr):
 if not Poly(expand(expr),*GENS).is_zero:raise ValueError('nonzero coefficient')

def nonnegative(expr,gens=(u,v,w)):
 if any(c<0 for c in Poly(expand(expr),*gens).coeffs()):
  raise ValueError('negative guard-chamber coefficient')

def P(p):return (0,2,p,3*p+1,-6*p)
def Q(p):return (2,0,-p,1-3*p,6*p-3)
def Z(R,s,U):return (0,2,R,3*R+s,U-s-6*R)
def H(R,U):return (0,0,-R,1-3*R,6*R+U-1)

def edge(a,tk,i,bk,j,b,fixed=None):
 fixed=fixed or {}
 lt,pt=M['occurrence'](a[0],tk,i,fixed)
 lb,pb=M['occurrence'](a[1],bk,j,fixed)
 if (lt,lb)!=b[:2]:raise ValueError('wrong actual child types')
 x,c,y=a[2:];image=(2*x+c+y,c+y,A*x+n*c+(n-1)*y)
 for q in range(3):zero((image[q]+pb[q]-pt[q]-b[q+2]).subs(fixed))

def certify():
 a=K*r;R=r+1
 pump=[(P(-r),'RUN',n+4+a,'FIRST',0,Q(-r)),
       (Q(-r),'FIRST',0,'RUN',2*n+4+a,P(-r-1))]
 cap1=[pump[0],(Q(-r),'FIRST',0,'LAST',A+1,H(R,1)),
       (H(R,1),'LAST',A+1,'RUN',t+4,Z(R+1,-2,2)),
       (Z(R+1,-2,2),'RUN',t+8,'FIRST',0,M['reverse'](P(R)))]
 cap0=[pump[0],(Q(-r),'FIRST',0,'LAST',A+1,H(R,0)),
       (H(R,0),'LAST',A+1,'RUN',d+3,Z(R,0,1)),
       (Z(R,0,1),'RUN',5,'FIRST',0,Q(R))]
 near=[(P(-r),'LAST',A+1,'RUN',n-1,Z(R,-2,1)),
       (Z(R,-2,1),'RUN',2,'FIRST',0,Q(R))]
 high=[(P(-r),'LAST',A+1,'RUN',d-a-1,Z(R,-2,2)),
       (Z(R,-2,2),'RUN',2*n+3-K*R,'FIRST',0,M['reverse'](P(r)))]
 branches=[(pump,{}),(cap1,{t:a+1}),(cap0,{t:a}),
           (near,{t:a-1}),(high,{})]
 for rows,fixed in branches:
  for aa,tk,i,bk,j,bb in rows:
   edge(aa,tk,i,bk,j,bb,fixed)
   edge(M['reverse'](aa),bk,j,tk,i,M['reverse'](bb),fixed)
 # Guard variables a=Kr are replaced by independent linear chambers.
 # This proves a superset of the divisible integer cases, so none are lost.
 kk,tt,aa=symbols('K0 t0 a0')
 nn=kk+tt+2;dd=kk+2*tt+4;AA=nn+dd;B=aa+kk
 guards={
  'pump':[nn+3+aa,AA-(nn+4+aa),2*nn+3+aa,AA-(2*nn+4+aa),
          nn-4-B],
  'cap1':[nn+3+aa,AA-(nn+4+aa),tt+3,AA-(tt+4),tt+7,AA-(tt+8),
          nn+3-B,2*nn-5-(aa+2*kk)],
  'cap0':[nn+3+aa,AA-(nn+4+aa),dd+2,AA-(dd+3),4,AA-5,nn+3-B],
  'near':[nn-2,1,1,AA-2,nn+3-B],
  'high':[dd-aa-2,nn-1-(dd-aa-1),2*nn+2-B,AA-(2*nn+3-B),
          nn+3-aa,2*nn-3-B]}
 Kc=u+1;ac=Kc+v
 substitutions={
  'pump':{kk:Kc,aa:ac,tt:ac+2+w},
  'cap1':{kk:Kc,aa:ac,tt:ac+1},
  'cap0':{kk:Kc,aa:ac,tt:ac},
  'near':{kk:Kc,aa:ac,tt:ac-1},
  'high':{kk:u+v+1,aa:w+u+2,tt:w}}
 # high: a-t-2=u>=0 and n-1-a=K-1-u=v>=0.
 for name,goals in guards.items():
  for goal in goals:nonnegative(expand(goal).subs(substitutions[name],simultaneous=True))
 zero((2*n+4+a-A).subs({t:a+1})-1)
 zero((2*n+4+a-A).subs({t:a})-2)
 zero((a+K-(n-3)).subs({t:a+1}))
 zero((a+K-(n-2)).subs({t:a}))
 zero((a+K-(n-1)).subs({t:a-1}))
 # Exact normalized physical shifts and root relation, modulo the cubic.
 h=1/beta;alpha=beta-(n+2);rho=alpha-h;V=K/(beta+1)
 chi=beta**3-(n+2)*beta**2-(t+3)*beta+2
 exprs=[alpha*(beta+1)-(t+3+alpha-2*h)]
 for label,want in [(P(-r),1+h+r*V),(Q(-r),-2+h-r*V),
                    (H(R,u),u+h+R*V),(Z(R,u,v),v+u*h-R*V)]:
  x,c,y=label[2:];exprs.append(x*(2+rho)+c*(1+h)+y-want)
 for expr in exprs:
  numerator,_=fraction(cancel(expr))
  zero(Poly(numerator,beta).rem(Poly(chi,beta)).as_expr())
 # With D=r+ell+q and r>=1, worst length 2ell+2(r+ell)+8
 # is at most 4D+6. q is the remaining nonnegative radius budget.
 ell,q=symbols('ell q')
 nonnegative(expand(4*(r+ell+q)+6-(2*ell+2*(r+ell)+8)).subs(r,u+1),(u,q))
 return dict(coefficient_ring='Z[k,t,r]',directed_edge_schema_checks=28,
  exhaustive_integer_wall_regimes=5,nonnegative_guard_certificates=sum(map(len,guards.values())),
  root_and_shift_identities=len(exprs),radius_budget='D-r decreases by one per pump',
  selected_path_bound='4D+6',formalized_full_geometry=False,
  parameter_uniform_x_coverage_proved=False,universal_x_productivity=False)

if __name__=='__main__':
 import json
 print(json.dumps(certify(),indent=2,sort_keys=True))
