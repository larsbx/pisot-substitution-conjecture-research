"""Exact typed RUN-shear covariance and linear guard implication receipts.

Each guard is a nonnegative rational linear combination of explicitly
named premises. This certifies unbounded implication, not sample fitting.
Geometry inequalities are proved in the accompanying manuscript.
"""
from pathlib import Path
import runpy
from sympy import Poly,cancel,expand,fraction,symbols

M=runpy.run_path(str(Path(__file__).with_name('class_a_x_transfer_plane_symbolic.py')))
k,t,p,s,beta=M['k'],M['t'],M['p'],M['s'],M['beta']
n,d,K,A=M['n'],M['d'],M['K'],M['A']
x,c,y,m,i,j,b,a=symbols('x c y m i j b a')
GENS=(k,t,p,s,beta,x,c,y,m,i,j,b,a)


def zero(expr):
 if not Poly(expand(expr),*GENS).is_zero:raise ValueError('nonzero coefficient')


def image(delta):
 x,c,y=delta
 return (2*x+c+y,c+y,A*x+n*c+(n-1)*y)


def transport(top,bottom,delta,tk,ii,bk,jj):
 lt,pt=M['occurrence'](top,tk,ii,{})
 lb,pb=M['occurrence'](bottom,bk,jj,{})
 v=image(delta)
 return lt,lb,tuple(expand(v[q]+pb[q]-pt[q]) for q in range(3))


def certificate(goal,premises,weights):
 if any(weight<0 for weight in weights.values()):raise ValueError('negative cone weight')
 zero(goal-sum(weight*premises[name] for name,weight in weights.items()))


def certify():
 delta=(x,c,y);sheared=(x,c+m,y-m);cases=0
 for top in range(3):
  for bottom in range(3):
   for bk,jj in [('FIRST',0),('RUN',j),('LAST',(A,n,n-1)[bottom]+1)]:
    base=transport(top,bottom,delta,'RUN',i,bk,jj)
    lifted=transport(top,bottom,sheared,'RUN',i+m,bk,jj)
    if base[:2]!=lifted[:2]:raise ValueError('shear changed child types')
    for old,new in zip(base[2],lifted[2]):zero(old-new)
    # Genuine reversal transposes indices and negates the full source.
    rb=transport(bottom,top,tuple(-v for v in delta),bk,jj,'RUN',i)
    rl=transport(bottom,top,tuple(-v for v in sheared),bk,jj,'RUN',i+m)
    if rb[:2]!=rl[:2] or rb[:2]!=(base[1],base[0]):raise ValueError('reversal type mismatch')
    for old,new,target in zip(rb[2],rl[2],base[2]):zero(old-new);zero(old+target)
    cases+=1
 # Specific entrance packets, including the p=0 auxiliary target.
 Z=(p,3*p+s,1-s-6*p);Q=(-p,1-3*p,6*p-3)
 got=transport(0,2,Z,'RUN',n+s+3-K*p,'FIRST',0)
 if got[:2]!=(2,0):raise ValueError('wrong Q type')
 for old,new in zip(got[2],Q):zero(old-new)
 got=transport(0,2,(0,s,1-s),'RUN',n+s+1,'FIRST',0)
 for old,new in zip(got[2],(0,1,-1)):zero(old-new)
 # Seven Farkas-style implication certificates. Every named premise is
 # nonnegative in its stated positive, zero or negative sector.
 pp={'one':1,'K-1':K-1,'t':t,'b-K':b-K,'n-1-b':n-1-b,
     's+3':s+3,'3-s':3-s}
 zp={'one':1,'K-1':K-1,'t':t,'s+3':s+3,'3-s':3-s}
 np={'one':1,'K-1':K-1,'t':t,'a-K':a-K,'t-a':t-a,
     's+3':s+3,'1-s':1-s}
 rows=[(n+s+2-b,pp,{'n-1-b':1,'s+3':1}),
       (A-(n+s+3-b),pp,{'K-1':2,'t':2,'b-K':1,'3-s':1}),
       (n+s,zp,{'K-1':1,'t':1,'s+3':1}),
       (A-(n+s+1),zp,{'K-1':1,'t':2,'3-s':1,'one':1}),
       (n+s+2+a,np,{'K-1':2,'t':1,'s+3':1,'a-K':1,'one':3}),
       (A-(n+s+3+a),np,{'K-1':1,'t':1,'t-a':1,'1-s':1,'one':1}),
       (n-1-a,np,{'K-1':1,'t-a':1,'one':2})]
 for goal,premises,weights in rows:certificate(goal,premises,weights)
 h=1/beta;rho=beta-(n+2)-h;V=K/(beta+1)
 chi=beta**3-(n+2)*beta**2-(t+3)*beta+2
 xx,cc,yy=Z;expr=xx*(2+rho)+cc*(1+h)+yy-(1+s*h-p*V)
 numerator,_=fraction(cancel(expr))
 zero(Poly(numerator,beta).rem(Poly(chi,beta)).as_expr())
 return dict(coefficient_ring='Z[k,t,x,c,y,m,i,j,p,s]',
  generic_parent_and_bottom_occurrence_cases=cases,
  generic_oriented_shear_cases=2*cases,sector_entrance_schemas=2,
  nonnegative_linear_guard_certificates=len(rows),root_shift_identities=1,
  generic_run_guard_required=True,formalized_full_geometry=False,
  universal_x_productivity=False)


if __name__=='__main__':
 import json
 print(json.dumps(certify(),indent=2,sort_keys=True))
