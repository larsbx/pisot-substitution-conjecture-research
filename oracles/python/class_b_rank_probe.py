"""Bounded synthesis prototype, not a certificate or canonical rank verifier.
Try one floor((a*l+b*k+c)/2) depth envelope per typed interval on plus g=1.
Candidates must later pass canonical all-parameter occurrence/rank checks.
"""
import json
from pathlib import Path
from class_b_label_rays import read, intervals


def probe(directory):
    directory=Path(directory)
    points={}
    rows9=intervals(read(directory/'plus-g1-q9.labels')[1])
    rows10=intervals(read(directory/'plus-g1-q10.labels')[1])
    def row_of(q, v):
        t,b,k,c,y,*_=v;typ=(t,b,3*k+c+y,c-3*k)
        matches=[i for i,(x,z) in enumerate(zip(rows9,rows10)) if x[:4]==typ and x[4]+(q-9)*(z[4]-x[4])<=k<=x[5]+(q-9)*(z[5]-x[5])]
        if len(matches)!=1:raise ValueError('ray carrier mismatch')
        return matches[0]
    for q in range(9,27):
        for v in read(directory/f'plus-g1-q{q}.labels')[1]:
            points.setdefault(row_of(q,v),[]).append((q,v[2],v[5]))
    fits={};refusals=[]
    for ri,pts in sorted(points.items()):
        ans=None
        for slack in range(3):
            for a in range(-4,5):
                for b in range(-4,5):
                    lo=max(2*z-a*l-b*k for l,k,z in pts)
                    hi=min(2*z+1+2*slack-a*l-b*k for l,k,z in pts)
                    # Nonnegative eventual endpoint slopes are necessary, not sufficient.
                    if lo<=hi and all(a+b*(rows10[ri][j]-rows9[ri][j])>=0 for j in (4,5)):
                        ans=(a,b,lo,slack);break
                if ans:break
            if ans:break
        if ans:fits[ri]=ans
        else:refusals.append(ri)
    failures=[]
    for q in range(27,43):
        for v in read(directory/f'plus-g1-q{q}.labels')[1]:
            ri=row_of(q,v)
            if ri not in fits:continue
            a,b,c,slack=fits[ri];rank=(a*q+b*v[2]+c)//2
            if not v[5]<=rank<=v[5]+slack:
                failures.append(dict(q=q,row=ri,label=v[:5],depth=v[5],envelope=rank));break
    witness_audit=dict(checked=0,missing_potential=0,nondecreasing=0,first_nondecreasing=None)
    for q in (9,10):
        path=directory.parent/'witnesses'/f'plus-g1-q{q}.labels'
        _,raw=read(path);depths={v[:5]:v[5] for v in raw}
        seen=set()
        for line in path.read_text().splitlines():
            if not line.startswith('W '):continue
            v=tuple(map(int,line.split()[1:]));parent=v[:5];child=v[5:10];i,j=v[10:]
            if parent in seen:raise ValueError('duplicate descent')
            seen.add(parent)
            # Independent ordinary image-prefix construction, not the typed map.
            p=3*q+11;sigma=[[0]+[2]*p+[0],[1]+[2]*q+[0],[1]+[2]*(q+1)+[0]]
            if not (0<=i<len(sigma[parent[0]]) and 0<=j<len(sigma[parent[1]])):raise ValueError('illegal index')
            if sigma[parent[0]][i]!=child[0] or sigma[parent[1]][j]!=child[1]:raise ValueError('wrong child letters')
            k,c,y=parent[2:];mw=[2*k+c+y,c+y,p*k+q*c+(q+1)*y]
            expected=tuple(mw[h]+sigma[parent[1]][:j].count(h)-sigma[parent[0]][:i].count(h) for h in range(3))
            if expected!=child[2:] or depths[child]!=depths[parent]-1:raise ValueError('wrong shift/depth descent')
            witness_audit['checked']+=1
            pr,cr=row_of(q,parent),row_of(q,child)
            if pr not in fits or cr not in fits:
                witness_audit['missing_potential']+=1;continue
            def potential(ri,v):
                a,b,c,_=fits[ri];return a*q+b*v[2]+c
            if potential(cr,child)>=potential(pr,parent):
                witness_audit['nondecreasing']+=1
                if witness_audit['first_nondecreasing'] is None:
                    witness_audit['first_nondecreasing']=dict(q=q,parent=parent,child=child,indices=[i,j],parent_X=potential(pr,parent),child_X=potential(cr,child))
        if seen!={v[:5] for v in raw if v[5]>0}:raise ValueError('incomplete descent witnesses')
    return dict(witness_audit=witness_audit,status='bounded-synthesis-only',training=[9,26],holdout=[27,42],coefficient_budget=[-4,4],denominator=2,slack_budget=[0,2],rows=len(rows9),candidates={str(k):v for k,v in fits.items()},refused_rows=refusals,first_failure_per_holdout=failures)

if __name__=='__main__':
    import sys
    report=probe(sys.argv[1]);Path(sys.argv[2]).write_text(json.dumps(report,indent=2)+'\n')
    print('RANK_PROBE',report['rows'],'rows',len(report['candidates']),'candidates',len(report['refused_rows']),'refused',len(report['first_failure_per_holdout']),'holdouts with envelope failure; no rank certificate')
