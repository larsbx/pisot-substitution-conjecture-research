"""Independent literal-word/Fraction H9 stars; universal guard proof separate."""
from pathlib import Path
import runpy
p9=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_p9_children.py')))
j9=p9['j9'];j8=j9['j8'];r4=j9['r4']
Geometry,reverse,C=p9['Geometry'],p9['reverse'],p9['C']


def source(kind):
    if kind not in (0,1):raise ValueError('unknown H9 orientation')
    return j9['source'](4+kind)


def companion(kind):
    if kind not in range(6):raise ValueError('unknown H9 companion')
    w=(2,0,-1,-3,4+kind//2)
    return reverse(w) if kind%2 else w


def interface(w,include_new=False):
    old=p9['interface'](w,True)
    if old is not None:return old
    return 'H9' if include_new and w in (source(0),source(1)) else None


def exit_interface(w,include_new=False):
    old=p9['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        for group,name in enumerate(('K9','L9','M9')):
            if w in (companion(2*group),companion(2*group+1)):return name
    return None


def count(k,t):
    if min(k,t)<0:raise ValueError('negative parameter')
    n=k+t+3;A=3*n-1-k
    return 2*A+3 if k<=1 else 2*A-2*k+5


def predicted(kind,g,i,j):
    w=source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j);k,A=g.k,g.n+g.d
    if a==0:return k<=1 if b==0 else max(1,k-1)<=b<=k+1
    if a<=A:
        if 1<=b<=A:return b-a in (k,k+1)
        return b==A+1 and A-k<=a<=min(A,A-k+2)
    return b==A+1 and k<=1


def envelope():
    base=({(0,0,-1,-3,r) for r in (4,5)}|{(0,2,0,-3,r) for r in (3,4,5)}|
          {(2,2,-1,-3,r) for r in (5,6)}|{(2,0,-1,-3,r) for r in (4,5,6)})
    out=base|{reverse(w) for w in base}
    assert len(out)==20
    return out


def path(kind,g):return j9['path'](4+kind,g)


def verify_path(w,g,packet,want):p9['verify_path'](w,g,packet,want)


def verify_star(kind,g,edges):
    if len(edges)!=count(g.k,g.t) or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate H9 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong indexed typed target')



def companion_path(kind,g):
    companion(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group,flip=divmod(kind,2)
    if group==0:
        v=(0,2,0,1,-2)
        out=[(0,g.d+3,v)]+j9['e7']['b5']['y4']['tail'](v,g)
    elif group==1:out=[(0,g.t+5,j9['e7']['b5']['source'](1))]+j9['e7']['b5']['path'](1,g)
    else:out=[(g.k+1,0,r4['source'](11))]+r4['path'](11,g)
    return [(j,i,reverse(w)) for i,j,w in out] if flip else out


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('outside H9 image tail interface')
    for flip in (0,1):
        if w==p9['companion'](flip):return p9['companion_path'](flip,g)
        for group in (1,2,3,4):
            if w==j8['source'](2*group+flip):return j8['path'](2*group+flip,g)
        for group in (2,5):
            if w==r4['source'](2*group+flip):return r4['path'](2*group+flip,g)
        for group in range(3):
            if w==companion(2*group+flip):return companion_path(2*group+flip,g)
    raise ValueError('H9 image dispatch missed a label')


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong first H9 packet')
    return [edge]+tail(w,g)


def verify_walk(kind,g,edge,packet):
    if len(packet)>7:raise ValueError('H9 first-choice bound exceeded')
    verify_path(source(kind),g,packet,walk(kind,g,edge))


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(j9['e7']['b5']['r3']['candidate'](True))
    return dict(labels=41,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                source_rows=registry_rows({source(i) for i in (0,1)}|{companion(i) for i in range(6)}),rows=rows,image_rows=registry_rows(envelope()),previous_P9_image_rows=registry_rows(p9['envelope']()))


def verify_native_registry(output):
    import ast
    code=Path(__file__).with_name('class_a_boundary_j9_children.py').read_text()
    fn=next(n for n in ast.parse(code).body if isinstance(n,ast.FunctionDef) and n.name=='verify_native_registry')
    ids=ast.literal_eval(fn.body[0].value);ids.update(W9=64,B9=65,K9=66,L9=67,M9=68)
    rec=reconciliation()
    for name,key in [('SOURCE','source_rows'),('CANDIDATE','rows'),('IMAGE','image_rows'),('P9_IMAGE','previous_P9_image_rows')]:
        prefix='CLASS_A_H9_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/oracle H9 registry disagreement')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=companion_edges=walk_edges=max_walk=image_tail_edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);counts=[];A=g.n+g.d
            for kind in (0,1):
                w=source(kind);assert g.interior(w)
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(A+2) for j in range(A+2) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual));assert len(actual)==count(k,t)
                for edge in sorted(actual):
                    i,j,v=edge;assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    packet=walk(kind,g,edge);verify_walk(kind,g,edge,packet)
                    walk_edges+=len(packet);max_walk=max(max_walk,len(packet))
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==6 and p[0] in actual
                path_edges+=len(p);pairs+=(A+2)**2;accepted+=len(actual);counts.append(len(actual))
                if k==0:assert g.child(p9['source'](kind),0,0)==w
                if k<=1:
                    assert (0,0,g.child(w,0,0)) in actual and (A+1,A+1,g.child(w,A+1,A+1)) in actual
                    assert g.child(w,0,0)==g.child(w,A+1,A+1)
            for kind in range(6):
                w=companion(kind);assert g.interior(w)
                p=companion_path(kind,g);verify_path(w,g,p,p);assert len(p)==(4,3,6)[kind//2];companion_edges+=len(p)
            for w in sorted(envelope()):
                p=tail(w,g);verify_path(w,g,p,p);image_tail_edges+=len(p)
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and max_walk==7
    rec=reconciliation()
    return dict(scope='finite independent implementation replay; universal nine-kind/count/path proof separate; no global BH',members=len(rows),source_cells=2*len(rows),pairs=pairs,accepted=accepted,source_path_edges=path_edges,companion_path_edges=companion_edges,all_child_walk_edges=walk_edges,all_image_tail_edges=image_tail_edges,max_selected_walk=max_walk,image_labels=20,source_exit=6,
                all_direct_children_productivity_proved=True,closed_carrier_proved=False,new_companion_stars=False,image_registered_stars=sum(interface(w,True) is not None for w in envelope()),image_uniform_exits=sum(exit_interface(w,True) is not None for w in envelope()),
                reconciliation=rec,witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
