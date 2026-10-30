"""Independent literal-word/Fraction W9 stars, separate from universal proof."""
from pathlib import Path
import runpy
h9=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_h9_children.py')))
p9=h9['p9'];j9=h9['j9'];j8=h9['j8'];r4=h9['r4']
Geometry,reverse,C=h9['Geometry'],h9['reverse'],h9['C']
eh=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_e_children.py')))


def source(kind):
    if kind not in (0,1):raise ValueError('unknown W9 orientation')
    return p9['companion'](kind)


def interface(w,include_new=False):
    old=h9['interface'](w,True)
    if old is not None:return old
    return 'W9' if include_new and w in (source(0),source(1)) else None


def companion(kind):
    if kind not in range(12):raise ValueError('unknown W9 companion')
    base=((2,0,-1,-2,5),(0,2,0,-2,2),(0,2,0,-2,3),(0,2,0,-2,4),(2,2,0,-2,2),(2,2,0,-2,3))
    return reverse(base[kind//2]) if kind%2 else base[kind//2]


def exit_interface(w,include_new=False):
    old=h9['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        for group,name in enumerate(('N9','X2','X3','X4','Y2','Y3')):
            if w in (companion(2*group),companion(2*group+1)):return name
    return None


def count(k,t):
    if min(k,t)<0:raise ValueError('negative parameter')
    return 4*(k+t+3)+1


def predicted(kind,g,i,j):
    w=source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    A=g.n+g.d;t=g.t
    if not(0<=i<=A+1 and 0<=j<=A+1):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j)
    if 1<=a<=A:
        if b==0:return t+3<=a<=t+5
        return 1<=b<=A and a-b in (t+4,t+5)
    return a==A+1 and A-t-4<=b<=A-t-2


def envelope():
    base=({(2,0,-1,-2,r) for r in (3,4,5)}|{(2,2,0,-2,r) for r in (2,3)}|{(0,2,0,-2,r) for r in (2,3,4)})
    out=base|{reverse(w) for w in base}
    assert len(out)==16
    return out


def path(kind,g):return p9['companion_path'](kind,g)


def verify_path(w,g,packet,want):h9['verify_path'](w,g,packet,want)



def verify_star(kind,g,edges):
    if len(edges)!=count(g.k,g.t) or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate W9 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong indexed typed target')


def companion_path(kind,g):
    companion(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group,flip=divmod(kind,2)
    y4=j9['e7']['b5']['y4']
    if group==0:out=[(g.k+1,0,j8['source'](5))]+j8['path'](5,g)
    elif group in (1,4):out=[(0,2,y4['source'](0))]+y4['path'](0,g)
    elif group in (2,5):out=[(g.n-1,0,eh['source'](3))]+eh['short_path'](3,g)
    else:
        h3=r4['h3'];out=[(2*g.n+1,0,h3['source'](2))]+h3['path'](2,g)
    return [(j,i,reverse(w)) for i,j,w in out] if flip else out


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('outside W9 image tail interface')
    for flip in (0,1):
        b5=j9['e7']['b5']
        if w==b5['source'](flip):return b5['path'](flip,g)
        if w==p9['companion'](2+flip):return p9['companion_path'](2+flip,g)
        for group in range(6):
            if w==companion(2*group+flip):return companion_path(2*group+flip,g)
    raise ValueError('W9 complete image tail dispatcher missed a label')


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong first W9 packet')
    return [edge]+tail(w,g)


def verify_walk(kind,g,edge,packet):
    if len(packet)>6:raise ValueError('W9 selected first-choice bound exceeded')
    verify_path(source(kind),g,packet,walk(kind,g,edge))


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(j9['e7']['b5']['r3']['candidate'](True))
    return dict(labels=41,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                source_rows=registry_rows({source(i) for i in (0,1)}|{companion(i) for i in range(12)}),rows=rows,image_rows=registry_rows(envelope()),previous_H9_image_rows=registry_rows(h9['envelope']()))


def verify_native_registry(output):
    import ast
    code=Path(__file__).with_name('class_a_boundary_j9_children.py').read_text()
    fn=next(n for n in ast.parse(code).body if isinstance(n,ast.FunctionDef) and n.name=='verify_native_registry')
    ids=ast.literal_eval(fn.body[0].value);ids.update(W9=64,B9=65,K9=66,L9=67,M9=68,N9=69,X2=70,X3=71,X4=72,Y2=73,Y3=74)
    rec=reconciliation()
    for name,key in [('SOURCE','source_rows'),('CANDIDATE','rows'),('IMAGE','image_rows'),('H9_IMAGE','previous_H9_image_rows')]:
        prefix='CLASS_A_W9_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/oracle W9 registry disagreement')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=companion_edges=walk_edges=image_tail_edges=max_walk=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);A=g.n+g.d;counts=[];image=set()
            for kind in (0,1):
                w=source(kind);assert g.interior(w)
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(A+2) for j in range(A+2) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual));assert len(actual)==count(k,t)
                for edge in sorted(actual):
                    i,j,v=edge;image.add(v);witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    packet=walk(kind,g,edge);verify_walk(kind,g,edge,packet);walk_edges+=len(packet);max_walk=max(max_walk,len(packet))
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==4 and p[0] in actual
                path_edges+=len(p);pairs+=(A+2)**2;accepted+=len(actual);counts.append(len(actual))
                if k==0:
                    assert g.child(h9['source'](1-kind),0,0)==w
                    assert g.child(h9['source'](1-kind),A+1,A+1)==w
            assert image==envelope() # same image in EVERY member, not only the chamber union
            for kind in range(12):
                w=companion(kind);assert g.interior(w)
                p=companion_path(kind,g);verify_path(w,g,p,p);assert len(p)==(3,3,2,5,3,2)[kind//2];companion_edges+=len(p)
            for w in sorted(envelope()):
                p=tail(w,g);verify_path(w,g,p,p);image_tail_edges+=len(p)
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts,image_labels=len(image)))
    assert set(witnesses)==envelope() and max_walk==6
    return dict(scope='finite independent implementation replay; universal nine-kind/count/member-image/path proof separate; no global BH',members=len(rows),source_cells=2*len(rows),pairs=pairs,accepted=accepted,source_path_edges=path_edges,companion_path_edges=companion_edges,all_child_walk_edges=walk_edges,all_image_tail_edges=image_tail_edges,max_selected_walk=max_walk,image_labels=16,constant_memberwise_image=True,source_exit=4,
                all_direct_children_productivity_proved=True,closed_carrier_proved=False,new_companion_stars=False,image_registered_stars=sum(interface(w,True) is not None for w in envelope()),image_uniform_exits=sum(exit_interface(w,True) is not None for w in envelope()),
                reconciliation=reconciliation(),witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
