"""Independent literal-word/Fraction B5 stars and every-first-choice replay."""
from pathlib import Path
import runpy
ROOT=Path(__file__).parent
y4=runpy.run_path(str(ROOT/'class_a_boundary_y4_children.py'))
r3=y4['b3']['r3']
q3=runpy.run_path(str(ROOT/'class_a_boundary_q3_children.py'))
Geometry,reverse,C=y4['Geometry'],y4['reverse'],y4['C']
BASE=((2,0,-1,-2,3),(0,0,0,1,0),(0,0,0,1,1))


def source(kind):
    if kind not in range(6):raise ValueError('unknown B5/endpoint orientation')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def interface(w,include_new=False):
    old=y4['interface'](w,True)
    if old is not None:return old
    return 'B5' if include_new and w in (source(0),source(1)) else None


def exit_interface(w,include_new=False):
    old=y4['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        for group,name in [(0,'B5'),(1,'E6')]:
            if w in (source(2*group),source(2*group+1)):return name
    return None


def envelope():
    base=({(0,2,0,1,r) for r in range(-2,2)}|
          {(0,0,0,1,r) for r in (0,1)}|
          {(2,2,-1,1,r) for r in (1,2)}|
          {(2,0,-1,1,r) for r in range(-1,3)})
    out=base|{reverse(w) for w in base}
    assert len(out)==24
    return out


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(r3['candidate'](True))
    return dict(labels=41,terminal_labels=1,before_registered_including_terminal=sum(r['before'] is not None for r in rows),
                after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),
                after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                rows=rows,image_rows=registry_rows(envelope()))


def verify_native_registry(output):
    ids={None:0,'terminal':1,'T':2,'U':3,'V':4,'E':5,'T1':6,'T2':7,'Q3':8,'X':9,
         'R3':10,'D3':11,'P0':12,'P1':13,'H3':14,'H1':15,'H2':16,'B3':17,'Dxx':18,
         'B4':19,'D0':20,'F4':21,'L':22,'R4':23,'E4':24,'D4':25,'Y4':26,'E5':27,'G5':28,
         'R5':29,'D5':30,'M5':31,'CM':32,'F0':33,'B5':37,'E6':38}
    rec=reconciliation()
    for name,key in [('CANDIDATE','rows'),('IMAGE','image_rows')]:
        prefix='CLASS_A_B5_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/source-oracle registry disagreement')


def predicted(kind,g,i,j):
    if kind not in (0,1) or g.eps!=-1:raise ValueError('only B5 minus complete-star interface')
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j)
    n,d,A=g.n,g.d,g.n+g.d
    if a==0:return d+2<=b<=min(A,d+5) or(b==A+1 and n<=4)
    if 1<=a<=n-1:
        if 1<=b<=A:return b-a in (d+4,d+5)
        return b==A+1 and a>=max(1,n-4)
    return False


def path(kind,g):
    source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group=kind//2
    if group==0:out=[(0,g.d+3,y4['p3']['source'](3)),(2,1,C)]
    elif group==1:out=[(g.n+2,0,(2,0,0,1,-1)),(2,1,C)]
    else:
        if g.n!=4:raise ValueError('E7 tail is scoped to n=4 only')
        out=[(g.n+g.d+1,0,(0,0,1,2,-3-g.t))]
        out+=([(9,0,y4['p3']['source'](2)),(1,2,C)] if g.t==0 else [(6,1,(2,2,0,-2,2)),(1,3,C)])
    return [(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def verify_path(w,g,packet,want):y4['verify_path'](w,g,packet,want)


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('no B5-image tail interface')
    if w in y4['envelope']():return y4['tail'](w,g)
    for flip in (0,1):
        if w==q3['source'](flip):return q3['path'](flip,g)
        if w==r3['source'](flip):return r3['path'](flip,g)
        for group in (1,2):
            if w==source(2*group+flip):return path(2*group+flip,g)
    raise ValueError('complete B5 tail dispatch missed a label')


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong first indexed packet')
    return [edge]+tail(w,g)


def verify_walk(kind,g,edge,packet):
    if len(packet)>8:raise ValueError('walk bound exceeded')
    verify_path(source(kind),g,packet,walk(kind,g,edge))


def verify_star(kind,g,edges):
    if kind not in (0,1) or len(edges)!=2*g.n-1 or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate/unsupported star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong indexed full typed target')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=walk_edges=max_walk=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);n,A=g.n,g.n+g.d;counts=[]
            for kind in (0,1):
                w=source(kind);assert g.interior(w)
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(len(g.words[w[0]])) for j in range(len(g.words[w[1]])) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual))
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==2;path_edges+=len(p)
                for edge in sorted(actual):
                    i,j,v=edge
                    assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    packet=walk(kind,g,edge);verify_walk(kind,g,edge,packet)
                    walk_edges+=len(packet);max_walk=max(max_walk,len(packet))
                assert g.child(y4['source'](2+kind),0 if kind else t+1,t+1 if kind else 0)==w
                pairs+=len(g.words[w[0]])*len(g.words[w[1]]);accepted+=len(actual);counts.append(len(actual))
            for kind in (2,3):
                p=path(kind,g);verify_path(source(kind),g,p,p);path_edges+=len(p)
            if n==4:
                for kind in (4,5):
                    p=path(kind,g);verify_path(source(kind),g,p,p);path_edges+=len(p)
            rows.append(dict(k=k,t=t,n=n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and max_walk==8
    rec=reconciliation()
    return dict(scope='finite exact implementation replay; universal guards and finite endpoint proof separate; no global BH',members=len(rows),source_cells=2*len(rows),pairs=pairs,accepted=accepted,
                source_and_companion_path_edges=path_edges,all_child_walk_edges=walk_edges,max_walk=max_walk,image_labels=24,source_exit_bound=2,child_tail_bound=7,walk_bound=8,
                all_direct_children_productive=True,uniform_companion_E6_exit_bound=2,E7_tail_n4_only=True,E7_uniform_exit_registered=False,
                image_registered_stars=sum(r['after'] is not None for r in rec['image_rows']),image_uniform_exits=sum(r['after_exit'] is not None for r in rec['image_rows']),
                reconciliation=rec,closed_carrier_proved=False,witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
