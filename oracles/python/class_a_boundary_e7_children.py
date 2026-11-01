"""Independent exact E7 complete stars, half-chambers and uniform exits."""
from pathlib import Path
import runpy
ROOT=Path(__file__).parent
e6=runpy.run_path(str(ROOT/'class_a_boundary_e6_children.py'))
b5=e6['b5'];h3=e6['h3'];pp=e6['pp']
b4=e6['b5']['y4']['b4']
h5=runpy.run_path(str(ROOT/'class_a_boundary_h5_children.py'))
e2=runpy.run_path(str(ROOT/'class_a_boundary_e2_children.py'))
Geometry,reverse,C=e6['Geometry'],e6['reverse'],e6['C']
BASE=((0,0,0,1,1),(0,0,1,2,-3),(0,0,1,2,-4))


def source(kind):
    if kind not in range(6):raise ValueError('unknown E7/companion orientation')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def interface(w,include_new=False):
    old=e6['interface'](w,True)
    if old is not None:return old
    if w in (h3['source'](2),h3['source'](3)):return 'J'
    if w in (h5['source'](0),h5['source'](1)):return 'H5'
    return 'E7' if include_new and w in (source(0),source(1)) else None


def exit_interface(w,include_new=False):
    old=e6['exit_interface'](w,True)
    if old is not None:return old
    if w in (h3['source'](2),h3['source'](3)):return 'J'
    if w in (h5['source'](0),h5['source'](1)):return 'H5'
    if include_new and w in (source(0),source(1)):return 'E7'
    return None


def envelope():
    base=({(2,0,1,2,r) for r in range(-7,-3)}|{(2,2,2,2,r) for r in range(-8,-5)}|
          {(0,0,1,2,r) for r in range(-7,-2)}|{(0,2,2,2,r) for r in range(-8,-4)})
    out=base|{reverse(w) for w in base}
    assert len(out)==32
    return out


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(b5['r3']['candidate'](True))
    return dict(labels=41,terminal_labels=1,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                rows=rows,image_rows=registry_rows(envelope()),previous_B5_image_rows=registry_rows(b5['envelope']()),reused_complete_families=['J','H5'])


def verify_native_registry(output):
    ids={None:0,'terminal':1,'T':2,'U':3,'V':4,'E':5,'T1':6,'T2':7,'Q3':8,'X':9,'R3':10,'D3':11,'P0':12,'P1':13,'H3':14,'H1':15,'H2':16,'B3':17,'Dxx':18,'B4':19,'D0':20,'F4':21,'L':22,'R4':23,'E4':24,'D4':25,'Y4':26,'E5':27,'G5':28,'R5':29,'D5':30,'M5':31,'CM':32,'F0':33,'B5':37,'E6':38,'J6':39,'K6':40,'L6':41,'J':42,'E7':43,'U7':44,'V7':45,'H5':46}
    rec=reconciliation()
    for name,key in [('CANDIDATE','rows'),('IMAGE','image_rows'),('B5_IMAGE','previous_B5_image_rows')]:
        prefix='CLASS_A_E7_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/source-oracle registry disagreement')


def high(k,t):return t>k or(t==k and k>=2)


def predicted(kind,g,i,j):
    if kind not in (0,1) or g.eps!=-1:raise ValueError('only E7 minus complete-star interface')
    A=g.n+g.d
    if not(0<=i<=A+1 and 0<=j<=A+1):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j);n,t=g.n,g.t;e=int(high(g.k,t))
    if 1<=a<=A:
        if b==0:return 2*n+4<=a<=2*n+6+e
        return 1<=b<=A and a-b in (2*n+5+e,2*n+6+e)
    if a==A+1:return t<=3+e if b==0 else max(1,t-3-e)<=b<=t-1
    return False


def path(kind,g):
    source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group=kind//2
    if group==0:
        out=([(g.n+g.d+1,0,source(2+2*g.t))]+path(2+2*g.t,g) if g.t<=1 else
             [(2*g.n+4,0,h3['source'](2))]+h3['path'](2,g))
    elif group==1:return b4['path'](3-kind%2,g)
    else:
        if g.n==3:return e2['path'](2+kind%2,g)
        out=[(g.t+5,1,pp['source'](5))]+pp['path'](5,g)
    return [(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def verify_path(w,g,packet,want):e6['verify_path'](w,g,packet,want)


def registered_tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('outside E7 image tail interface')
    for flip in (0,1):
        if w==h3['source'](2+flip):return h3['path'](2+flip,g)
        if w==h5['source'](flip):return h5['path'](flip,g)
        for group in (1,2):
            if w==source(2*group+flip):return path(2*group+flip,g)
    raise ValueError('no registered uniform E7-image tail')


def uniform_b5_tail(w,g):
    if g.eps!=-1 or w not in b5['envelope']():raise ValueError('outside B5 image uniform tail interface')
    for flip in (0,1):
        if w==source(flip):return path(flip,g)
    return b5['tail'](w,g)


def verify_star(kind,g,edges):
    if kind not in (0,1) or len(edges)!=max(1,2*g.t-1) or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate/unsupported E7 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong full typed target or geometry')


def path_length(kind,g):return (3 if g.t<=1 else 5,2,4 if g.n==3 else 2)[kind//2]


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=registered_tail_edges=b5_uniform_tail_edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);n,A=g.n,g.n+g.d;counts=[]
            for kind in range(6):
                w=source(kind);assert g.interior(w)
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==path_length(kind,g);path_edges+=len(p)
                if kind>=2:continue
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(A+2) for j in range(A+2) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual))
                for i,j,v in sorted(actual):
                    assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                if t<=1:assert actual=={p[0]}
                else:assert p[0] in actual
                pairs+=(A+2)**2;accepted+=len(actual);counts.append(len(actual))
            for w in envelope():
                if exit_interface(w,True) is not None:
                    p=registered_tail(w,g);verify_path(w,g,p,p);registered_tail_edges+=len(p)
            for w in b5['envelope']():
                p=uniform_b5_tail(w,g);verify_path(w,g,p,p);assert len(p)<=7;b5_uniform_tail_edges+=len(p)
            if n==4:
                for flip in (0,1):assert path(flip,g)==b5['path'](4+flip,g)
            rows.append(dict(k=k,t=t,n=n,d=g.d,half_high=high(k,t),counts=counts))
    assert set(witnesses)==envelope()
    rec=reconciliation()
    return dict(scope='finite exact implementation replay; universal nine-kind/half-chamber proof separate; no global BH',members=len(rows),source_cells=2*len(rows),path_source_cells=6*len(rows),pairs=pairs,accepted=accepted,
                source_and_companion_path_edges=path_edges,registered_image_tail_edges=registered_tail_edges,uniform_B5_image_tail_edges=b5_uniform_tail_edges,image_labels=32,source_exit_bound=5,source_exit_tle1=3,source_exit_tge2=5,
                all_direct_children_productive_tle1=True,all_direct_children_productive_all_t_proved=False,closed_carrier_proved=False,image_registered_stars=sum(r['after'] is not None for r in rec['image_rows']),image_uniform_exits=sum(r['after_exit'] is not None for r in rec['image_rows']),
                previous_B5_image_registered_stars=sum(r['after'] is not None for r in rec['previous_B5_image_rows']),previous_B5_image_uniform_exits=sum(r['after_exit'] is not None for r in rec['previous_B5_image_rows']),reconciliation=rec,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
