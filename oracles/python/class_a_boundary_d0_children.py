"""Independent literal-word/Fraction D0 stars and every-first-choice replay."""
from pathlib import Path
import runpy
ROOT=Path(__file__).parent
e7=runpy.run_path(str(ROOT/'class_a_boundary_e7_children.py'))
b5=e7['b5'];y4=b5['y4'];p3=y4['p3']
Geometry,reverse,C=e7['Geometry'],e7['reverse'],e7['C']


def source(kind):
    if kind not in (0,1):raise ValueError('unknown D0 orientation')
    w=(0,0,1,2,-3)
    return reverse(w) if kind else w


def interface(w,include_new=False):
    old=e7['interface'](w,True)
    if old is not None:return old
    return 'D0' if include_new and w in (source(0),source(1)) else None


def exit_interface(w,include_new=False):
    return e7['exit_interface'](w,True)


def envelope():
    base=({(2,0,0,-1,r) for r in range(-1,3)}|
          {(2,2,1,-1,r) for r in (-2,-1)}|
          {(0,0,0,-1,r) for r in (-1,0)}|
          {(0,2,1,-1,r) for r in range(-2,2)})
    out=base|{reverse(w) for w in base}
    assert len(out)==24
    return out


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(b5['r3']['candidate'](True))
    return dict(labels=41,terminal_labels=1,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                source_rows=registry_rows({source(0),source(1)}),rows=rows,image_rows=registry_rows(envelope()),previous_E7_image_rows=registry_rows(e7['envelope']()))


def verify_native_registry(output):
    ids={None:0,'terminal':1,'T':2,'U':3,'V':4,'E':5,'T1':6,'T2':7,'Q3':8,'X':9,'R3':10,'D3':11,'P0':12,'P1':13,'H3':14,'H1':15,'H2':16,'B3':17,'Dxx':18,'B4':19,'D0':20,'F4':21,'L':22,'R4':23,'E4':24,'D4':25,'Y4':26,'E5':27,'G5':28,'R5':29,'D5':30,'M5':31,'CM':32,'F0':33,'B5':37,'E6':38,'J6':39,'K6':40,'L6':41,'J':42,'E7':43,'H5':46}
    rec=reconciliation()
    for name,key in [('SOURCE','source_rows'),('CANDIDATE','rows'),('IMAGE','image_rows'),('E7_IMAGE','previous_E7_image_rows')]:
        prefix='CLASS_A_D0_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/source-oracle registry disagreement')


def predicted(kind,g,i,j):
    if kind not in (0,1) or g.eps!=-1:raise ValueError('D0 minus interface required')
    A=g.n+g.d
    if not(0<=i<=A+1 and 0<=j<=A+1):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j)
    if 1<=a<=A:
        if b==0:return g.d+2<=a<=g.d+5
        return 1<=b<=A and a-b in (g.d+4,g.d+5)
    if a==A+1:return g.n<=4 if b==0 else max(1,g.n-4)<=b<=g.n-1
    return False


def path(kind,g):
    source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    return e7['path'](2+kind,g)


def verify_path(w,g,packet,want):e7['verify_path'](w,g,packet,want)


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('outside D0 image tail interface')
    return e7['uniform_b5_tail'](w,g)


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong first indexed packet')
    return [edge]+tail(w,g)


def verify_walk(kind,g,edge,packet):
    if len(packet)>8:raise ValueError('first-choice walk exceeds bound')
    verify_path(source(kind),g,packet,walk(kind,g,edge))


def verify_star(kind,g,edges):
    if kind not in (0,1) or len(edges)!=2*g.n-1 or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate/unsupported star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong indexed full typed target')


def probe():
    assert envelope()==b5['envelope']()
    rows=[];witnesses={};pairs=accepted=path_edges=walk_edges=tail_edges=max_walk=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);n,A=g.n,g.n+g.d;counts=[]
            for kind in (0,1):
                w=source(kind);assert w==e7['source'](2+kind) and g.interior(w)
                actual=set(g.edges(w))
                chosen={(i,j,g.child(w,i,j)) for i in range(A+2) for j in range(A+2) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                other=b5['source'](1-kind)
                assert w!=other and w[2:]==other[2:] and actual==set(g.edges(other))
                verify_star(kind,g,list(actual))
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==2;path_edges+=len(p)
                for edge in sorted(actual):
                    i,j,v=edge;assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    packet=walk(kind,g,edge);verify_walk(kind,g,edge,packet)
                    walk_edges+=len(packet);max_walk=max(max_walk,len(packet))
                pairs+=(A+2)**2;accepted+=len(actual);counts.append(len(actual))
            for w in envelope():
                p=tail(w,g);verify_path(w,g,p,p);assert len(p)<=7;tail_edges+=len(p)
            T=p3['source'](2);Y=y4['source'](0)
            assert g.child(source(0),g.d+3,0)==T
            assert g.child(T,0,1)==Y and g.interior(Y) and Y not in envelope()
            rows.append(dict(k=k,t=t,n=n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and max_walk==8
    rec=reconciliation()
    return dict(scope='finite exact implementation replay; universal nine-kind proof separate; no global BH',members=len(rows),source_cells=2*len(rows),pairs=pairs,accepted=accepted,
                source_path_edges=path_edges,all_child_walk_edges=walk_edges,uniform_image_tail_edges=tail_edges,max_walk=max_walk,image_labels=24,source_exit_bound=2,child_tail_bound=7,walk_bound=8,
                all_direct_children_productive=True,new_companion_stars_or_exits=False,image_equals_B5=True,surviving_indexed_stars_equal_reversed_B5=True,sources_equal_B5=False,
                image_registered_stars=sum(r['after'] is not None for r in rec['image_rows']),image_uniform_exits=sum(r['after_exit'] is not None for r in rec['image_rows']),closed_carrier_proved=False,
                previous_E7_image_registered_stars=sum(r['after'] is not None for r in rec['previous_E7_image_rows']),previous_E7_image_uniform_exits=sum(r['after_exit'] is not None for r in rec['previous_E7_image_rows']),
                reconciliation=rec,witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
