"""Independent literal-word/Fraction E6 complete stars and all-child walks."""
from pathlib import Path
import runpy
ROOT=Path(__file__).parent
b5=runpy.run_path(str(ROOT/'class_a_boundary_b5_children.py'))
y4=b5['y4'];r4=y4['r4'];pp=y4['pp']
eh=runpy.run_path(str(ROOT/'class_a_boundary_e_children.py'))
h3=runpy.run_path(str(ROOT/'class_a_boundary_h3_children.py'))
Geometry,reverse,C=b5['Geometry'],b5['reverse'],b5['C']
BASE=((0,0,0,1,0),(0,2,1,1,-4),(0,2,1,1,-3),(0,2,1,1,-2))


def source(kind):
    if kind not in range(8):raise ValueError('unknown E6/companion orientation')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def interface(w,include_new=False):
    old=b5['interface'](w,True)
    if old is not None:return old
    return 'E6' if include_new and w in (source(0),source(1)) else None


def exit_interface(w,include_new=False):
    old=b5['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        for group,name in [(1,'J6'),(2,'K6'),(3,'L6')]:
            if w in (source(2*group),source(2*group+1)):return name
    return None


def envelope():
    base=({(2,0,0,1,r) for r in (-3,-2,-1)}|{(2,2,1,1,r) for r in (-4,-3)}|{(0,2,1,1,r) for r in (-4,-3,-2)})
    out=base|{reverse(w) for w in base}
    assert len(out)==16
    return out


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(b5['r3']['candidate'](True))
    return dict(labels=41,terminal_labels=1,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),rows=rows,image_rows=registry_rows(envelope()),previous_B5_image_rows=registry_rows(b5['envelope']()))


def verify_native_registry(output):
    ids={None:0,'terminal':1,'T':2,'U':3,'V':4,'E':5,'T1':6,'T2':7,'Q3':8,'X':9,'R3':10,'D3':11,'P0':12,'P1':13,'H3':14,'H1':15,'H2':16,'B3':17,'Dxx':18,'B4':19,'D0':20,'F4':21,'L':22,'R4':23,'E4':24,'D4':25,'Y4':26,'E5':27,'G5':28,'R5':29,'D5':30,'M5':31,'CM':32,'F0':33,'B5':37,'E6':38,'J6':39,'K6':40,'L6':41}
    rec=reconciliation()
    for name,key in [('CANDIDATE','rows'),('IMAGE','image_rows'),('B5_IMAGE','previous_B5_image_rows')]:
        prefix='CLASS_A_E6_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/source-oracle registry disagreement')


def predicted(kind,g,i,j):
    if kind not in (0,1) or g.eps!=-1:raise ValueError('only E6 minus complete-star interface')
    A=g.n+g.d
    if not(0<=i<=A+1 and 0<=j<=A+1):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j)
    if 1<=a<=A:
        if b==0:return g.n+2<=a<=g.n+4
        return 1<=b<=A and a-b in (g.n+3,g.n+4)
    return a==A+1 and g.d-3<=b<=g.d-1


def path(kind,g):
    source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group=kind//2
    if group==0:return b5['path'](2+kind%2,g)
    if group==1:out=[(0,g.k+1,r4['source'](4))]+r4['path'](4,g)
    elif group==2:out=[(g.t+3,0,b5['source'](0))]+b5['path'](0,g)
    else:out=[(g.d+2,0,y4['p3']['source'](2)),(1,2,C)]
    return [(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def verify_path(w,g,packet,want):b5['verify_path'](w,g,packet,want)


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('no E6-image tail interface')
    for flip in (0,1):
        for kind in (2+flip,4+flip):
            if w==eh['source'](kind):return eh['short_path'](kind,g)
        if w==h3['source'](flip):return h3['path'](flip,g)
        for group in (0,1):
            kind=2*group+flip
            if w==pp['source'](kind):return pp['path'](kind,g)
        for group in (1,2,3):
            kind=2*group+flip
            if w==source(kind):return path(kind,g)
    raise ValueError('complete E6 tail dispatch missed label')


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong first indexed E6 packet')
    return [edge]+tail(w,g)


def verify_walk(kind,g,edge,packet):
    if len(packet)>9:raise ValueError('E6 walk exceeds bound')
    verify_path(source(kind),g,packet,walk(kind,g,edge))


def verify_star(kind,g,edges):
    if kind not in (0,1) or len(edges)!=2*g.d-1 or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate/unsupported E6 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong full typed target or geometry')


def path_length(kind,g):return (2,8 if g.n==3 else 4,3,2)[kind//2]


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=walk_edges=max_walk=0
    S=b5['r3']['candidate'](True)
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);n,d,A=g.n,g.d,g.n+g.d;counts=[];local_labels=set()
            for kind in range(8):
                w=source(kind);assert g.interior(w)
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==path_length(kind,g);path_edges+=len(p)
                if kind>=2:continue
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(A+2) for j in range(A+2) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual))
                for edge in sorted(actual):
                    i,j,v=edge;local_labels.add(v);assert v in envelope() and exit_interface(v,True) is not None
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    packet=walk(kind,g,edge);verify_walk(kind,g,edge,packet)
                    assert len(packet)<=9;walk_edges+=len(packet);max_walk=max(max_walk,len(packet))
                pairs+=(A+2)**2;accepted+=len(actual);counts.append(len(actual))
            assert local_labels==envelope()
            assert g.child(source(0),A+1,d-2)==source(4) not in S
            assert g.child(source(4),t+3,0)==b5['source'](0) not in envelope()
            assert not g.interior(g.child(source(0),n+1,0))
            assert not g.interior(g.child(source(0),A+1,d))
            if n==3:
                assert g.child(b5['source'](0),0,A+1)==source(0)
            rows.append(dict(k=k,t=t,n=n,d=d,counts=counts))
    assert set(witnesses)==envelope() and max_walk==9
    rec=reconciliation()
    return dict(scope='finite exact implementation replay; universal guard and tail proof separate; no global BH',members=len(rows),source_cells=2*len(rows),path_source_cells=8*len(rows),pairs=pairs,accepted=accepted,
                source_and_companion_path_edges=path_edges,all_child_walk_edges=walk_edges,max_walk=max_walk,image_labels=16,every_member_image_labels=16,source_exit_bound=2,child_tail_bound=8,walk_bound=9,
                all_direct_children_productive=True,all_image_labels_uniform_exit=True,companion_complete_stars_proved=False,closed_carrier_proved=False,n3_three_cycle=True,
                image_registered_stars=sum(r['after'] is not None for r in rec['image_rows']),image_uniform_exits=sum(r['after_exit'] is not None for r in rec['image_rows']),previous_B5_image_registered_stars=sum(r['after'] is not None for r in rec['previous_B5_image_rows']),
                reconciliation=rec,witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
