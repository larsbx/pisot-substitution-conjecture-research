"""Independent exact J8 literal stars, k=0 separator and guarded typed tails."""
from pathlib import Path
import runpy
ROOT=Path(__file__).parent
d0=runpy.run_path(str(ROOT/'class_a_boundary_d0_children.py'))
e7=d0['e7'];r4=e7['e6']['r4'];b4=e7['b4'];h3=e7['h3'];pp=e7['pp'];p3=d0['p3']
Geometry,reverse,C=d0['Geometry'],d0['reverse'],d0['C']
BASE=((2,0,1,2,-5),(0,0,-1,-3,4),(0,2,0,-3,4),(2,2,-1,-3,5),(2,2,-1,-3,6),
      (1,2,-1,-3,5),(1,2,-1,-3,6),(0,1,1,2,-5),(2,0,0,3,-5),(1,1,1,2,-5),
      (0,0,0,-3,5),(0,0,2,3,-6),(1,1,1,2,-4),(1,2,-1,-3,7))
NAMES=('J8','H8','L','R8','S8','A8','B8','C8','G5','Q8','W8','Z8','D8','L8')


def source(kind):
    if kind not in range(28):raise ValueError('unknown J8/companion orientation')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def interface(w,include_new=False):
    old=d0['interface'](w,True)
    if old is not None:return old
    return 'J8' if include_new and w in (source(0),source(1)) else None


def exit_interface(w,include_new=False):
    old=d0['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        for group in range(11):
            if w in (source(2*group),source(2*group+1)):return NAMES[group]
    return None


def envelope():
    base={BASE[g] for g in (1,2,3,4,5,6,13)}|{r4['source'](4),r4['source'](10)}
    out=base|{reverse(w) for w in base}
    assert len(out)==18
    return out


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(e7['b5']['r3']['candidate'](True))
    return dict(labels=41,terminal_labels=1,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                source_rows=registry_rows({source(i) for i in range(28)}),rows=rows,image_rows=registry_rows(envelope()),previous_E7_image_rows=registry_rows(e7['envelope']()))


def verify_native_registry(output):
    ids={None:0,'terminal':1,'T':2,'U':3,'V':4,'E':5,'T1':6,'T2':7,'Q3':8,'X':9,'R3':10,'D3':11,'P0':12,'P1':13,'H3':14,'H1':15,'H2':16,'B3':17,'Dxx':18,'B4':19,'D0':20,'F4':21,'L':22,'R4':23,'E4':24,'D4':25,'Y4':26,'E5':27,'G5':28,'R5':29,'D5':30,'M5':31,'CM':32,'F0':33,'B5':37,'E6':38,'J6':39,'K6':40,'L6':41,'J':42,'E7':43,'H5':46}
    ids.update({name:47+i for i,name in enumerate(NAMES[:11]) if i not in (2,8)})
    rec=reconciliation()
    for name,key in [('SOURCE','source_rows'),('CANDIDATE','rows'),('IMAGE','image_rows'),('E7_IMAGE','previous_E7_image_rows')]:
        prefix='CLASS_A_J8_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/source-oracle registry disagreement')


def predicted(kind,g,i,j):
    if kind not in (0,1) or g.eps!=-1:raise ValueError('only J8 minus complete-star interface')
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j);n,k,A=g.n,g.k,g.n+g.d
    if a==0:return k==0 if b==0 else max(1,k)<=b<=k+2
    if 1<=a<=n-1:return 1<=b<=A and b-a in (k+1,k+2)
    return a==n and n+k+1<=b<=n+k+2+(k==0)


def path(kind,g):
    source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group,flip=divmod(kind,2);k,t,n,d=g.k,g.t,g.n,g.d
    if group in (11,13) and k!=0:raise ValueError('k=0-only companion tail')
    if group==12 and k!=1:raise ValueError('k=1-only companion tail')
    if group==0:out=[(0,2 if k==0 else k,r4['source'](10 if k==0 else 4))]+r4['path'](10 if k==0 else 4,g)
    elif group==1:out=[(0,d+4,p3['source'](5 if n==3 else 3))]+p3['path'](5 if n==3 else 3,g)
    elif group==2:return h3['path'](7-flip,g)
    elif group==3:out=([(0,n,source(14))]+path(14,g) if k==0 else [(0,t+3,h3['source'](5))]+h3['path'](5,g))
    elif group==4:out=[(k+1,0,source(16))]+path(16,g)
    elif group==5:out=([(0,n,source(18 if k==0 else 24))]+path(18 if k==0 else 24,g) if k<=1 else [(1,t+4,pp['source'](3))]+pp['path'](3,g))
    elif group==6:out=[(k+1,0,source(0))]+path(0,g)
    elif group==7:out=[(0,k+1,b4['source'](4))]+b4['path'](4,g)
    elif group==8:return r4['path'](11-flip,g)
    elif group==9:out=[(1,k+2,source(6))]+path(6,g)
    elif group==10:out=[(2*n,0,h3['source'](2))]+h3['path'](2,g)
    elif group==11:out=[(n+d+1,0,source(20))]+path(20,g)
    elif group==12:out=[(t+4,1,pp['source'](7))]+pp['path'](7,g)
    else:out=[(n+1,0,source(22))]+path(22,g)
    return [(j,i,reverse(w)) for i,j,w in out] if flip else out


def path_length(kind,g):
    return (6 if g.k==0 else 4,2,2,6 if g.k==0 else 4,6,8 if g.k==0 else 4,7 if g.k==0 else 5,5,5,7 if g.k==0 else 5,5,6,3,7)[kind//2]


def verify_path(w,g,packet,want):e7['verify_path'](w,g,packet,want)


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('outside J8 image tail interface')
    for flip in (0,1):
        for group in (1,2,3,4,5,6,13):
            if w==source(2*group+flip):return path(2*group+flip,g)
        for group in (2,5):
            if w==r4['source'](2*group+flip):return r4['path'](2*group+flip,g)
    raise ValueError('J8 image tail dispatch missed a label')


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong first indexed packet')
    return [edge]+tail(w,g)


def verify_walk(kind,g,edge,packet):
    if len(packet)>9:raise ValueError('J8 walk bound exceeded')
    verify_path(source(kind),g,packet,walk(kind,g,edge))


def verify_star(kind,g,edges):
    if kind not in (0,1) or len(edges)!=2*g.n+3+(g.k==0) or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate/unsupported J8 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong indexed full typed target')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=path_cells=walk_edges=tail_edges=max_walk=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);n,A=g.n,g.n+g.d;counts=[]
            # The cubic identity is independently evaluated at beta using rational signs.
            q=(3,-n-3,1)
            assert g.sign(q)==(1 if k==0 else -1)
            assert g.interior(source(26))==(k==0)
            for kind in range(28):
                group=kind//2
                if (group in (11,13) and k!=0) or (group==12 and k!=1):continue
                w=source(kind);assert g.interior(w)
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==path_length(kind,g)
                path_edges+=len(p);path_cells+=1
                if kind>=2:continue
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(len(g.words[w[0]])) for j in range(len(g.words[w[1]])) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual))
                for edge in sorted(actual):
                    i,j,v=edge;assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    packet=walk(kind,g,edge);verify_walk(kind,g,edge,packet)
                    walk_edges+=len(packet);max_walk=max(max_walk,len(packet))
                assert p[0] in actual
                pairs+=len(g.words[w[0]])*len(g.words[w[1]]);accepted+=len(actual);counts.append(len(actual))
            for w in envelope():
                if w in (source(26),source(27)) and k!=0:continue
                p=tail(w,g);verify_path(w,g,p,p);assert len(p)<=8;tail_edges+=len(p)
            assert g.child(source(0),n,n+k+2)==source(12) and g.child(source(12),k+1,0)==source(0)
            if t>=3:assert g.child(e7['source'](0),2*n+5,0)==source(0)
            else:
                i=2*n+5
                if i<=A+1:assert g.child(e7['source'](0),i,0)!=source(0)
            rows.append(dict(k=k,t=t,n=n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and max_walk==9
    rec=reconciliation()
    return dict(scope='finite exact implementation replay; universal guard/path proof separate; no global BH',members=len(rows),source_cells=2*len(rows),path_source_cells=path_cells,pairs=pairs,accepted=accepted,
                source_and_companion_path_edges=path_edges,all_child_walk_edges=walk_edges,guarded_image_tail_edges=tail_edges,max_walk=max_walk,image_labels=18,source_exit_k0=6,source_exit_kpositive=4,child_tail_bound=8,walk_bound=9,
                all_actual_direct_children_productive=True,all_image_labels_full_cone_uniform_sources=False,conditional_L8_k0_only=True,new_companion_stars=False,closed_carrier_proved=False,
                image_registered_stars=sum(r['after'] is not None for r in rec['image_rows']),image_uniform_exits=sum(r['after_exit'] is not None for r in rec['image_rows']),previous_E7_image_registered_stars=sum(r['after'] is not None for r in rec['previous_E7_image_rows']),previous_E7_image_uniform_exits=sum(r['after_exit'] is not None for r in rec['previous_E7_image_rows']),
                reconciliation=rec,witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
