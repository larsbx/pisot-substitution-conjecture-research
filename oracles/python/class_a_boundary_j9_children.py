"""Independent literal-word/Fraction J9 stars, half-threshold and source exits."""
from pathlib import Path
import runpy
ROOT=Path(__file__).parent
j8=runpy.run_path(str(ROOT/'class_a_boundary_j8_children.py'))
r4=j8['r4'];e7=j8['e7']
Geometry,reverse,C=j8['Geometry'],j8['reverse'],j8['C']
BASE=((2,0,1,2,-6),(0,2,-1,-4,7),(0,0,1,3,-6))


def source(kind):
    if kind not in range(6):raise ValueError('unknown J9/companion orientation')
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def interface(w,include_new=False):
    old=j8['interface'](w,True)
    if old is not None:return old
    return 'J9' if include_new and w in (source(0),source(1)) else None


def exit_interface(w,include_new=False):
    old=j8['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        for group,name in enumerate(('J9','P9','H9')):
            if w in (source(2*group),source(2*group+1)):return name
    return None


def envelope():
    base=({(0,2,-1,-4,r) for r in range(6,10)}|{(2,2,-2,-4,r) for r in range(8,11)}|
          {(2,0,-2,-4,r) for r in range(7,11)}|{(1,2,-2,-4,r) for r in (9,10)}|{(1,0,-2,-4,r) for r in range(7,11)})
    out=base|{reverse(w) for w in base}
    assert len(out)==34
    return out


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(e7['b5']['r3']['candidate'](True))
    return dict(labels=41,terminal_labels=1,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                source_rows=registry_rows({source(i) for i in range(6)}),rows=rows,image_rows=registry_rows(envelope()),previous_E7_image_rows=registry_rows(e7['envelope']()))


def verify_native_registry(output):
    ids={None:0,'terminal':1,'T':2,'U':3,'V':4,'E':5,'T1':6,'T2':7,'Q3':8,'X':9,'R3':10,'D3':11,'P0':12,'P1':13,'H3':14,'H1':15,'H2':16,'B3':17,'Dxx':18,'B4':19,'D0':20,'F4':21,'L':22,'R4':23,'E4':24,'D4':25,'Y4':26,'E5':27,'G5':28,'R5':29,'D5':30,'M5':31,'CM':32,'F0':33,'B5':37,'E6':38,'J6':39,'K6':40,'L6':41,'J':42,'E7':43,'H5':46,'J8':47,'H8':48,'R8':50,'S8':51,'A8':52,'B8':53,'C8':54,'Q8':56,'W8':57,'J9':61,'P9':62,'H9':63}
    rec=reconciliation()
    for name,key in [('SOURCE','source_rows'),('CANDIDATE','rows'),('IMAGE','image_rows'),('E7_IMAGE','previous_E7_image_rows')]:
        prefix='CLASS_A_J9_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/source-oracle registry disagreement')


def high(k,t):
    if min(k,t)<0:raise ValueError('negative parameter')
    return t+2>=k


def count(k,t):
    if min(k,t)<0:raise ValueError('negative parameter')
    n=k+t+3;m=t-k
    if m<=-3:return 4*t+9
    if m==-2:return 2*n-1
    if m==-1:return 2*n+1
    return 2*n+min(m,2)+2-(k==0)


def predicted(kind,g,i,j):
    if kind not in (0,1) or g.eps!=-1:raise ValueError('only J9 minus complete-star interface')
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j);n,k,t,A=g.n,g.k,g.t,g.n+g.d;s=int(high(k,t))
    if a==0:return n+k+2+(k==0)<=b<=n+k+4+s
    if 1<=a<=n-1:
        if 1<=b<=A:return b-a in (n+k+3+s,n+k+4+s)
        return b==A+1 and 2*t+2-s<=a<=2*t+4
    if a==n:return -1<=t-k<=2 if b==A+1 else 2*n+k+4<=b<=min(A,2*n+k+5)
    return False


def path(kind,g):
    source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group,flip=divmod(kind,2);k,n=g.k,g.n
    if group==0:out=[(0,n+k+3,source(2))]+path(2,g)
    elif group==1:out=([(0,0,source(4))]+path(4,g) if k==0 else [(k,0,r4['source'](11))]+r4['path'](11,g))
    else:out=[(0,k+1,r4['source'](10))]+r4['path'](10,g)
    return [(j,i,reverse(w)) for i,j,w in out] if flip else out


def path_length(kind,g):return (8 if g.k==0 else 7,7 if g.k==0 else 6,6)[kind//2]


def verify_path(w,g,packet,want):j8['verify_path'](w,g,packet,want)


def registered_tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('outside J9 image tail interface')
    for flip in (0,1):
        if w==source(2+flip):return path(2+flip,g)
    raise ValueError('no registered uniform J9-image tail')


def verify_star(kind,g,edges):
    if kind not in (0,1) or len(edges)!=count(g.k,g.t) or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate/unsupported J9 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong indexed full typed target')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=registered_edges=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);n,A=g.n,g.n+g.d;counts=[]
            # Independent integer reduction and rational sign; no imported guard.
            g4=(4,-n-3,1);q=(2,-2*n-5,2)
            assert tuple(a+b for a,b in zip(g.times_beta(g4),g4))==(2,1-k,0)
            assert g.times_beta(q)==(-4,n+t-k+5,-1)
            assert g.sign(g4)==(1 if k<=1 else -1)
            assert g.sign(q)==(1 if high(k,t) else -1)
            for kind in range(6):
                w=source(kind);assert g.interior(w)
                p=path(kind,g);verify_path(w,g,p,p);assert len(p)==path_length(kind,g);path_edges+=len(p)
                if kind>=2:continue
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(len(g.words[w[0]])) for j in range(len(g.words[w[1]])) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual));assert p[0] in actual
                for i,j,v in sorted(actual):
                    assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                pairs+=len(g.words[w[0]])*len(g.words[w[1]]);accepted+=len(actual);counts.append(len(actual))
            for flip in (0,1):
                w=source(2+flip);p=registered_tail(w,g);verify_path(w,g,p,p);registered_edges+=len(p)
            p=path(2,g);assert p[0][2] not in envelope()
            if t>=4:assert g.child(e7['source'](0),2*n+6,0)==source(0)
            else:
                i=2*n+6
                if i<=A+1:assert g.child(e7['source'](0),i,0)!=source(0)
            rows.append(dict(k=k,t=t,n=n,d=g.d,v_half_high=high(k,t),counts=counts))
    assert set(witnesses)==envelope()
    rec=reconciliation()
    return dict(scope='finite exact implementation replay; universal guards/separator/path proof separate; no global BH',members=len(rows),source_cells=2*len(rows),path_source_cells=6*len(rows),pairs=pairs,accepted=accepted,
                source_and_companion_path_edges=path_edges,registered_image_tail_edges=registered_edges,image_labels=34,source_exit_k0=8,source_exit_kpositive=7,P9_exit_k0=7,P9_exit_kpositive=6,H9_exit=6,
                all_direct_children_productivity_proved=False,new_companion_stars=False,closed_carrier_proved=False,image_registered_stars=sum(r['after'] is not None for r in rec['image_rows']),image_uniform_exits=sum(r['after_exit'] is not None for r in rec['image_rows']),
                previous_E7_image_registered_stars=sum(r['after'] is not None for r in rec['previous_E7_image_rows']),previous_E7_image_uniform_exits=sum(r['after_exit'] is not None for r in rec['previous_E7_image_rows']),
                reconciliation=rec,witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
