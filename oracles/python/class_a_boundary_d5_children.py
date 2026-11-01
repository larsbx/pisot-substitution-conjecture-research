"""Independent literal-word/integer-polynomial/Fraction D5 replay."""
from pathlib import Path
import runpy
ROOT=Path(__file__).parent
r5=runpy.run_path(str(ROOT/'class_a_boundary_r5_children.py'))
b5=runpy.run_path(str(ROOT/'class_a_boundary_b5_children.py'))
y4=r5['y4']
Geometry,reverse,C=y4['Geometry'],y4['reverse'],y4['C']
BASE=((0,1,1,-1,0),(2,1,0,-1,1),(2,1,0,-1,2),(1,1,0,1,-1))
X0=(0,0,0,0,0)


def source(kind):
    if kind not in range(9):raise ValueError('unknown D5/companion orientation')
    if kind==8:return X0
    return reverse(BASE[kind//2]) if kind%2 else BASE[kind//2]


def candidate(enlarged=False):
    out=set(y4['b3']['r3']['candidate'](True))
    return out|{source(0),source(1)} if enlarged else out


def interface(w,include_new=False):
    old=r5['interface'](w,True) or b5['interface'](w,True)
    if old is not None:return old
    if include_new:
        if w in (source(0),source(1)):return 'D5'
        if w==X0:return 'X0_terminal'
    return None


def exit_interface(w,include_new=False):
    old=r5['exit_interface'](w) or b5['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        if w==X0:return 'X0_terminal'
        for group,name in [(1,'D6'),(2,'D7'),(3,'C6')]:
            if w in (source(2*group),source(2*group+1)):return name
    return None


def envelope():return {C,X0,source(2),source(3),source(4),source(5)}


def scopes():
    return dict(S41=candidate(),S43=candidate(True),IMAGE=envelope(),
                Y4_IMAGE=y4['envelope'](),R5_IMAGE=r5['envelope'](),B5_IMAGE=b5['envelope']())


def reconciliation():
    out={}
    for name,labels in scopes().items():
        rows=[dict(label=list(w),before=interface(w),after=interface(w,True),
                   before_exit=exit_interface(w),after_exit=exit_interface(w,True),
                   typed_terminal=w in (C,X0)) for w in sorted(labels)]
        out[name]=dict(labels=len(rows),before_registered_including_terminals=sum(r['before'] is not None for r in rows),
                       after_registered_including_terminals=sum(r['after'] is not None for r in rows),
                       before_exits=sum(r['before_exit'] is not None for r in rows),after_exits=sum(r['after_exit'] is not None for r in rows),
                       typed_terminals=sum(r['typed_terminal'] for r in rows),rows=rows)
    return out


def verify_native_registry(output):
    ids={None:0,'terminal':1,'T':2,'U':3,'V':4,'E':5,'T1':6,'T2':7,'Q3':8,'X':9,
         'R3':10,'D3':11,'P0':12,'P1':13,'H3':14,'H1':15,'H2':16,'B3':17,'Dxx':18,
         'B4':19,'D0':20,'F4':21,'L':22,'R4':23,'E4':24,'D4':25,'Y4':26,'E5':27,'G5':28,
         'R5':29,'D5':30,'M5':31,'CM':32,'F0':33,'B2':34,'B2h':35,'K':36,'B5':37,'E6':38,
         'X0_terminal':39,'D6':40,'D7':41,'C6':42}
    for name,rec in reconciliation().items():
        prefix='CLASS_A_D5_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if line.startswith(prefix):
                a=tuple(map(int,line.split()[1:]))
                if len(a)!=9 or a[:5] in got:raise ValueError('malformed or duplicate native inventory row')
                got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[key]] for key in ('before','after','before_exit','after_exit')) for r in rec['rows']}
        if got!=want:raise ValueError('native/source registry disagreement in '+name)


def predicted(kind,g,i,j):
    if kind not in (0,1) or g.eps!=-1:raise ValueError('only D5 minus complete-star interface')
    w=source(kind)
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('nonexistent occurrence')
    a,b=(j,i) if kind else (i,j)
    n,d,A=g.n,g.d,g.n+g.d
    if 1<=a<=A:
        return a in (d-1,d) if b==0 else 1<=b<=n and a-b==d
    return a==A+1 and b==n+1


def path(kind,g):
    source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    if kind<2:return y4['path'](4+kind,g)
    if kind//2==1:out=[(1,3,y4['T1'])]+y4['seed_suffix'](1,0,g)
    elif kind//2==2:out=[(g.n,0,BASE[3]),(2,1,C)]
    elif kind//2==3:out=[(2,1,C)]
    else:out=[(1,1,C)]
    return [(j,i,reverse(w)) for i,j,w in out] if kind%2 else out


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('unknown D5-image tail source')
    if w==C:return []
    for kind in (2,3,4,5,8):
        if w==source(kind):return path(kind,g)
    raise ValueError('D5 tail dispatch missed a label')


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong indexed first packet')
    return [edge]+tail(w,g)


def verify_path(kind,g,packet):y4['verify_path'](source(kind),g,packet,path(kind,g))


def verify_walk(kind,g,edge,packet):
    if len(packet)>7:raise ValueError('D5 first-choice walk exceeded seven')
    y4['verify_path'](source(kind),g,packet,walk(kind,g,edge))


def verify_star(kind,g,edges):
    if kind not in (0,1) or len(edges)!=g.n+3 or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate/unsupported D5 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong actual full packet')


def probe():
    rows=[];witnesses={};pairs=accepted=source_edges=walk_edges=max_walk=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);n,d,A=g.n,g.d,g.n+g.d;counts=[]
            for kind in range(9):
                w=source(kind);assert g.interior(w)
                p=path(kind,g);verify_path(kind,g,p);assert len(p)==(1,6,2,1,1)[kind//2];source_edges+=len(p)
                if kind>=2:continue
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(len(g.words[w[0]])) for j in range(len(g.words[w[1]])) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual))
                assert sum(v==C for _,_,v in actual)==n and sum(v==X0 for _,_,v in actual)==1
                for edge in sorted(actual):
                    i,j,v=edge;assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    p=walk(kind,g,edge);verify_walk(kind,g,edge,p)
                    walk_edges+=len(p);max_walk=max(max_walk,len(p))
                assert g.child(y4['source'](kind),n if kind else A+1,A+1 if kind else n)==w
                pairs+=len(g.words[w[0]])*len(g.words[w[1]]);accepted+=len(actual);counts.append(len(actual))
            # Exact touching, including both integer RUN/RUN neighbors.
            for i,j in [(d+1,0),(d,1),(d+2,1),(A,n+1),(A+1,n)]:
                assert not g.interior(g.child(BASE[0],i,j)) and not predicted(0,g,i,j)
            assert g.child(BASE[0],d,0)==BASE[1] not in candidate(True)
            assert g.child(BASE[1],1,3)==y4['T1'] not in envelope()
            rows.append(dict(k=k,t=t,n=n,d=d,counts=counts))
    assert set(witnesses)==envelope() and max_walk==7
    rec=reconciliation()
    assert (rec['S41']['after_registered_including_terminals'],rec['S41']['after_exits'])==(31,33)
    assert (rec['S43']['after_registered_including_terminals'],rec['S43']['after_exits'])==(33,35)
    assert (rec['Y4_IMAGE']['after_registered_including_terminals'],rec['Y4_IMAGE']['after_exits'])==(18,18)
    assert (rec['R5_IMAGE']['after_registered_including_terminals'],rec['R5_IMAGE']['after_exits'])==(8,8)
    return dict(scope='finite exact implementation replay; universal guard and uniform-tail proof separate; no global BH',
                members=len(rows),source_cells=2*len(rows),path_source_cells=9*len(rows),pairs=pairs,accepted=accepted,
                source_path_edges=source_edges,all_child_walk_edges=walk_edges,max_walk=max_walk,image_labels=6,
                source_exit_bound=1,child_tail_bound=6,first_choice_walk_bound=7,all_direct_children_productive=True,
                image_typed_terminals=2,image_classified_nonterminal_stars=0,image_registered_exits=6,
                S43_escape=True,image_escape=True,closed_carrier_proved=False,reconciliation=rec,
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
