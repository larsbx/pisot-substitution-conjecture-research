"""Independent literal-word/Fraction replay of P9 complete indexed stars."""
from pathlib import Path
import runpy
j9=runpy.run_path(str(Path(__file__).with_name('class_a_boundary_j9_children.py')))
Geometry,reverse,C=j9['Geometry'],j9['reverse'],j9['C']


def source(kind):
    if kind not in (0,1):raise ValueError('unknown P9 orientation')
    return j9['source'](2+kind)


def interface(w,include_new=False):
    old=j9['interface'](w,True)
    if old is not None:return old
    return 'P9' if include_new and w in (source(0),source(1)) else None


def companion(kind):
    if kind not in range(6):raise ValueError('unknown P9 companion')
    base=((0,0,1,3,-5),(2,0,-1,-2,4),(0,2,2,3,-6))
    return reverse(base[kind//2]) if kind%2 else base[kind//2]


def exit_interface(w,include_new=False):
    old=j9['exit_interface'](w,True)
    if old is not None:return old
    if include_new:
        for group,name in enumerate(('W9','B9')):
            if w in (companion(2*group),companion(2*group+1)):return name
    return None


def count(k,t):
    if min(k,t)<0:raise ValueError('negative parameter')
    return 2*(k+t+3)+2+(k>=2)


def predicted(kind,g,i,j):
    w=source(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    if not(0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):raise ValueError('unavailable occurrence')
    a,b=(j,i) if kind else (i,j);k,n,A=g.k,g.n,g.n+g.d
    if a==0:return k<=2 if b==0 else k==0 and b==1
    if a<=A:
        if b==0:return max(1,k-2)<=a<=k
        if b<n:return a-b in (k,k-1)
        return k+n-1<=a<=k+n+(k==0)
    return False


def envelope():
    base=({(0,0,1,3,r) for r in range(-6,-3)}|{(0,2,2,3,-6)}|
          {(2,0,0,3,r) for r in range(-5,-2)}|{(2,2,1,3,r) for r in (-6,-5)}|
          {(2,1,1,3,r) for r in range(-7,-4)})
    out=base|{reverse(w) for w in base}
    assert len(out)==24
    return out


def path(kind,g):return j9['path'](2+kind,g)


def verify_path(w,g,packet,want):j9['verify_path'](w,g,packet,want)


def verify_star(kind,g,edges):
    if len(edges)!=count(g.k,g.t) or len({(i,j) for i,j,_ in edges})!=len(edges):raise ValueError('incomplete/duplicate P9 star')
    for i,j,w in edges:
        if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w and g.interior(w)):raise ValueError('wrong indexed typed target')



def companion_path(kind,g):
    companion(kind)
    if g.eps!=-1:raise ValueError('minus chamber required')
    group,flip=divmod(kind,2)
    if group==0:out=[(g.t+4,0,companion(2))]+companion_path(2,g)
    elif group==1:out=[(0,g.t+4,j9['e7']['b5']['source'](1))]+j9['e7']['b5']['path'](1,g)
    else:
        if g.k!=0:raise ValueError('X9 selected tail is k=0-only')
        out=[(g.n+g.d+1,0,j9['j8']['source'](20))]+j9['j8']['path'](20,g)
    return [(j,i,reverse(w)) for i,j,w in out] if flip else out


def tail(w,g):
    if g.eps!=-1 or w not in envelope():raise ValueError('outside P9 image tail interface')
    for flip in (0,1):
        if w==j9['source'](4+flip):return j9['path'](4+flip,g)
        for kind in (flip,4+flip):
            if w==companion(kind):return companion_path(kind,g)
        for group in (1,2,3,4,5,6,13):
            if w==j9['j8']['source'](2*group+flip):return j9['j8']['path'](2*group+flip,g)
        for group in (2,5):
            if w==j9['r4']['source'](2*group+flip):return j9['r4']['path'](2*group+flip,g)
    raise ValueError('complete P9 image tail dispatch missed a label')


def walk(kind,g,edge):
    i,j,w=edge
    if not(predicted(kind,g,i,j) and g.child(source(kind),i,j)==w):raise ValueError('wrong first P9 packet')
    return [edge]+tail(w,g)


def verify_walk(kind,g,edge,packet):
    if len(packet)>9:raise ValueError('P9 selected first-choice bound exceeded')
    verify_path(source(kind),g,packet,walk(kind,g,edge))


def registry_rows(labels):
    return [dict(label=list(w),before=interface(w),after=interface(w,True),before_exit=exit_interface(w),after_exit=exit_interface(w,True)) for w in sorted(labels)]


def reconciliation():
    rows=registry_rows(j9['e7']['b5']['r3']['candidate'](True))
    return dict(labels=41,before_registered_including_terminal=sum(r['before'] is not None for r in rows),after_registered_including_terminal=sum(r['after'] is not None for r in rows),
                before_exits_including_terminal=sum(r['before_exit'] is not None for r in rows),after_exits_including_terminal=sum(r['after_exit'] is not None for r in rows),
                source_rows=registry_rows({source(i) for i in (0,1)}|{companion(i) for i in range(6)}),rows=rows,image_rows=registry_rows(envelope()),previous_J9_image_rows=registry_rows(j9['envelope']()))


def verify_native_registry(output):
    # Reuse only the established name->integer representation, not any geometry.
    import ast
    code=Path(__file__).with_name('class_a_boundary_j9_children.py').read_text()
    fn=next(n for n in ast.parse(code).body if isinstance(n,ast.FunctionDef) and n.name=='verify_native_registry')
    ids=ast.literal_eval(fn.body[0].value);ids.update(W9=64,B9=65)
    rec=reconciliation()
    for name,key in [('SOURCE','source_rows'),('CANDIDATE','rows'),('IMAGE','image_rows'),('J9_IMAGE','previous_J9_image_rows')]:
        prefix='CLASS_A_P9_'+name+'_REGISTRY ';got={}
        for line in output.splitlines():
            if not line.startswith(prefix):continue
            a=tuple(map(int,line.split()[1:]))
            if len(a)!=9 or a[:5] in got:raise ValueError('bad/duplicate native registry row')
            got[a[:5]]=a[5:]
        want={tuple(r['label']):tuple(ids[r[k]] for k in ('before','after','before_exit','after_exit')) for r in rec[key]}
        if got!=want:raise ValueError('native/oracle registry disagreement')


def probe():
    rows=[];witnesses={};pairs=accepted=path_edges=walk_edges=companion_edges=max_walk=0
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t);counts=[]
            for kind in (0,1):
                w=source(kind);assert g.interior(w)
                actual=set(g.edges(w));chosen={(i,j,g.child(w,i,j)) for i in range(len(g.words[w[0]])) for j in range(len(g.words[w[1]])) if predicted(kind,g,i,j)}
                assert actual==chosen,(k,t,kind,actual^chosen)
                verify_star(kind,g,list(actual));assert len(actual)==count(k,t)
                for edge in sorted(actual):
                    i,j,v=edge
                    assert v in envelope()
                    witnesses.setdefault(v,dict(k=k,t=t,kind=kind,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(v) and g.interior(reverse(v))
                    packet=walk(kind,g,edge);verify_walk(kind,g,edge,packet)
                    walk_edges+=len(packet);max_walk=max(max_walk,len(packet))
                p=path(kind,g);verify_path(w,g,p,p);assert p[0] in actual
                assert len(p)==(7 if k==0 else 6)
                path_edges+=len(p);pairs+=len(g.words[w[0]])*len(g.words[w[1]]);accepted+=len(actual);counts.append(len(actual))
                # Uniform actual J9 ancestry is independent of image-tail claims.
                assert g.child(j9['source'](kind),g.n+k+3 if kind else 0,0 if kind else g.n+k+3)==w
            for kind in range(6):
                if kind>=4 and k!=0:continue
                w=companion(kind);assert g.interior(w)
                p=companion_path(kind,g);verify_path(w,g,p,p);assert len(p)==(4,3,6)[kind//2];companion_edges+=len(p)
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,counts=counts))
    assert set(witnesses)==envelope() and max_walk==9
    rec=reconciliation()
    return dict(scope='finite independent implementation replay; universal guards and selected-path proof separate; no global BH',members=len(rows),source_cells=2*len(rows),pairs=pairs,accepted=accepted,source_path_edges=path_edges,companion_path_edges=companion_edges,all_child_walk_edges=walk_edges,max_selected_walk=max_walk,image_labels=24,
                source_exit_k0=7,source_exit_kpositive=6,all_direct_children_productivity_proved=True,closed_carrier_proved=False,new_companion_stars=False,
                image_registered_stars=sum(interface(w,True) is not None for w in envelope()),image_uniform_exits=sum(exit_interface(w,True) is not None for w in envelope()),image_guarded_tail_labels=4,
                reconciliation=rec,witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__=='__main__':
    import json
    print(json.dumps(probe(),sort_keys=True,indent=2))
