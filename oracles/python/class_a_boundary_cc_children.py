"""Independent exact literal-word/Fraction replay of CC=(c,c,0,-2,3).

Scope: a complete four-edge indexed star (eight across reversals)
and a selected three-edge typed-coincidence path on the minus class-A
boundary chamber. Finite replay does not establish the universal claim.
"""
from pathlib import Path
import runpy

Geometry=runpy.run_path(str(Path(__file__).with_name(
    "class_a_boundary_children.py")))["Geometry"]

CC=(1,1,0,-2,3)
YC=(2,1,1,0,-2)
XC=(0,1,1,0,-3)
XY3=(0,2,1,1,-3)
XY2=(0,2,1,1,-2)
Q=(2,0,0,-1,1)
C=(2,2,0,0,0)
BASE={YC,XC,XY3,XY2}


def reverse(w):
    return (w[1],w[0],*(-v for v in w[2:]))


def source(flip):
    if flip not in (0,1):
        raise ValueError("unknown CC orientation")
    return reverse(CC) if flip else CC


def predicted(flip,g,i,j):
    w=source(flip)
    if not (0<=i<len(g.words[w[0]]) and 0<=j<len(g.words[w[1]])):
        raise ValueError("nonexistent CC occurrence")
    a,b=(j,i) if flip else (i,j)
    n=g.n
    return (a==n and b==0) or (a==n+1 and b in (0,1,2))


def image():
    return BASE|{reverse(w) for w in BASE}


def selected_path(flip,g):
    base=[(g.n+1,2,XY2),(g.d+2,0,Q),(1,2,C)]
    return [(j,i,reverse(target)) for i,j,target in base] if flip else base


def verify_selected(flip,g,steps):
    if steps!=selected_path(flip,g):
        raise ValueError("selected CC exit changed")
    current=source(flip)
    for i,j,target in steps:
        if not (g.interior(current) and
                g.child(current,i,j)==target and g.interior(target)):
            raise ValueError("CC indexed path, typing or strict overlap failed")
        current=target
    if current!=C:
        raise ValueError("not equal-letter offset-zero coincidence")


# Exact universal Parikh identities in Z[k,t], not specimen interpolation.
# Polynomials are affine triples (coefficient of k, t, constant).
def add(a,b):
    return tuple(x+y for x,y in zip(a,b))


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def scale(x,a):
    return tuple(x*v for v in a)


def symbolic_exit():
    z=(0,0,0)
    one=(0,0,1)
    two=(0,0,2)
    n=(1,1,3)
    d=(1,2,5)
    A=add(n,d)
    N=sub(n,one)
    # M applied to the full Parikh offset of each successive source.
    # CC=(0,-2,3) -> M=(1,1,n-3)
    Mcc=(one,one,sub(n,(0,0,3)))
    # Top c LAST n+1 prefix (0,1,n), bottom c RUN 2 (0,1,1).
    delta=(z,z,sub(one,n))
    assert tuple(add(a,b) for a,b in zip(Mcc,delta))==(one,one,(0,0,-2))
    # XY2=(1,1,-2) -> M=(1,-1,d+2).
    Mxy2=(one,scale(-1,one),add(d,two))
    # Top x RUN d+2 prefix (1,0,d+1), bottom y FIRST 0.
    delta=(scale(-1,one),z,scale(-1,add(d,one)))
    assert tuple(add(a,b) for a,b in zip(Mxy2,delta))==(z,scale(-1,one),one)
    # Q=(0,-1,1) -> M=(0,0,-1).
    Mq=(z,z,scale(-1,one))
    # Top y RUN 1 prefix (1,0,0), bottom x RUN 2 (1,0,1).
    delta=(z,z,one)
    assert tuple(add(a,b) for a,b in zip(Mq,delta))==(z,z,z)
    # Every occurrence exists: n>=3, 1<=2<=n, 1<=d+2<=A.
    assert sub(n,(0,0,3))==(1,1,0)
    assert sub(A,add(d,two))==sub(n,two)
    return dict(universal_integer_transport=True,
                selected_path_length=3,
                actual_types_and_indices=True,
                strict_geometry="requires inherited exact Perron inequalities",
                finite_replay_not_universal_BH=True)


def probe():
    rows=[];pairs=accepted=path_edges=0;witnesses={}
    for k in range(13):
        for t in range(9):
            g=Geometry(-1,k,t)
            n=g.n
            assert g.interior(CC)
            endpoint=g.child((2,2,1,-1,-1),n,n)
            assert endpoint==(1,1,0,-2,t+3)
            assert (endpoint==CC)==(t==0)
            assert g.interior(endpoint)==(t==0)
            for flip in (0,1):
                w=source(flip)
                actual=set(g.edges(w))
                predicted_set={(i,j,g.child(w,i,j))
                               for i in range(len(g.words[w[0]]))
                               for j in range(len(g.words[w[1]]))
                               if predicted(flip,g,i,j)}
                assert actual==predicted_set and len(actual)==4
                for i,j,target in sorted(actual):
                    assert target in image()
                    witnesses.setdefault(target,dict(k=k,t=t,flip=flip,i=i,j=j))
                    assert g.child(reverse(w),j,i)==reverse(target)
                    assert g.interior(reverse(target))
                path=selected_path(flip,g)
                verify_selected(flip,g,path)
                pairs+=len(g.words[w[0]])*len(g.words[w[1]])
                accepted+=len(actual)
                path_edges+=len(path)
            assert not g.interior(g.child(CC,0,0))
            assert not g.interior(g.child(CC,n+1,n+1))
            rows.append(dict(k=k,t=t,n=n,d=g.d))
    assert set(witnesses)==image() and len(witnesses)==8
    symbolic_exit()
    return dict(scope="finite literal/Fraction replay plus separate Z[k,t] path transport",
                members=len(rows),source_cells=2*len(rows),pairs=pairs,
                accepted=accepted,path_edges=path_edges,image_labels=8,
                children_each=4,selected_depth=3,
                forward_closed=False,all_child_productivity=False,
                universal_BH=False,
                witnesses=[dict(target=list(w),**r)
                           for w,r in sorted(witnesses.items())],
                rows=rows)


if __name__=="__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
