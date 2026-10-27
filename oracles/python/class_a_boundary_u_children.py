"""Independent finite literal-prefix/Perron-field replay; not a universal proof."""
from pathlib import Path
import runpy

Geometry = runpy.run_path(str(Path(__file__).with_name("class_a_boundary_children.py")))["Geometry"]
U = (0, 2, 1, 2, -3)
T1 = (2, 2, -1, 1, 1)


def reverse(label):
    return (label[1], label[0], *(-x for x in label[2:]))


def predicted(g, i, j):
    n, d = g.n, g.d
    A, N = n+d, n-1
    if not (0 <= i <= A+1 and 0 <= j <= N+1):
        raise ValueError("nonexistent occurrence")
    if i == 0:
        return False
    if i == A+1:
        return (g.k+g.t <= 1) if j == 0 else (max(1,n-4) <= j <= N)
    if j == 0:
        return d+2 <= i <= d+5
    return j <= N and i-j in (d+4,d+5)


def envelope():
    return {(2,0,0,-1,y) for y in range(-1,3)} | {
        (2,2,1,-1,y) for y in (-2,-1)} | {
        (0,0,0,-1,y) for y in (-1,0)} | {
        (0,2,1,-1,y) for y in range(-2,2)}


def probe():
    rows, witnesses, cycles = [], {}, 0
    v_pairs = 0
    for k in range(13):
        for t in range(9):
            g = Geometry(-1,k,t)
            assert g.interior(U)
            actual = set(g.edges(U))
            selected = {(i,j,g.child(U,i,j))
                        for i in range(len(g.words[0]))
                        for j in range(len(g.words[2])) if predicted(g,i,j)}
            assert selected == actual
            assert len(actual) == 2*g.n-1
            for i,j,target in sorted(actual):
                assert target in envelope()
                assert g.child(reverse(U),j,i) == reverse(target)
                assert g.interior(reverse(target))
                witnesses.setdefault(target,dict(k=k,t=t,i=i,j=j))
            assert g.child((0,1,0,0,0),1,2) == T1
            assert g.child(T1,0,t+1) == U
            # A genuine four-cycle, with actual oriented occurrences.
            if g.n >= 5:
                path = [(T1,0,t+1,U),(U,g.d+5,1,reverse(T1)),
                        (reverse(T1),t+1,0,reverse(U)),
                        (reverse(U),1,g.d+5,T1)]
                for source,i,j,target in path:
                    assert g.interior(source) and g.interior(target)
                    assert g.child(source,i,j) == target
                cycles += 1
            V, W = (2,0,0,-1,2), (1,0,0,1,-1)
            assert g.child(U,g.d+2,0) == V and g.interior(V)
            assert set(g.edges(V)) == {(g.n,0,W)}
            v_pairs += len(g.words[2])*len(g.words[0])
            # Legal words do not suffice: the first/first pair is disjoint.
            assert not g.interior(g.child(U,0,0))
            assert not g.interior(g.child(U,1,1))
            assert not g.interior(g.child(U,g.n+g.d+1,g.n))
            rows.append(dict(k=k,t=t,n=g.n,d=g.d,
                             pairs=len(g.words[0])*len(g.words[2]),accepted=len(actual)))
    assert set(witnesses) == envelope()
    return dict(scope="finite independent replay; U outgoing image only; no closure or BH",
                members=len(rows),pairs=sum(r["pairs"] for r in rows),
                accepted=sum(r["accepted"] for r in rows),four_cycle_members=cycles,
                V_pairs=v_pairs,V_accepted=len(rows),V_unique_child=[1,0,0,1,-1],
                image_labels=len(witnesses),
                witnesses=[dict(target=list(w),**v) for w,v in sorted(witnesses.items())],rows=rows)


if __name__ == "__main__":
    import json
    print(json.dumps(probe(),indent=2,sort_keys=True))
