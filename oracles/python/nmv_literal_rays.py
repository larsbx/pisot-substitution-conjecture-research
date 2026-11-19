"""Independent literal-word oracle for the (NM_V) census.

Canonical implementation: kernel/psc/zero_fibre_asymptotes.mojo with the driver
kernel/nmv_census.mojo (docs/c4-unique-partner-exclusion-2026-11-18.md, section
"Scope on the corpus"). This stdlib script shares no code with it and uses a
different method: it expands the substitution words themselves. An interior
member's ray comes from the literal address sigma^k(j) = P j S with
(M^k - I) v = p(P), and a vertex member's ray from iterating its seam letter.
A reported asymptote is confirmed when the two rays share a lattice vertex
beyond which RAY // 3 consecutive tiles agree. This is a one-sided check of each
reported failure: a confirmation is evidence, and a mismatch raises.

Usage:
  python3 oracles/python/nmv_literal_rays.py evidence/nmv-census-2026-11-18/nmv-census.log
"""
import ast
import re
import sys


class OracleFailure(Exception):
    pass


RAY=1500
def subst(s,w): return [c for x in w for c in s[x]]
def power(s,w,k):
    for _ in range(k): w=subst(s,w)
    return w
def par(w,n): return [w[:n].count(i) for i in range(3)]
def interior_ray(s,j,v,right):
    for k in range(1,13):
        img=power(s,[j],k)
        cols=[par(power(s,[a],k),10**9) for a in range(3)]
        tgt=[sum(cols[a][i]*v[a] for a in range(3))-v[i] for i in range(3)]
        idx=[i for i in range(1,len(img)-1) if img[i]==j and par(img,i)==tgt]
        if not idx: continue
        i=idx[-1]
        if right:
            ray=[j]; seg=img[i+1:]
            while len(ray)<RAY: ray+=seg; seg=power(s,seg,k)
        else:
            ray=[]; seg=img[:i]
            while len(ray)<RAY: ray+=seg[::-1]; seg=power(s,seg,k)
        return ray[:RAY]
    raise OracleFailure("no literal interior address up to period 12")
def vertex_ray(s,l,right):
    w=[l]
    while len(w)<RAY: w=subst(s,w)
    for _ in range(6):
        if (w[0] if right else w[-1])==l: break
        w=subst(s,w)
    return w[:RAY] if right else w[::-1][:RAY]
def agree(a,sa,b,sb,right):
    va={};p=list(sa)
    for i,c in enumerate(a):
        if not right: p[c]-=1
        va[tuple(p)]=i
        if right: p[c]+=1
    q=list(sb)
    for i,c in enumerate(b):
        if not right: q[c]-=1
        if tuple(q) in va:
            ia=va[tuple(q)]
            ja=ia if right else ia+1; jb=i if right else i+1
            L=RAY//3
            if ja+L<=len(a) and jb+L<=len(b) and a[ja:ja+L]==b[jb:jb+L]: return True
        if right: q[c]+=1
    return False


def confirm_log(path):
    """Confirm every failing pair of a census log; return the number confirmed."""
    confirmed = 0
    for line in open(path):
        if not line.startswith("fail"):
            continue
        s = ast.literal_eval(re.search(r"sigma (\[\[.*?\]\])", line).group(1))
        for side, vl, vr, x in re.findall(r"\[(L|R) (\d)\.(\d) ~. ([^\]]+)\]", line):
            right = side == "R"
            vl, vr = int(vl), int(vr)
            vray = vertex_ray(s, vr if right else vl, right)
            m = re.match(r"\((\d);(-?\d+),(-?\d+),(-?\d+)\)", x)
            if m:
                j, a, b, c = map(int, m.groups())
                ok = agree(vray, [0, 0, 0], interior_ray(s, j, [a, b, c], right), [-a, -b, -c], right)
            else:
                xl, xr = map(int, x.split("."))
                ok = agree(vray, [0, 0, 0], vertex_ray(s, xr if right else xl, right), [0, 0, 0], right)
            if not ok:
                raise OracleFailure(f"no literal agreement: {line.strip()[:60]} {side} {x}")
            confirmed += 1
    return confirmed


if __name__ == "__main__":
    print("confirmed", confirm_log(sys.argv[1]))
