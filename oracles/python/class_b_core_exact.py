"""Independent exact class-B core closure; Fraction intervals, integral children.

This oracle does not call the native graph engine or the floating probes.
It reconstructs segment pairs, isolates the cubic root using rational
bisection, and bounds every quadratic by interval Horner arithmetic. An
unresolved sign or cap refuses. Inputs/outputs are finite, never a g-uniform
certificate. Usage: python ... NATIVE.labels BRANCH GAP Q
"""
from collections import deque
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from class_b_ray_certificate import Ray, ev, roots_in, prem
from class_b_label_rays import read


class ExactMember:
    def __init__(self, branch, gap, q):
        if branch not in ('plus', 'minus') or not 1 <= gap <= 32 or not 1 <= q <= 320:
            raise ValueError('bounded exact core domain')
        self.eps = 1 if branch == 'plus' else -1
        self.g, self.q = gap, q
        self.p = 3*q+6+6*self.eps-gap
        if not (self.p > 2*q+(13 if self.eps == 1 else 7) and
                2*self.p > 5*q+(10 if self.eps == 1 else -5)):
            raise ValueError('outside open top layer')
        ray = Ray(self.eps, gap, q % gap)
        ray.derive()
        self.lengths = ray.lengths
        self.chi = list(ray.a_poly)
        self.chi[1] -= q
        self.chi[2] -= q
        lo, hi = F(q+3+self.eps), F(q+7+self.eps)
        if ev(self.chi, lo) >= 0 or ev(self.chi, hi) <= 0 or roots_in(self.chi, lo, hi) != 1:
            raise ValueError('root not uniquely bracketed')
        for _ in range(96):
            mid = (lo+hi)/2
            if ev(self.chi, mid) < 0: lo = mid
            else: hi = mid
        self.bracket = lo, hi
        self.segments = []
        for t, run in enumerate((self.p, q, q+self.eps)):
            px, pc = int(t == 0), int(t != 0)
            self.segments.append(((0 if t == 0 else 1, 0, 0, 0, 0),
                                  (2, px, pc, 0, run-1), (0, px, pc, run, run)))

    @lru_cache(maxsize=None)
    def sign(self, coeff):
        coeff = tuple(prem(coeff, self.chi))
        if not coeff: return 0
        lo, hi = self.bracket
        for _ in range(32):
            a, b = F(0), F(0)
            for c in reversed(coeff):
                products = (a*lo, a*hi, b*lo, b*hi)
                a, b = min(products)+c, max(products)+c
            if a > 0: return 1
            if b < 0: return -1
            # Refine only if this particular polynomial is still unresolved.
            mid = (lo+hi)/2
            if ev(self.chi, mid) < 0: lo = mid
            else: hi = mid
        raise ValueError('exact Perron sign budget exhausted')

    def disp(self, w):
        return tuple(sum(self.lengths[j][i]*w[j] for j in range(3)) for i in range(3))

    def strict(self, state):
        t,b,w = state
        T = self.disp(w)
        return (self.sign(tuple(self.lengths[t][i]-T[i] for i in range(3))) > 0 and
                self.sign(tuple(T[i]+self.lengths[b][i] for i in range(3))) > 0)

    def children(self, state):
        t,b,(k,c,y) = state
        if (k,c,y) == (0,0,0): return ()
        mw = (2*k+c+y, c+y, self.p*k+self.q*c+(self.q+self.eps)*y)
        out = set()
        for ct,px,pc,lo,hi in self.segments[t]:
            for cb,bx,bc,blo,bhi in self.segments[b]:
                base = (mw[0]+bx-px, mw[1]+bc-pc, mw[2])
                T = self.disp(base)
                # Monotonic integer search, no floating estimate or epsilon.
                lower, upper = blo-hi, bhi-lo
                def gt_bottom(dy):
                    return self.sign(tuple(T[i]+self.lengths[cb][i]+dy*self.lengths[2][i] for i in range(3))) > 0
                a,z = lower,upper+1
                while a<z:
                    m=(a+z)//2
                    if gt_bottom(m): z=m
                    else: a=m+1
                for dy in range(a,upper+1):
                    child=(ct,cb,(base[0],base[1],base[2]+dy))
                    if self.sign(tuple(self.lengths[ct][i]-T[i]-dy*self.lengths[2][i] for i in range(3))) <= 0: break
                    out.add(child)
        return tuple(sorted(out))

    def core(self):
        return {(t,b,(k,d+3*k,u-6*k-d)) for u in range(-3,4) for d in range(-6,7)
                for k in range(-2,3) for t in range(3) for b in range(3)
                if self.strict((t,b,(k,d+3*k,u-6*k-d)))}

    def build(self, cap=20000):
        adj = {s: None for s in sorted(self.core())}
        todo = deque(adj)
        while todo:
            s = todo.popleft()
            adj[s] = self.children(s)
            for c in adj[s]:
                if c not in adj:
                    if len(adj) >= cap: raise ValueError('core closure cap: no verdict')
                    adj[c] = None
                    todo.append(c)
        return adj


def depths(adj):
    reverse = {}
    for s,cs in adj.items():
        for c in cs:
            if c not in adj: raise ValueError('escaping child')
            reverse.setdefault(c,[]).append(s)
    depth = {s:0 for s in adj if s[2] == (0,0,0)}
    todo = deque(depth)
    while todo:
        c=todo.popleft()
        for s in reverse.get(c,()):
            if s not in depth:
                depth[s]=depth[c]+1
                todo.append(s)
    if len(depth)!=len(adj): raise ValueError('state without target descendant')
    return depth


def check(path, branch, gap, q):
    member = ExactMember(branch,gap,q)
    adj = member.build()
    depth = depths(adj)
    rq, rows = read(path)
    expected={(t,b,(k,c,y)):z for t,b,k,c,y,z in rows}
    if rq!=q or expected!=depth: raise ValueError('native/oracle labels or depths disagree')
    return dict(branch=branch,g=gap,q=q,states=len(adj),core=len(member.core()),max_depth=max(depth.values()))



def check_file(path):
    import re
    m=re.fullmatch(r'(plus|minus)-g(\d+)-q(\d+)\.labels',Path(path).name)
    if m is None:raise ValueError('malformed native core export name')
    return check(path,m[1],int(m[2]),int(m[3]))


if __name__=='__main__':
    import json
    if len(sys.argv)==3 and sys.argv[1]=='--packet':
        from concurrent.futures import ProcessPoolExecutor
        paths=sorted(Path(sys.argv[2]).glob('*.labels'))
        if len(paths)!=150:raise ValueError('expected 150 native core exports')
        with ProcessPoolExecutor(max_workers=4) as pool:
            for result in pool.map(check_file,paths):print(json.dumps(result,sort_keys=True),flush=True)
        print('CLASS_B_EXACT_CORE_AGREEMENT members 150')
    else:
        print(json.dumps(check(sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4])),sort_keys=True))
