#!/usr/bin/env python3
"""Independent exact finite class-C swap-seed graph oracle. No floats or dependencies.

The quantified PIP theorem is in docs/class-c-residual-domain-2026-10-29.md.
The finite graph results alone do NOT prove any uniform BH assertion.
"""
from fractions import Fraction
from collections import deque, defaultdict
from functools import lru_cache
import argparse, hashlib, json
from pathlib import Path

ZERO = (0, 0, 0)
def add(a, b): return tuple(x+y for x,y in zip(a,b))
def sub(a, b): return tuple(x-y for x,y in zip(a,b))

def pip_claim(d, eps, n):
    if d < 1 or eps not in (-1,1) or n-d+eps < 1:
        raise ValueError("outside the strictly positive-run normal form")
    return {
        "threshold": 2*d-3*eps-2,
        "pip": n >= 2*d-3*eps-2,
        "chi_at_minus_one": 2*(2*d-3*eps-n-3),
        "chi_at_minus_two": 2*(5*d-6*eps-3*n-12),
        "chi_at_one": -2*d, "chi_at_two": -2*(d+n),
    }

class ExactClassC:
    def __init__(self, d, eps, n):
        if not pip_claim(d, eps, n)["pip"]:
            raise ValueError("oracle requires proved PIP region; root isolation not justified")
        self.d, self.eps, self.n = d, eps, n
        self.p, self.q, self.r = n+d, n, n-d+eps
        self.A = n-d+eps+3
        self.B = n-3*d+3*eps+2
        self.lo = Fraction(2)
        self.hi = Fraction(2*(self.A+abs(self.B)+3))
        assert self.chi(self.lo) < 0 < self.chi(self.hi)
        # Integer vectors are coefficients in the basis 1,beta,beta^2.
        # These tile lengths are (beta-2)(beta-1) times the left eigenvector.
        p,q = self.p,self.q
        self.lengths = ((-p,p,0), (p-2*q,q,0), (2,-3,1))
        self.words = (
            (0,)+(2,)*p+(0,),
            (1,)+(2,)*q+(0,),
            (1,)+(2,)*self.r+(1,),
        )
        self.prefix = []
        for i, word in enumerate(self.words):
            cursor = ZERO
            pos = []
            for letter in word:
                pos.append(cursor)
                cursor = add(cursor,self.lengths[letter])
            if cursor != self.beta(self.lengths[i]):
                raise ArithmeticError("substitution scaling failure")
            self.prefix.append(pos)
        self.refinements = 0
        self.sign_queries = 0

    def chi(self,x): return ((x-self.A)*x+self.B)*x-2*self.eps

    def beta(self,a):
        a0,a1,a2=a
        # beta^3 = A*beta^2 - B*beta + 2*eps
        return (2*self.eps*a2,a0-self.B*a2,a1+self.A*a2)

    def refine(self):
        mid = (self.lo+self.hi)/2
        value = self.chi(mid)
        if value < 0: self.lo=mid
        elif value > 0: self.hi=mid
        else: raise ArithmeticError("rational root in an irreducible PIP cubic")
        self.refinements += 1

    @lru_cache(maxsize=None)
    def sign(self,a):
        if a==ZERO: return 0
        self.sign_queries += 1
        for _ in range(2048):
            lo,hi=self.lo,self.hi
            low=a[0]+sum(c*(lo**j if c>0 else hi**j) for j,c in enumerate(a[1:],1))
            high=a[0]+sum(c*(hi**j if c>0 else lo**j) for j,c in enumerate(a[1:],1))
            if low>0: return 1
            if high<0: return -1
            self.refine()
        raise ArithmeticError("exact sign not isolated")

    def overlaps(self,st):
        a,b,w=st
        return self.sign(add(w,self.lengths[b]))>0 and self.sign(sub(w,self.lengths[a]))<0

    def seeds(self):
        out=[]
        for a in range(3):
            for b in range(a+1,3):
                tops=(a,b); bottoms=(b,a)
                topstarts=(ZERO,self.lengths[a])
                bottomstarts=(ZERO,self.lengths[b])
                for i in range(2):
                    for j in range(2):
                        st=(tops[i],bottoms[j],sub(bottomstarts[j],topstarts[i]))
                        if self.overlaps(st): out.append(st)
        return out

    def children(self,st):
        top,bottom,w=st
        w=self.beta(w)
        # Intentionally O(|sigma(top)|*|sigma(bottom)|): no shared Mojo
        # sliding-window optimizer or parametric symbolic interval logic.
        for i,a in enumerate(self.words[top]):
            start_a=self.prefix[top][i]
            for j,b in enumerate(self.words[bottom]):
                shift=sub(add(w,self.prefix[bottom][j]),start_a)
                child=(a,b,shift)
                if self.overlaps(child):
                    yield child

    def graph(self,cap=20000):
        todo=deque(self.seeds())
        seen={}
        states=[]
        edges=[]
        while todo:
            st=todo.popleft()
            if st in seen: continue
            if len(states)>=cap:
                raise ArithmeticError("20,000-vertex cap reached")
            seen[st]=len(states)
            states.append(st)
            children=set(self.children(st))
            edges.append(children)
            todo.extend(k for k in children if k not in seen)
        back={st:[] for st in states}
        for st,children in zip(states,edges):
            for ch in children:
                back[ch].append(st)
        zeros={st for st in states if st[2]==ZERO}
        good=set(zeros)
        queue=deque(zeros)
        while queue:
            for parent in back[queue.popleft()]:
                if parent not in good:
                    good.add(parent)
                    queue.append(parent)
        lines=self.typed_rows(states)
        return {
            "d":self.d,"eps":self.eps,"n":self.n,
            "vertices":len(states),"zero":len(zeros),
            "all_hit":len(good)==len(states),"unhit":len(states)-len(good),
            "typed_rows":len(lines),
            "label_digest":hashlib.sha256("".join(lines).encode()).hexdigest(),
            "sign_queries":self.sign_queries,
            "bracket_refinements":self.refinements,
            "rows_text":"".join(lines),
        }

    def typed_rows(self,states):
        groups=defaultdict(list)
        for top,bottom,(a,b,c) in states:
            # Invert the integer tile-length basis, independently:
            # shift = wx*Lx + wc*Lc + wy*Ly.
            if (a+b+c)%self.d: raise ArithmeticError("noninteger wc")
            wc=(a+b+c)//self.d
            if (b+3*c-self.n*wc)%self.p: raise ArithmeticError("noninteger wx")
            wx=(b+3*c-self.n*wc)//self.p
            groups[(top,bottom,wx+wc+c,c)].append(wx)
        out=[]
        for key,values in sorted(groups.items()):
            values.sort()
            start=last=values[0]
            for x in values[1:]:
                if x==last: raise ArithmeticError("duplicate label")
                if x>last+1:
                    out.append("R "+" ".join(map(str,(*key,start,last)))+"\n")
                    start=x
                last=x
            out.append("R "+" ".join(map(str,(*key,start,last)))+"\n")
        return out

def verify():
    expected={(1,-2):204,(1,-1):198,(1,0):196,
              (-1,-2):222,(-1,-1):216,(-1,0):214}
    row_counts={(1,-1):79,(1,0):77,(-1,-1):83,(-1,0):81}
    # These are finite regression checks of a quantified, separately proved
    # identity; the loops alone are NOT the theorem.
    for d in range(6,65):
        for eps in (-1,1):
            threshold=2*d-3*eps-2
            for n in (threshold-2,threshold-1,threshold,threshold+1):
                if n-d+eps<1: continue
                claim=pip_claim(d,eps,n)
                assert claim["pip"]==(n>=threshold)
                assert (claim["chi_at_minus_one"]<0)==(n>=threshold)
    for eps in (1,-1):
        for off in (-2,-1,0):
            baseline=None
            for d in (6,7,8):
                n=4*d+(4 if eps==-1 else 0)+off
                g=ExactClassC(d,eps,n).graph()
                assert g["all_hit"] and g["vertices"]==expected[(eps,off)]
                if (eps,off) in row_counts:
                    assert g["typed_rows"]==row_counts[(eps,off)]
                if baseline is None:baseline=g["rows_text"]
                else:assert baseline==g["rows_text"]
                del g["rows_text"]
                print(json.dumps(g,sort_keys=True))
        # Independent finite graph, byte-for-byte against BOTH previously
        # committed reference packets; this compares all labels, not counts.
        sign = "plus" if eps == 1 else "minus"
        evidence = Path(__file__).resolve().parents[1]
        for packet in (
            evidence / "class-c-tail-theorem-2026-10-28" / ("theorem-"+sign+".log"),
            evidence / "class-c-gap-profile-2026-10-28" / ("frozen-tail-"+sign+".txt"),
        ):
            actual = "".join(line+"\n" for line in packet.read_text().splitlines() if line.startswith("R "))
            assert actual == baseline, "independent full typed rows differ from "+str(packet)
        low=2*6-3*eps-2
        g=ExactClassC(6,eps,low).graph()
        assert g["all_hit"] and g["vertices"]==(2432 if eps==1 else 1283)
        del g["rows_text"]
        print(json.dumps(g,sort_keys=True))
    print("PASS: independent finite graphs, offset rows, and integer border controls")

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("cases",nargs="*",help="d,eps,n")
    ap.add_argument("--verify",action="store_true")
    args=ap.parse_args()
    if args.verify:
        verify()
    else:
        for spec in args.cases or ("6,1,24","6,-1,28","8,1,31","8,-1,35"):
            d,eps,n=map(int,spec.split(","))
            g=ExactClassC(d,eps,n).graph()
            del g["rows_text"]
            print(json.dumps({"pip":pip_claim(d,eps,n),"graph":g},sort_keys=True))

if __name__=="__main__": main()
