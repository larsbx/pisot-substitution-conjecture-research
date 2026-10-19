"""Finite guarded cycle superset for minus positive-b class D.

This is a conditional theorem layer: assuming a genuine cyclic overlap has
s(w)=wx+wc+wy in {-1,0,1}, the predecessor identities force
m=wx+wc in [-3,3] and tau=wx-wc in [-10,10].

We enumerate every typed integral state in that finite box.  A segment-pair
edge is retained unless exact Farkas arithmetic proves that its required
occurrence-index difference is impossible for every a>=2,b>=1.  Thus the graph
is an overapproximation of every actual cycle satisfying the sum premise.

Its recurrent part is classified against the sealed 145-label carrier.
"""
from std.collections import Dict
from finite_graph.scc import has_cycle, sccs
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.farkas_lp import lp_infeasible
from psc.class_d_positive_b_geometry import _margins20


struct CycleState(Copyable, Movable):
    var top: Int
    var bottom: Int
    var x: Int
    var c: Int
    var y: Int

    def __init__(out self, top: Int, bottom: Int, x: Int, c: Int, y: Int):
        self.top = top
        self.bottom = bottom
        self.x = x
        self.c = c
        self.y = y

    def key(self) -> String:
        return String(self.top)+":"+String(self.bottom)+":"+String(self.x)+","+String(self.c)+","+String(self.y)

    def is_zero_offset(self) -> Bool:
        return self.x == 0 and self.c == 0 and self.y == 0


def _first(letter: Int) -> Int:
    return 0 if letter == 0 else 1


def _last(letter: Int) -> Int:
    return 0 if letter == 1 else 1


def _run(letter: Int) -> List[Int]:
    # R = A*a + C + b.
    if letter == 0:
        return [3,5,1]
    if letter == 1:
        return [3,6,1]
    return [2,4,1]


def _segment(letter: Int, kind: Int) raises -> List[List[Int]]:
    """[child], prefix-x/c, index-low/high as affine [A,C,B]."""
    if kind < 0 or kind > 2:
        raise Error("segment kind outside first/run/last")
    var out = List[List[Int]]()
    if kind == 0:
        out.append([_first(letter)])
        out.append([0,0])
        out.append([0,0,0])
        out.append([0,0,0])
        return out^
    var px = 1 if _first(letter) == 0 else 0
    var pc = 1 if _first(letter) == 1 else 0
    var r = _run(letter)
    if kind == 1:
        out.append([2])
        out.append([px,pc])
        out.append([0,1,0])
        out.append(r.copy())
        return out^
    out.append([_last(letter)])
    out.append([px,pc])
    out.append([r[0],r[1]+1,r[2]])
    out.append([r[0],r[1]+1,r[2]])
    return out^


def _sub3(a: List[Int], b: List[Int]) -> List[Int]:
    return [a[0]-b[0],a[1]-b[1],a[2]-b[2]]


def _shift_corner(f: List[Int]) -> List[Int]:
    # f=A*a+C+B*b; a=2+u,b=1+v -> (C+2A+B)+A*u+B*v.
    return [f[1]+2*f[0]+f[2],f[0],f[2]]


def edge_forms(
    state: CycleState, st: List[List[Int]], sb: List[List[Int]], sp: Int
) raises -> List[List[Int]]:
    var s = state.x+state.c+state.y
    var A = 3*state.x+3*state.c+2*state.y
    var C = 7*state.x+8*state.c+6*state.y
    # Required j-i = sp - (A*a + s*b + C).
    var req: List[Int] = [-A,sp-C,-s]
    var lower = _sub3(sb[2],st[3])
    var upper = _sub3(sb[3],st[2])
    var forms = List[List[Int]]()
    forms.append(_shift_corner(_sub3(req,lower)))
    forms.append(_shift_corner(_sub3(upper,req)))
    return forms^


def _edge_possible(
    state: CycleState, st: List[List[Int]], sb: List[List[Int]], sp: Int
) raises -> Bool:
    var forms = edge_forms(state,st,sb,sp)
    # If exact Farkas arithmetic cannot refute the region, retain the edge.
    # This is deliberately an overapproximation.
    return not lp_infeasible(forms,2)


def _boundary_only(v: CycleState) -> Bool:
    var row: List[Int] = [v.top,v.bottom,v.x,v.c,v.y]
    var m = _margins20(row)
    for k in range(2):
        if m[k][0] == 0 and m[k][1] == 0 and m[k][2] == 0:
            return True
    return False


def _exceptional(v: CycleState) -> Bool:
    var k = v.key()
    return (
        k == "2:1:-2,4,-3" or
        k == "1:2:2,-4,3" or
        k == "2:1:3,-6,4" or
        k == "1:2:-3,6,-4"
    )


def verify_minus_cycle_superset() raises -> List[Int]:
    var states = List[CycleState]()
    var index = Dict[String,Int]()

    for top in range(3):
        for bottom in range(3):
            for s in range(-1,2):
                for m in range(-3,4):
                    for tau in range(-10,11):
                        if (m+tau) % 2 != 0:
                            continue
                        var x = (m+tau)//2
                        var c = m-x
                        var y = s-m
                        var v = CycleState(top,bottom,x,c,y)
                        index[v.key()] = len(states)
                        states.append(v^)

    if len(states) != 1971:
        raise Error("minus cycle-superset state count changed")

    var adj = List[List[Int]]()
    for _ in range(len(states)):
        adj.append(List[Int]())

    for i in range(len(states)):
        var v = states[i].copy()
        var s = v.x+v.c+v.y
        var m = v.x+v.c
        for kt in range(3):
            var st = _segment(v.top,kt)
            for kb in range(3):
                var sb = _segment(v.bottom,kb)
                var dx = sb[1][0]-st[1][0]
                var dc = sb[1][1]-st[1][1]
                var mp = 2*s+dx+dc
                var taup = 2*m-2*s+dx-dc
                if mp < -3 or mp > 3 or taup < -10 or taup > 10:
                    continue
                if (mp+taup) % 2 != 0:
                    continue
                var xp = (mp+taup)//2
                var cp = mp-xp
                for sp in range(-1,2):
                    if not _edge_possible(v,st,sb,sp):
                        continue
                    var child = CycleState(st[0][0],sb[0][0],xp,cp,sp-mp)
                    var key = child.key()
                    if key in index:
                        adj[i].append(index[key])

    var cover = Dict[String,Int]()
    var rows = minus_spine_rows()
    for i in range(len(rows)):
        var v = CycleState(rows[i][0],rows[i][1],rows[i][2],rows[i][3],rows[i][4])
        cover[v.key()] = i

    var comps = sccs(adj)
    var recurrent = 0
    var carrier = 0
    var zero = 0
    var zero_coincidence = 0
    var zero_noncoincidence = 0
    var boundary = 0
    var exceptional = 0
    for comp in comps:
        if not has_cycle(adj,comp):
            continue
        for at in comp:
            recurrent += 1
            var v = states[at].copy()
            if v.key() in cover:
                carrier += 1
            elif v.is_zero_offset():
                # Explicit known BH targets, not a blanket coincidence filter.
                if v.top == v.bottom:
                    if v.key() != "0:0:0,0,0":
                        raise Error("unexpected noncarrier terminal coincidence")
                    zero_coincidence += 1
                else:
                    if v.key() != "1:0:0,0,0":
                        raise Error("unexpected noncarrier zero-offset noncoincidence")
                    zero_noncoincidence += 1
                print("SUPERSET_ZERO_TARGET",v.key(),"coincidence=",v.top == v.bottom)
                zero += 1
            elif _boundary_only(v):
                boundary += 1
            elif _exceptional(v):
                exceptional += 1
            else:
                raise Error("unclassified recurrent cycle-superset state: "+v.key())

    if zero_coincidence != 1 or zero_noncoincidence != 1:
        raise Error("zero-target coincidence partition changed")
    if recurrent != 145 or carrier != 131 or zero != 2 or boundary != 8 or exceptional != 4:
        raise Error("minus cycle-superset recurrent classification changed")

    return [len(states),recurrent,carrier,zero,boundary,exceptional]
