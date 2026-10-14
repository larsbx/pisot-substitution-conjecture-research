"""Exact symbolic child closure on class D's minus b=0 line, a>=4.

The proof/sign contracts are in the family note section 4i. Every child is
accounted for by nine segment pairs, an exhaustive third-coordinate bound,
and uniform quadratic/affine signs. No fitted graph or floating predicate.
Resource guards bound all intermediate integers below 150 million; an
undecided sign or exhausted guard raises instead of returning a certificate.
"""
from std.collections import Dict
from psc.class_d_boundary import boundary_member
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables, first_left_aligned_depths
from psc.vertex_coincidence import length_matrix, offset_vector


def offset_sign(x: Int, y: Int, z: Int, floor: Int) raises -> Int:
    if floor < 0 or floor > 64 or x < -1000 or x > 1000 or y < -1000 or y > 1000 or z < -1000 or z > 1000:
        raise Error("symbolic sign arithmetic budget exceeded")
    var t = 2*floor+6
    var c2 = 3*x+3*y+2*z
    var c1 = -2*x+2*z
    var c0 = -4*x-2*y
    var d0 = c0+c1*t+c2*t*t
    var d1 = c1+2*c2*t
    if d0 == 0 and d1 == 0 and c2 == 0:
        return 0
    if d0 >= 0 and d1 >= 0 and c2 >= 0:
        return 1
    if d0 <= 0 and d1 <= 0 and c2 <= 0:
        return -1
    raise Error("UNDECIDED quadratic sign on beta>2*floor+6")


def affine_nonnegative(slope: Int, base: Int, floor: Int) raises -> Bool:
    if floor < 0 or floor > 64 or slope < -10000 or slope > 10000 or base < -10000 or base > 10000:
        raise Error("affine sign arithmetic budget exceeded")
    var v = slope*floor+base
    if slope >= 0 and v >= 0:
        return True
    if slope <= 0 and v < 0:
        return False
    raise Error("UNDECIDED affine occurrence inequality")


def label_key(v: List[Int]) raises -> Int:
    if len(v) != 5 or v[0] < 0 or v[0] > 2 or v[1] < 0 or v[1] > 2:
        raise Error("invalid symbolic vertex label")
    var key = v[0]*3+v[1]
    for i in range(2,5):
        if v[i] < -100 or v[i] > 100:
            raise Error("symbolic coordinate budget exceeded")
        key = key*201+(v[i]+100)
    return key


def real_label(v: List[Int], floor: Int) raises -> Bool:
    _ = label_key(v)
    var lo = List[Int]([v[2],v[3],v[4]])
    var hi = List[Int]([-v[2],-v[3],-v[4]])
    lo[v[1]] += 1
    hi[v[0]] += 1
    return offset_sign(lo[0],lo[1],lo[2],floor) > 0 and offset_sign(hi[0],hi[1],hi[2],floor) > 0


def run_slope(letter: Int) -> Int:
    return 2 if letter == 2 else 3


def run_base(letter: Int) -> Int:
    return 4 if letter == 2 else 5+letter


def segment(letter: Int, part: Int) -> List[Int]:
    # [child letter, prefix x, prefix c, prefix y slope, prefix y base].
    var first = 0 if letter == 0 else 1
    var last = 0 if letter == 1 else 1
    if part == 0:
        return [first,0,0,0,0]
    return [2 if part == 1 else last, 1 if first == 0 else 0, 1 if first == 1 else 0, run_slope(letter) if part == 2 else 0, run_base(letter) if part == 2 else 0]


def symbolic_children(v: List[Int], floor: Int) raises -> List[List[Int]]:
    _ = label_key(v)
    var out = List[List[Int]]()
    if v[0] == v[1] and v[2] == 0 and v[3] == 0 and v[4] == 0:
        return out^
    var seen = Dict[Int, Int]()
    var x = v[2]
    var y = v[3]
    var z = v[4]
    for top_part in range(3):
        var top = segment(v[0],top_part)
        for bottom_part in range(3):
            var bottom = segment(v[1],bottom_part)
            var u = x+y+bottom[1]-top[1]
            var w = x+y+2*z+bottom[2]-top[2]
            var slope = 3*x+3*y+2*z+bottom[3]-top[3]
            var base = 5*x+6*y+4*z+bottom[4]-top[4]
            var lo_slope = -run_slope(v[0]) if top_part == 1 else 0
            var lo_base = 1-run_base(v[0]) if top_part == 1 else 0
            var hi_slope = run_slope(v[1]) if bottom_part == 1 else 0
            var hi_base = run_base(v[1])-1 if bottom_part == 1 else 0
            var bound = 2+2*(abs(u)+abs(w))
            if bound > 100:
                raise Error("symbolic child-coordinate budget exceeded")
            for c in range(-bound,bound+1):
                var child = List[Int]([top[0],bottom[0],u,w,c])
                if not real_label(child,floor):
                    continue
                # m=c-(slope*a+base); all integer differences in [lo,hi]
                # are realized by actual pairs of run positions.
                if not affine_nonnegative(-slope-lo_slope,c-base-lo_base,floor):
                    continue
                if not affine_nonnegative(hi_slope+slope,hi_base-c+base,floor):
                    continue
                var key = label_key(child)
                if key not in seen:
                    seen[key] = 1
                    out.append(child^)
    return out^


struct BoundaryTemplate(Copyable, Movable):
    var floor: Int
    var vertices: List[List[Int]]
    var adj: List[List[Int]]
    var index: Dict[Int, Int]
    var cap: Int

    def __init__(out self, floor: Int, cap: Int):
        self.floor = floor
        self.cap = cap
        self.vertices = List[List[Int]]()
        self.adj = List[List[Int]]()
        self.index = Dict[Int, Int]()

    def intern(mut self, v: List[Int]) raises -> Int:
        var key = label_key(v)
        if key in self.index:
            return self.index[key]
        if len(self.vertices) >= self.cap:
            raise Error("STATE_BUDGET_EXHAUSTED: no symbolic verdict")
        var i = len(self.vertices)
        self.index[key] = i
        self.vertices.append(v.copy())
        self.adj.append(List[Int]())
        return i

    def edge_count(self) -> Int:
        var n = 0
        for i in range(len(self.adj)):
            n += len(self.adj[i])
        return n


def boundary_template(floor: Int = 4, cap: Int = 20000) raises -> BoundaryTemplate:
    if floor < 0 or floor > 64 or cap < 1 or cap > 20000:
        raise Error("symbolic closure budget outside declared range")
    var g = BoundaryTemplate(floor,cap)
    for a in range(3):
        for b in range(a+1,3):
            for top_pos in range(2):
                for bottom_pos in range(2):
                    var v = List[Int]([a if top_pos == 0 else b,b if bottom_pos == 0 else a,0,0,0])
                    if top_pos == 1:
                        v[2+a] -= 1
                    if bottom_pos == 1:
                        v[2+b] += 1
                    if real_label(v,floor):
                        _ = g.intern(v)
    var head = 0
    while head < len(g.vertices):
        var children = symbolic_children(g.vertices[head],floor)
        var edges = List[Int]()
        for child in children:
            edges.append(g.intern(child))
        g.adj[head] = edges^
        head += 1
    return g^


def template_depths(g: BoundaryTemplate) raises -> List[Int]:
    # Reverse BFS on the complete symbolic adjacency, with exact zero targets.
    var parents = List[List[Int]]()
    var d = List[Int]()
    var queue = List[Int]()
    for i in range(len(g.vertices)):
        parents.append(List[Int]())
        if g.vertices[i][2] == 0 and g.vertices[i][3] == 0 and g.vertices[i][4] == 0:
            d.append(0)
            queue.append(i)
        else:
            d.append(-1)
    for i in range(len(g.adj)):
        for j in g.adj[i]:
            parents[j].append(i)
    var head = 0
    while head < len(queue):
        var v = queue[head]
        head += 1
        for p in parents[v]:
            if d[p] < 0:
                d[p] = d[v]+1
                queue.append(p)
    return d^


def check_exact_support(g: BoundaryTemplate, a: Int) raises:
    if a < g.floor:
        raise Error("cross-check is below the certified parameter floor")
    var tables = build_seed_overlap_tables_screened(boundary_member(-1,a))
    var exact = build_seed_overlap_graph_from_tables(tables,20000)
    if exact.capped or exact.size() != len(g.vertices):
        raise Error("exact/template graph size mismatch or cap")
    var lengths = length_matrix(tables)
    var keys = List[Int]()
    for i in range(exact.size()):
        var v = exact.states[i]
        var w = offset_vector(lengths,v.shift)
        keys.append(label_key([v.top,v.bottom,w[0],w[1],w[2]]))
    for i in range(exact.size()):
        if keys[i] not in g.index:
            raise Error("exact vertex absent from symbolic template")
        var si = g.index[keys[i]]
        var children = Dict[Int, Int]()
        for j in exact.adj[i]:
            children[keys[j]] = 1
        if len(children) != len(g.adj[si]):
            raise Error("exact/template directed support sizes differ")
        for j in g.adj[si]:
            if label_key(g.vertices[j]) not in children:
                raise Error("symbolic edge absent from exact directed support")


def certify_minus_boundary() raises -> BoundaryTemplate:
    var g = boundary_template()
    var depths = template_depths(g)
    for d in depths:
        if d < 0 or d > 4:
            raise Error("symbolic vertex fails the claimed four-step hitting bound")
    # Exact finite prefix joins the uniform tail without a gap.
    for a in range(g.floor):
        var tables = build_seed_overlap_tables_screened(boundary_member(-1,a))
        var exact = build_seed_overlap_graph_from_tables(tables,20000)
        for d in first_left_aligned_depths(exact):
            if d < 0 or d > 4:
                raise Error("finite-prefix vertex fails the claimed four-step hitting bound")
    check_exact_support(g,4)
    check_exact_support(g,8)
    return g^
