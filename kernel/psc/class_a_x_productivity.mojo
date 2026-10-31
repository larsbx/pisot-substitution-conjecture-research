"""Complete oriented indexed overlap graphs: finite verdicts only.

Intern exact physical states but retain every full Parikh label and reject
any inconsistent lift. Preserve ordered occurrences. Reuse the vendored
iterative SCC kernel. Caps and arithmetic/sign failures yield no verdict.
"""
from std.collections import Dict
from finite_exact.checked_int import checked_add, checked_mul
from finite_graph.scc import sccs, has_cycle
from psc.class_a_boundary_children import (
    BoundaryLabel, geometric_state, member_transport, _run, _letter,
)
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, interior_overlap_cached, cached_sign,
)
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_sub_checked, cubic_mul_beta


struct IndexedGraph(Copyable, Movable):
    var states: List[BoundaryLabel]
    var adj: List[List[Int]]
    var ii: List[List[Int]]
    var jj: List[List[Int]]

    def __init__(out self, states: List[BoundaryLabel], adj: List[List[Int]],
                 ii: List[List[Int]], jj: List[List[Int]]):
        self.states=states.copy()
        self.adj=adj.copy()
        self.ii=ii.copy()
        self.jj=jj.copy()


def terminal(w: BoundaryLabel) -> Bool:
    return w.top==w.bottom and w.x==0 and w.c==0 and w.y==0


def nine_sources() -> List[BoundaryLabel]:
    return [BoundaryLabel(0,1,0,0,0),BoundaryLabel(0,0,0,1,0),
            BoundaryLabel(1,0,-1,1,0),BoundaryLabel(0,2,0,0,0),
            BoundaryLabel(0,0,0,0,1),BoundaryLabel(2,0,-1,0,1),
            BoundaryLabel(1,2,0,0,0),BoundaryLabel(1,1,0,0,1),
            BoundaryLabel(2,1,0,-1,1)]


def _intern(tables: SeedOverlapTables,mut states: List[BoundaryLabel],
            mut ids: Dict[OverlapState,Int],w: BoundaryLabel,cap: Int) raises -> Int:
    var key=geometric_state(tables,w)
    if key in ids:
        var v=ids[key]
        if states[v]!=w:
            raise Error("physical interning lost a full Parikh coordinate")
        return v
    if len(states)>=cap:
        raise Error("incomplete indexed graph: cap reached, no verdict")
    var v=len(states)
    states.append(w)
    ids[key]=v
    return v


def build_indexed(tables: SeedOverlapTables,k: Int,t: Int,cap: Int=6000) raises -> IndexedGraph:
    if k<0 or t<0 or cap<1:
        raise Error("invalid minus graph parameters or cap")
    var n=checked_add(checked_add(k,t),3)
    var d=checked_add(checked_add(k,checked_mul(2,t)),5)
    if len(tables.sigma)!=3:
        raise Error("wrong alphabet in indexed graph tables")
    for p in range(3):
        if len(tables.sigma[p])!=checked_add(_run(-1,n,d,p),2):
            raise Error("indexed graph tables have different image lengths")
        for z in range(len(tables.sigma[p])):
            if tables.sigma[p][z]!=_letter(-1,n,d,p,z):
                raise Error("indexed graph tables have different literal words")
    var states=List[BoundaryLabel]()
    var ids=Dict[OverlapState,Int]()
    var cache=Dict[CubicElt,Int]()
    for w in nine_sources():
        for flip in [False,True]:
            var z=reversed_label(w) if flip else w
            if not interior_overlap_cached(tables,cache,geometric_state(tables,z)):
                raise Error("non-strict swap source")
            _=_intern(tables,states,ids,z,cap)
    if len(states)!=18:
        raise Error("eighteen distinct orientations required")
    var adj=List[List[Int]]()
    var ii=List[List[Int]]()
    var jj=List[List[Int]]()
    var cursor=0
    while cursor<len(states):
        var w=states[cursor]
        var targets=List[Int]()
        var top_indices=List[Int]()
        var bottom_indices=List[Int]()
        if not terminal(w):
            var source=geometric_state(tables,w)
            var scaled=cubic_mul_beta(tables.field,source.shift)
            # The existing overlap_seed_patch streaming partition sweep,
            # specialized to retain actual ordinals and their Parikh lifts.
            var first_bottom=0
            var bottom_count=len(tables.sigma[w.bottom])
            for i in range(len(tables.sigma[w.top])):
                var top_prefix=tables.prefix(w.top,i)
                var top_end=cubic_add_checked(top_prefix,tables.lengths.at(tables.sigma[w.top][i]))
                while first_bottom<bottom_count:
                    var bstart=cubic_add_checked(scaled,tables.prefix(w.bottom,first_bottom))
                    var bend=cubic_add_checked(bstart,tables.lengths.at(tables.sigma[w.bottom][first_bottom]))
                    if cached_sign(tables,cache,cubic_sub_checked(bend,top_prefix))>0:
                        break
                    first_bottom+=1
                var j=first_bottom
                while j<bottom_count:
                    var bstart=cubic_add_checked(scaled,tables.prefix(w.bottom,j))
                    if cached_sign(tables,cache,cubic_sub_checked(bstart,top_end))>=0:
                        break
                    var child=member_transport(-1,k,n,d,w,i,j)
                    if interior_overlap_cached(tables,cache,geometric_state(tables,child)):
                        targets.append(_intern(tables,states,ids,child,cap))
                        top_indices.append(i)
                        bottom_indices.append(j)
                    j+=1
        adj.append(targets^)
        ii.append(top_indices^)
        jj.append(bottom_indices^)
        cursor+=1
    return IndexedGraph(states,adj,ii,jj)


def backwards(adj: List[List[Int]],roots: List[Int]) raises -> List[Int]:
    var rev=List[List[Int]]()
    var distance=List[Int]()
    for _ in range(len(adj)):
        rev.append(List[Int]())
        distance.append(-1)
    for v in range(len(adj)):
        for w in adj[v]:
            if w<0 or w>=len(adj):
                raise Error("invalid adjacency")
            rev[w].append(v)
    var queue=List[Int]()
    for root in roots:
        if root<0 or root>=len(adj):
            raise Error("invalid root")
        if distance[root]<0:
            distance[root]=0
            queue.append(root)
    var cursor=0
    while cursor<len(queue):
        var w=queue[cursor]
        cursor+=1
        for v in rev[w]:
            if distance[v]<0:
                distance[v]=distance[w]+1
                queue.append(v)
    return distance^


def summarize(tables: SeedOverlapTables,g: IndexedGraph) raises -> List[Int]:
    var roots=List[Int]()
    var xid=-1
    var edges=0
    var sparse=List[List[Int]]()
    var corners=List[List[Int]]()
    var reverse_adj=List[List[Int]]()
    for v in range(len(g.states)):
        reverse_adj.append(List[Int]())
        if terminal(g.states[v]):
            roots.append(v)
        if g.states[v]==BoundaryLabel(0,0,1,0,-1):
            xid=v
        edges=checked_add(edges,len(g.adj[v]))
        var ss=List[Int]()
        var cc=List[Int]()
        var a=g.states[v]
        for z in range(len(g.adj[v])):
            var i=g.ii[v][z]
            var j=g.jj[v][z]
            var ti=i==0 or i==len(tables.sigma[a.top])-1
            var bj=j==0 or j==len(tables.sigma[a.bottom])-1
            if ti or bj:
                ss.append(g.adj[v][z])
            if ti and bj:
                cc.append(g.adj[v][z])
        sparse.append(ss^)
        corners.append(cc^)
    if xid<0 or len(roots)==0:
        raise Error("X or coincidence absent")
    for v in range(len(g.states)):
        for w in g.adj[v]:
            reverse_adj[w].append(v)
    var dc=backwards(g.adj,roots)
    var dx=backwards(g.adj,[xid])
    var forward_x=backwards(reverse_adj,[xid])
    var de=backwards(sparse,roots)
    var corner_depth=backwards(corners,roots)
    var parts=sccs(g.adj)
    var owner=List[Int]()
    for _ in g.states:
        owner.append(-1)
    for z in range(len(parts)):
        for v in parts[z]:
            owner[v]=z
    var maxc=0
    var maxx=0
    var maxe=0
    var bad=0
    var nonreturn=0
    var sparse_bad=0
    var corners_bad=0
    var xcount=0
    var xcomponent=len(parts[owner[xid]])
    for v in range(len(g.states)):
        maxc=max(maxc,dc[v])
        maxx=max(maxx,dx[v])
        maxe=max(maxe,de[v])
        bad+=Int(dc[v]<0)
        nonreturn+=Int(dx[v]<0 and not terminal(g.states[v]))
        sparse_bad+=Int(de[v]<0)
        corners_bad+=Int(corner_depth[v]<0)
        xcount+=Int(forward_x[v]>=0)
        if (owner[v]==owner[xid])!=(forward_x[v]>=0 and dx[v]>=0):
            raise Error("X SCC fails independent forward/backward identity")
    var sinks=0
    var bad_sinks=0
    var recurrent=0
    for z in range(len(parts)):
        recurrent+=Int(has_cycle(g.adj,parts[z]))
        var sink=True
        for v in parts[z]:
            for w in g.adj[v]:
                if owner[w]!=z:
                    sink=False
        if sink:
            sinks+=1
            bad_sinks+=Int(dc[parts[z][0]]<0)
    return [len(g.states),edges,xcount,len(parts),xcomponent,len(roots),recurrent,sinks,
            bad_sinks,bad,nonreturn,maxc,maxx,sparse_bad,maxe,corners_bad]
