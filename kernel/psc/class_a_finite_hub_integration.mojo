"""Canonical FINITE four/nine-seed graph and hub audits; never universal BH."""
from std.collections import Dict
from a1_normal_form_census import class_member, CLASS_A
from psc.class_a_boundary_children import BoundaryLabel, geometric_state
from psc.class_a_native_length_contract import verify_native_length_normalization, decode_native_parikh_shift
from psc.overlap_seed_patch import OverlapState, SeedOverlapAutomaton, build_seed_overlap_tables_screened, build_overlap_graph_from_seeds, interior_overlap_cached, first_depths, first_coincidence_depths
from psc.overlap_obstruction import overlap_sccs, recurrent_sccs, nonproductive_sink_sccs
from psc.perron_field3 import CubicElt


def forward(adj: List[List[Int]],root: Int) raises -> List[Bool]:
    if root<0 or root>=len(adj):raise Error("unknown graph root")
    var seen=List[Bool](length=len(adj),fill=False)
    var queue=List[Int]([root]);seen[root]=True
    var head=0
    while head<len(queue):
        var v=queue[head];head+=1
        for w in adj[v]:
            if w<0 or w>=len(adj):raise Error("unknown child vertex")
            if not seen[w]:seen[w]=True;queue.append(w)
    return seen^


def finite_extension_criterion(adj: List[List[Int]],seeds: List[Int],hub: Int,exception: Int) raises -> Bool:
    if exception<0 or exception>=len(adj):raise Error("unknown exception")
    var reach=forward(adj,hub)
    for s in seeds:
        if s<0 or s>=len(adj):raise Error("unknown seed")
        if s!=exception and not reach[s]:return False
    for w in adj[exception]:
        if w<0 or w>=len(adj):raise Error("unknown exception child")
        if w!=exception and not reach[w]:return False
    for s in seeds:
        var actual=forward(adj,s)
        for i in range(len(actual)):
            if actual[i] and not reach[i] and i!=exception:raise Error("finite hub-extension invariant failed")
    return True


def finite_hub_graph(mode: Int,k: Int,t: Int,cap: Int=6000) raises -> SeedOverlapAutomaton:
    if (mode!=4 and mode!=9) or k<0 or k>3 or t<0 or t>3 or cap<=0 or cap>6000:raise Error("finite hub audit scope/budget")
    var n=k+t+3
    var d=k+2*t+5
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n-1))
    _=verify_native_length_normalization(tables,n,d)
    var cache=Dict[CubicElt,Int]()
    var labels=List[BoundaryLabel]()
    if mode==4:
        labels=[BoundaryLabel(0,0,1,0,-1),BoundaryLabel(2,2,1,-1,-1),BoundaryLabel(1,2,0,-2,2),BoundaryLabel(1,1,0,-2,3)]
    else:
        labels=[BoundaryLabel(0,1,0,0,0),BoundaryLabel(0,0,0,1,0),BoundaryLabel(1,0,-1,1,0),BoundaryLabel(0,2,0,0,0),BoundaryLabel(0,0,0,0,1),BoundaryLabel(2,0,-1,0,1),BoundaryLabel(1,2,0,0,0),BoundaryLabel(1,1,0,0,1),BoundaryLabel(2,1,0,-1,1)]
    var seeds=List[OverlapState]()
    for w in labels:
        var state=geometric_state(tables,w)
        if not interior_overlap_cached(tables,cache,state):raise Error("non-strict finite seed")
        seeds.append(state)
    var graph=build_overlap_graph_from_seeds(tables,seeds,cache,cap)
    if graph.capped:raise Error("incomplete finite graph; no hub or productivity verdict")
    return graph^


def finite_hub_audit(mode: Int,k: Int,t: Int,cap: Int=6000,export: Bool=False) raises -> List[Int]:
    var graph=finite_hub_graph(mode,k,t,cap)
    var n=k+t+3
    var d=k+2*t+5
    var labels=List[BoundaryLabel]()
    var hub = -1
    var exception = -1
    var terminals=0
    var edges=0
    for i in range(graph.size()):
        var v=graph.states[i]
        var w=decode_native_parikh_shift(n,d,v.shift)
        var label=BoundaryLabel(v.top,v.bottom,w[0],w[1],w[2])
        labels.append(label)
        if label==BoundaryLabel(0,0,1,0,-1):hub=i
        if label==BoundaryLabel(0,0,0,1,0):exception=i
        terminals+=1 if v.is_coincidence() else 0
        edges+=len(graph.adj[i])
        if v.is_coincidence() and len(graph.adj[i])!=0:raise Error("coincidence not terminalized")
    if hub<0:raise Error("missing canonical X hub")
    var mask=List[Bool](length=graph.size(),fill=False);mask[hub]=True
    var to_hub=first_depths(graph,mask)
    var to_coincidence=first_coincidence_depths(graph)
    var reach=forward(graph.adj,hub)
    var maxhub=0;var maxcoinc=0;var outside=0
    for i in range(graph.size()):
        if to_coincidence[i]<0 or (not graph.states[i].is_coincidence() and to_hub[i]<0):raise Error("finite productivity or hub claim refused")
        maxhub=max(maxhub,to_hub[i]);maxcoinc=max(maxcoinc,to_coincidence[i])
        if not reach[i]:
            outside+=1
            if mode==9 and i!=exception:raise Error("nine-seed outside-X vertex is not S1")
    var components=overlap_sccs(graph)
    var recurrent=recurrent_sccs(graph)
    var bad=nonproductive_sink_sccs(graph)
    if terminals!=2 or len(recurrent)!=1 or len(bad)!=0:raise Error("finite hub SCC calibration failed")
    if mode==9:
        if exception<0:raise Error("missing nine-seed S1")
        var seeds=List[Int]()
        for i in range(9):seeds.append(i)
        if not finite_extension_criterion(graph.adj,seeds,hub,exception):raise Error("finite nine-seed extension hypotheses refused")
    if export:
        print("GRAPH",mode,k,t,graph.size(),edges)
        for i in range(graph.size()):
            var w=labels[i]
            var line="V "+String(i)+" "+String(w.top)+" "+String(w.bottom)+" "+String(w.x)+" "+String(w.c)+" "+String(w.y)
            for child in graph.adj[i]:line+=" "+String(child)
            print(line)
    return [graph.size(),edges,len(components),len(recurrent),len(bad),terminals,maxhub,maxcoinc,outside]
