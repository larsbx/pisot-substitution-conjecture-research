"""Canonical exact finite calibration; no CycleSum or uniform BH conclusion.

Uses the complete swap-seed graph, not the conditional 1971-state superset.
All distinct-letter zero offsets are classified. Unknown labels and sum-bound
violations retain seed paths and closed cycles with actual occurrence indices.
"""
from finite_exact.checked_int import checked_add, checked_abs
from psc.perron_field3 import CubicElt
from psc.overlap_seed_patch import (
    OverlapState, SeedOverlapTables, SeedOverlapAutomaton,
    build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables,
    seed_overlap_states, selected_overlap_child, interior_overlap,
)
from psc.overlap_obstruction import recurrent_sccs
from psc.vertex_coincidence import length_matrix, offset_vector, offset_of
from psc.class_d_minus_spine_data import minus_spine_rows
from psc.class_d_minus_cycle_superset import CycleState, _exceptional


def member(a: Int, b: Int) raises -> List[List[Int]]:
    # Explicit finite calibration budget bounds all parameter arithmetic.
    if a < 2 or b < 1 or a > 100 or b > 100:
        raise Error("calibration parameter budget: 2<=a<=100, 1<=b<=100")
    var out = List[List[Int]]()
    for letter in range(3):
        var word = List[Int]()
        word.append(0 if letter == 0 else 1)
        var run = 3*a+5+b if letter == 0 else (3*a+6+b if letter == 1 else 2*a+4+b)
        for _ in range(run):
            word.append(2)
        word.append(0 if letter == 1 else 1)
        out.append(word^)
    return out^


def label(tables: SeedOverlapTables, state: OverlapState) raises -> CycleState:
    var w = offset_vector(length_matrix(tables),state.shift)
    var lengths = List[CubicElt]()
    for i in range(3):
        lengths.append(tables.lengths.at(i))
    if offset_of(lengths,w) != state.shift:
        raise Error("offset inverse replay failed")
    return CycleState(state.top,state.bottom,w[0],w[1],w[2])


def state_of(tables: SeedOverlapTables, v: CycleState) raises -> OverlapState:
    var lengths = List[CubicElt]()
    for i in range(3):
        lengths.append(tables.lengths.at(i))
    return OverlapState(v.top,v.bottom,offset_of(lengths,[v.x,v.c,v.y]))


def carrier_index(v: CycleState, rows: List[List[Int]]) -> Int:
    for i in range(len(rows)):
        if rows[i][0] == v.top and rows[i][1] == v.bottom and rows[i][2] == v.x and rows[i][3] == v.c and rows[i][4] == v.y:
            return i
    return -1


def classify(v: CycleState, rows: List[List[Int]]) -> String:
    if v.top == v.bottom and v.is_zero_offset():
        return "coincidence"
    if carrier_index(v,rows) >= 0:
        return "carrier"
    if v.top == 1 and v.bottom == 0 and v.is_zero_offset():
        return "boundary_hit_noncoincidence"
    if _exceptional(v):
        return "exceptional"
    # No blanket acceptance of distinct-letter zero offsets.
    return "unexplained"


def exceptional_exit(tables: SeedOverlapTables, v: CycleState, a: Int, b: Int) raises -> Int:
    if not _exceptional(v):
        raise Error("exceptional exit requested for an unknown label")
    var state = state_of(tables,v)
    if not interior_overlap(tables,state):
        raise Error("exceptional source is not an interior overlap")
    var mirror = v.top == 1
    var is_u = v.x == -2 or v.x == 2
    var ti = b if mirror else 0
    var bi = 0 if mirror else b
    if not is_u:
        ti = a+2 if mirror else b
        bi = b if mirror else a+2
    var child = selected_overlap_child(tables,state,ti,bi)
    if not interior_overlap(tables,child):
        raise Error("exceptional child is not an interior overlap")
    print("EXCEPTION_EXIT",a,b,v.key(),ti,bi,label(tables,child).key())
    var depth = 1
    if not is_u:
        var expected = CycleState(2,2,3 if mirror else -3,-5 if mirror else 5,3 if mirror else -3)
        if label(tables,child).key() != expected.key():
            raise Error("V intermediate label changed")
        ti = b-1 if mirror and b>=2 else 0
        bi = b-1 if not mirror and b>=2 else 0
        var target = selected_overlap_child(tables,child,ti,bi)
        if not interior_overlap(tables,target):
            raise Error("exceptional carrier target is not interior")
        print("EXCEPTION_EXIT",a,b,expected.key(),ti,bi,label(tables,target).key())
        child = target
        depth = 2
    var rows = minus_spine_rows()
    var expected_row = 97 if mirror else 69
    if not is_u and b == 1:
        expected_row = 35 if mirror else 44
    if carrier_index(label(tables,child),rows) != expected_row or rows[expected_row][5] > 2:
        raise Error("exceptional path missed its rank<=2 carrier target")
    return depth


def _path(adj: List[List[Int]], starts: List[Int], target: Int) raises -> List[Int]:
    var parent = List[Int]()
    for _ in range(len(adj)):
        parent.append(-1)
    var queue = List[Int]()
    for s in starts:
        parent[s] = s
        queue.append(s)
    var h = 0
    while h < len(queue) and parent[target] < 0:
        var at = queue[h]
        h += 1
        for to in adj[at]:
            if parent[to] < 0:
                parent[to] = at
                queue.append(to)
    if parent[target] < 0:
        return List[Int]()
    var backwards = List[Int]()
    var at = target
    backwards.append(at)
    while parent[at] != at:
        at = parent[at]
        backwards.append(at)
    var out = List[Int]()
    for i in range(len(backwards)):
        out.append(backwards[len(backwards)-1-i])
    return out^


def _emit_path(tables: SeedOverlapTables, g: SeedOverlapAutomaton, path: List[Int], kind: String, a: Int, b: Int) raises:
    for k in range(len(path)-1):
        var source = g.states[path[k]]
        var target = g.states[path[k+1]]
        var found = False
        for i in range(len(tables.sigma[source.top])):
            for j in range(len(tables.sigma[source.bottom])):
                if selected_overlap_child(tables,source,i,j) == target:
                    print("REPLAY_EDGE",kind,a,b,label(tables,source).key(),i,j,label(tables,target).key())
                    found = True
                    break
            if found:
                break
        if not found:
            raise Error("graph edge has no replayable occurrence")


def emit_counterexample(tables: SeedOverlapTables, g: SeedOverlapAutomaton, at: Int, a: Int, b: Int) raises:
    var roots = List[Int]()
    var seeds = seed_overlap_states(tables)
    for seed in seeds:
        for i in range(g.size()):
            if g.states[i] == seed:
                roots.append(i)
    var path = _path(g.adj,roots,at)
    if len(path) == 0:
        raise Error("recurrent label lost seed reachability")
    print("COUNTEREXAMPLE",a,b,label(tables,g.states[at]).key(),"seed",label(tables,g.states[path[0]]).key())
    _emit_path(tables,g,path,"seed",a,b)
    for child in g.adj[at]:
        var back = _path(g.adj,[child],at)
        if len(back) > 0:
            var cycle = List[Int]([at])
            for v in back:
                cycle.append(v)
            _emit_path(tables,g,cycle,"cycle",a,b)
            return
    raise Error("recurrent label lost its cycle")


def recurrent_report(a: Int, b: Int, cap: Int = 20000) raises -> List[Int]:
    var tables = build_seed_overlap_tables_screened(member(a,b))
    var g = build_seed_overlap_graph_from_tables(tables,cap)
    if g.capped:
        print("STATE_BUDGET_EXHAUSTED",a,b,cap)
        raise Error("partial graph cannot classify recurrent support")
    var rows = minus_spine_rows()
    var comps = recurrent_sccs(g)
    var counts: List[Int] = [g.size(),0,len(comps),0,0,0,0,0,0]
    # states, recurrent, SCCs, carrier, coincidence, exceptional, unexplained, max_abs_sum, named noncoincident BH target
    for comp in comps:
        for at in comp:
            var v = label(tables,g.states[at])
            var kind = classify(v,rows)
            var total = checked_add(checked_add(v.x,v.c),v.y)
            counts[1] += 1
            counts[7] = max(counts[7],checked_abs(total))
            print("RECURRENT_LABEL",a,b,v.top,v.bottom,v.x,v.c,v.y,kind)
            if kind == "carrier":
                counts[3] += 1
            elif kind == "coincidence":
                counts[4] += 1
            elif kind == "boundary_hit_noncoincidence":
                counts[8] += 1
            elif kind == "exceptional":
                _ = exceptional_exit(tables,v,a,b)
                counts[5] += 1
            else:
                counts[6] += 1
            if kind == "unexplained" or checked_abs(total) > 1:
                emit_counterexample(tables,g,at,a,b)
    print("RECURRENT_SUMMARY",a,b,counts[0],counts[1],counts[2],counts[3],counts[4],counts[5],counts[6],counts[7],counts[8])
    return counts^
