"""Canonical complete 18-source graphs vs independent literal/Fraction pins."""
from std.testing import assert_true
from std.sys import argv
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.class_a_x_productivity import build_indexed, summarize, backwards


def main() raises:
    var args=argv()
    var emit=len(args)==2 and args[1]=="--emit-indexed"
    var members=List[List[Int]]()
    for k in range(4):
        for t in range(4):
            members.append([k,t])
    members.append([0,4])
    members.append([4,0])
    members.append([4,4])
    members.append([0,8])
    members.append([8,0])
    members.append([8,8])
    var pins=List[Int]([784,1010,1220,1440,436,642,646,836,378,390,594,568,
                       352,342,362,548,1632,340,518,2312,326,456])
    var total_vertices=0
    var total_edges=0
    for z in range(len(members)):
        var k=members[z][0]
        var t=members[z][1]
        var n=k+t+3
        var d=k+2*t+5
        var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n-1))
        var graph=build_indexed(tables,k,t)
        if emit:
            for v in range(len(graph.states)):
                var w=graph.states[v]
                print("X_VERTEX",k,t,v,w.top,w.bottom,w.x,w.c,w.y)
                for q in range(len(graph.adj[v])):
                    print("X_EDGE",k,t,v,graph.adj[v][q],graph.ii[v][q],graph.jj[v][q])
        var row=summarize(tables,graph)
        assert_true(row[0]==pins[z])
        assert_true(row[2]==row[4]+2)
        assert_true(row[5]==2 and row[6]==1 and row[7]==2)
        assert_true(row[8]==0 and row[9]==0 and row[10]==0 and row[13]==0)
        assert_true(row[15]>0)
        if k==3 and t==0:
            assert_true(row[2]==350 and row[4]==348)
        total_vertices+=row[0]
        total_edges+=row[1]
        print("X_GRAPH",k,t,row)
    assert_true(total_vertices==16132 and total_edges==190966)
    var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,8,3,2))
    var refused=False
    try:
        _=build_indexed(tables,0,0,18)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        _=build_indexed(tables,0,1)
    except:
        refused=True
    assert_true(refused)
    var bad=List[List[Int]]()
    bad.append([0])
    bad.append(List[Int]())
    assert_true(backwards(bad,[1])[0]==-1)
    bad[0].append(1)
    assert_true(backwards(bad,[1])[0]==1)
    print("X_GRAPH_TOTAL",total_vertices,total_edges)
    require_contract("ClassAXCompleteOrientedIndexedFiniteGraphs")
