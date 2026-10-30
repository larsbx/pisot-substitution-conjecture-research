"""Complete outgoing interfaces for the ten Q children; no closure test."""
from std.collections import Dict
from std.sys import argv
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.class_c_boundary_frontier import frontier_parent, frontier_children
from psc.perron_field3 import CubicElt
from class_c_seed_interfaces import compare_sets


def main() raises:
    var args = argv()
    var dump = len(args) == 2 and args[1] == "dump"
    if len(args) != 1 and not dump:
        raise Error("usage: class_c_boundary_frontier [dump]")
    var count = 0
    var total = 0
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        var cache = Dict[CubicElt,Int]()
        for index in range(10):
            var parent = frontier_parent(m,index)
            var cs = frontier_children(m,index)
            compare_sets(cs,segment_children(m,cache,parent))
            if dump:
                print("P",d,index,parent.top,parent.bottom,parent.shift.a0,parent.shift.a1,parent.shift.a2)
                for i in range(len(cs)):
                    var ch = cs[i]
                    print("C",d,index,ch.top,ch.bottom,ch.shift.a0,ch.shift.a1,ch.shift.a2)
            print("COUNTS",d,index,len(cs))
            count += 1
            total += len(cs)
    print("BOUNDARY_TEN_FRONTIER_PASS",58,count,total)
