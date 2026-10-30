"""Deterministic complete local stars; no all-depth closure verdict."""
from std.collections import Dict
from std.sys import argv
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.class_c_boundary_descendants import boundary_parent, boundary_children
from psc.perron_field3 import CubicElt
from class_c_seed_interfaces import compare_sets


def main() raises:
    var args = argv()
    var dump = len(args) == 2 and args[1] == "dump"
    if len(args) != 1 and not dump:
        raise Error("usage: class_c_boundary_descendants [dump]")
    var interfaces = 0
    var children = 0
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        var cache = Dict[CubicElt,Int]()
        for stage in range(2):
            var parent = boundary_parent(m,stage)
            var out = boundary_children(m,stage)
            compare_sets(out,segment_children(m,cache,parent))
            if dump:
                print("P",d,stage,parent.top,parent.bottom,parent.shift.a0,parent.shift.a1,parent.shift.a2)
                for i in range(len(out)):
                    var ch = out[i]
                    print("C",d,stage,ch.top,ch.bottom,ch.shift.a0,ch.shift.a1,ch.shift.a2)
            interfaces += 1
            children += len(out)
    print("BOUNDARY_DESCENDANT_INTERFACES_PASS",58,interfaces,children)
