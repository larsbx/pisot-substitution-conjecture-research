"""Finite full-set replay of an all-d indexed local theorem; no closure test."""
from std.sys import argv
from std.collections import Dict
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.class_c_indexed_transfer import indexed_parent, indexed_children, indexed_representatives
from psc.perron_field3 import CubicElt
from class_c_seed_interfaces import compare_sets


def main() raises:
    var args = argv()
    var dump = len(args) == 2 and args[1] == "dump"
    if len(args) != 1 and not dump:
        raise Error("usage: class_c_indexed_transfer [dump]")
    var cases = 0
    var total = 0
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        var cache = Dict[CubicElt,Int]()
        var Ks = indexed_representatives(d)
        for index in range(len(Ks)):
            var K = Ks[index]
            var parent = indexed_parent(m,K)
            var cs = indexed_children(m,K)
            compare_sets(cs,segment_children(m,cache,parent))
            if dump:
                print("P",d,K,parent.top,parent.bottom,parent.shift.a0,parent.shift.a1,parent.shift.a2)
                for i in range(len(cs)):
                    var ch = cs[i]
                    print("C",d,K,ch.top,ch.bottom,ch.shift.a0,ch.shift.a1,ch.shift.a2)
            cases += 1
            total += len(cs)
    print("INDEXED_TRANSFER_INTERFACES_PASS",58,cases,total)
