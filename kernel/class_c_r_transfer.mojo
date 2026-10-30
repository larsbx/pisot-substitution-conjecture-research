"""Three exact R/T/U interfaces, and a strict translation negative control."""
from std.sys import argv
from psc.class_c_seed_interfaces import SeedInterface
from psc.class_c_boundary_frontier import BoundaryOffset, boundary_offset_children, frontier_children
from psc.perron_field3 import cubic_add_checked, cubic_mul_beta
from psc.class_c_r_transfer import r_parent, r_children
from class_c_seed_interfaces import compare_sets


def main() raises:
    var args = argv()
    var dump = len(args) == 2 and args[1] == "dump"
    if len(args) != 1 and not dump:
        raise Error("usage: class_c_r_transfer [dump]")
    for d in range(7,65):
        var m = SeedInterface(d,1,0)
        for index in range(3):
            var parent = r_parent(m,index)
            var offset = BoundaryOffset(-2,2,1) if index == 0 else (BoundaryOffset(-1,1,-4) if index == 1 else BoundaryOffset(3,-3,4))
            var cs = r_children(m,index)
            compare_sets(cs,boundary_offset_children(m,parent.top,parent.bottom,offset))
            if dump:
                print("P",d,index,parent.top,parent.bottom,parent.shift.a0,parent.shift.a1,parent.shift.a2)
                for i in range(len(cs)):
                    var ch = cs[i]
                    print("C",d,index,ch.top,ch.bottom,ch.shift.a0,ch.shift.a1,ch.shift.a2)
    print("R_TRANSFER_INTERFACES_PASS",58,174,870)
    var m = SeedInterface(7,1,0)
    var base = frontier_children(m,0)
    var target = boundary_offset_children(m,0,2,BoundaryOffset(3,-3,4))
    var delta = cubic_mul_beta(m.tables.field,m.v(1,-1,-1))
    for i in range(len(base)):
        var ch = base[i]
        ch.shift = cubic_add_checked(ch.shift,delta)
        var found = False
        for j in range(len(target)):
            found = found or ch == target[j]
        if not found:
            print("N",ch.top,ch.bottom,ch.shift.a0,ch.shift.a1,ch.shift.a2)
            print("R_TRANSLATION_NONCOMMUTATION_PASS",len(base),len(target))
            return
    raise Error("negative translation control unexpectedly had no escaping state")
