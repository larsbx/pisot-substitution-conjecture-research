"""Deterministic, depth-bounded seed-interface replay; never a BH certificate."""
from std.collections import Dict
from std.sys import argv
from std.testing import assert_equal, assert_true
from psc.class_c_seed_interfaces import SeedInterface, segment_children
from psc.overlap_seed_patch import OverlapState
from psc.perron_field3 import CubicElt


def representative_cs(d: Int, eps: Int) -> List[Int]:
    var values = List[Int]()
    if d <= 9:
        for c in range(d+5 if eps == 1 else d-1):
            values.append(c)
    else:
        var candidates: List[Int] = [0,1,2,(d+1)//2,(d+1)//2+1,d-1,d,d+1,d+2,d+4] if eps == 1 else [0,1,(d-3)//2,(d-3)//2+1,d-2]
        for i in range(len(candidates)):
            if candidates[i] not in values:
                values.append(candidates[i])
    return values^


def compare_sets(a: List[OverlapState], b: List[OverlapState]) raises:
    assert_equal(len(a),len(b))
    var seen = Dict[OverlapState,Bool]()
    for i in range(len(a)):
        seen[a[i]] = True
    for i in range(len(b)):
        assert_true(b[i] in seen)


def emit(prefix: StringLiteral, d: Int, eps: Int, c: Int, id: Int, st: OverlapState):
    print(prefix,d,eps,c,id,st.top,st.bottom,st.shift.a0,st.shift.a1,st.shift.a2)


def replay(dump: Bool) raises:
    var members = 0
    var interfaces = 0
    for d in [7,8,9,16,31,64]:
        for eps in [1,-1]:
            var cs = representative_cs(d,eps)
            for cc in range(len(cs)):
                var c = cs[cc]
                var m = SeedInterface(d,eps,c)
                var cache = Dict[CubicElt,Int]()
                for seed in range(9):
                    var formula = m.children(seed)
                    var transfer = segment_children(m,cache,m.seed(seed))
                    compare_sets(formula,transfer)
                    if dump:
                        for k in range(len(formula)):
                            emit("C",d,eps,c,seed,formula[k])
                    interfaces += 1
                members += 1
    print("NINE_SEED_INTERFACES_PASS",members,interfaces)


def descendants(dump: Bool) raises:
    # Fixed budget: d=7, both signs, c=0,1,2, depth 4. Inflate every
    # distinct parent in generations 0..3 (including coincidences), never
    # infer closure from the last frontier. Hard stop before 4096 states.
    for eps in [1,-1]:
        for c in range(3):
            var m = SeedInterface(7,eps,c)
            var cache = Dict[CubicElt,Int]()
            var seen = Dict[OverlapState,Int]()
            var queue = List[OverlapState]()
            var depth = List[Int]()
            for s in range(9):
                seen[m.seed(s)] = len(queue)
                queue.append(m.seed(s))
                depth.append(0)
            var pos = 0
            var edges = 0
            while pos < len(queue):
                if depth[pos] >= 4:
                    pos += 1
                    continue
                var cs = segment_children(m,cache,queue[pos])
                if dump:
                    emit("P",7,eps,c,pos,queue[pos])
                    for k in range(len(cs)):
                        emit("E",7,eps,c,pos,cs[k])
                edges += len(cs)
                for k in range(len(cs)):
                    if cs[k] not in seen:
                        if len(queue) >= 4096:
                            raise Error("DESCENDANT_BUDGET_EXHAUSTED: no verdict")
                        seen[cs[k]] = len(queue)
                        queue.append(cs[k])
                        depth.append(depth[pos]+1)
                pos += 1
            var parents = 0
            for i in range(len(depth)):
                parents += Int(depth[i] < 4)
            print("BOUNDED_DESCENDANTS",7,eps,c,"depth",4,"parents",parents,"states",len(queue),"edges",edges,"closure_not_tested")


def main() raises:
    var args = argv()
    var dump = False
    if len(args) == 2 and args[1] == "dump":
        dump = True
    elif len(args) != 1:
        raise Error("usage: class_c_seed_interfaces [dump]")
    replay(dump)
    descendants(dump)
