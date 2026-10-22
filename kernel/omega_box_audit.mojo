"""Export named box graphs for the independent exact audit of Theorem Omega.

This driver calls the canonical graph and depth kernels; it introduces no new
certificate decision. Pipe stdout to a file and pass it to
oracles/python/omega_box_audit.py. The oracle checks every state and edge,
start-set coverage, shortest depths, and containment of recurrent offsets.
"""

from psc.overlap_seed_patch import build_seed_overlap_tables, first_coincidence_depths, first_left_aligned_depths
from psc.vertex_coincidence import box_radii, build_box_graph


def export(name: String, a: List[Int], b: List[Int], c: List[Int]) raises:
    var sigma = List[List[Int]]()
    sigma.append(a.copy())
    sigma.append(b.copy())
    sigma.append(c.copy())
    var tables = build_seed_overlap_tables(sigma)
    var radii = box_radii(tables)
    var box = build_box_graph(tables)
    if box.capped:
        raise Error("capped box is not an audit export")
    var coin = first_coincidence_depths(box)
    var zero = first_left_aligned_depths(box)
    print("specimen", name, tables.field.chi0, tables.field.chi1, tables.field.chi2)
    print("radii", radii[0], radii[1], radii[2])
    for k in range(3):
        var l = tables.lengths.at(k)
        print("length", k, l.a0, l.a1, l.a2)
    for i in range(box.size()):
        var s = box.states[i]
        var line = String("vertex ") + String(i) + " " + String(s.top) + " " + String(s.bottom)
        line += " " + String(s.shift.a0) + " " + String(s.shift.a1) + " " + String(s.shift.a2)
        line += " " + String(coin[i]) + " " + String(zero[i])
        for j in range(len(box.adj[i])):
            line += " " + String(box.adj[i][j])
        print(line)
    print("end", box.size())


def main() raises:
    export("tribonacci", [0, 1], [0, 2], [0])
    export("cube", [1], [2, 2, 2], [0, 2, 2, 2])
    export("golden", [1], [0, 2, 1], [0, 0, 1])
    export("plastic", [1], [2], [1, 0])
    export("real-secondary", [1], [0, 2], [2, 0, 2])
