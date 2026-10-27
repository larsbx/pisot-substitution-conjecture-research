"""Exact bounded class-B top-layer canonical label export; no uniform certificate."""
from std.sys import argv
from a1_normal_form_census import CLASS_B, class_member
from class_b_top_layer_profile import top_layer_member, in_open_top_layer
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables, first_left_aligned_depths
from psc.vertex_coincidence import length_matrix, offset_vector
from psc.class_a_gap_dataset import _less
from psc.class_b_ray_carrier import prefix
from psc.bpa import substitution_incidence
from finite_linear_algebra.mat3 import Mat3


def label_block(plus: Bool, gap: Int, q: Int, cap: Int = 20000, witnesses: Bool = False, edges: Bool = False) raises -> String:
    if gap < 1 or gap > 5 or q < 1 or q > 48 or cap < 1 or cap > 20000:
        raise Error("bounded pilot domain: 1<=gap<=5, 1<=q<=48, 1<=cap<=20000")
    var t = top_layer_member(plus, gap - 1, q)
    if not in_open_top_layer(plus, t[0], q):
        raise Error("not in open top layer")
    var tables = build_seed_overlap_tables_screened(class_member(CLASS_B, t[0], q, t[2]))
    var graph = build_seed_overlap_graph_from_tables(tables, cap)
    if graph.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no label verdict")
    var depths = first_left_aligned_depths(graph)
    var lm = length_matrix(tables)
    var rows = List[List[Int]]()
    var deepest = 0
    for i in range(graph.size()):
        if depths[i] < 0:
            raise Error("vertex without offset-zero descendant")
        deepest = max(deepest, depths[i])
        var v = graph.states[i]
        var w = offset_vector(lm, v.shift)
        for coordinate in w:
            if coordinate < -20000 or coordinate > 20000:
                raise Error("offset coordinate budget exhausted")
        rows.append([v.top, v.bottom, w[0], w[1], w[2], depths[i], i])
    for i in range(1, len(rows)):
        var x = rows[i].copy()
        var j = i
        while j > 0 and _less(x, rows[j - 1]):
            rows[j] = rows[j - 1].copy()
            j -= 1
        rows[j] = x^
    var out = "M " + String(q) + " " + String(graph.size()) + " " + String(deepest) + "\n"
    var rank = List[Int](length=graph.size(), fill=0)
    for r in range(len(rows)):
        rank[rows[r][6]] = r
    for row in rows:
        out += "V"
        for h in range(6):
            out += " " + String(row[h])
        out += "\n"
    if edges:
        # Every adjacency edge, parents and children both in sorted label order.
        for row in rows:
            var children = List[Int]()
            for child in graph.adj[row[6]]:
                var r = rank[child]
                var h = len(children)
                children.append(r)
                while h > 0 and children[h - 1] > r:
                    children[h] = children[h - 1]
                    h -= 1
                children[h] = r
            for r in children:
                out += "E"
                for h in range(5):
                    out += " " + String(row[h])
                for h in range(5):
                    out += " " + String(rows[r][h])
                out += "\n"
    if witnesses:
        var matrix = Mat3(substitution_incidence(tables.sigma))
        for z in range(graph.size()):
            if depths[z] == 0:
                continue
            var dest = -1
            for child in graph.adj[z]:
                if depths[child] == depths[z] - 1:
                    dest = child
                    break
            if dest < 0:
                raise Error("missing shortest descent child")
            var v = graph.states[z]
            var child = graph.states[dest]
            var w = offset_vector(lm, v.shift)
            var cw = offset_vector(lm, child.shift)
            var mw = matrix.apply(w)
            var chosen_i = -1
            var chosen_j = -1
            for i in range(len(tables.sigma[v.top])):
                if tables.sigma[v.top][i] != child.top:
                    continue
                var pa = prefix(plus, gap, q, v.top, i)
                var jy = cw[2] - mw[2] + pa[2]
                for j in [0, jy + 1]:
                    if j < 0 or j >= len(tables.sigma[v.bottom]) or tables.sigma[v.bottom][j] != child.bottom:
                        continue
                    var pb = prefix(plus, gap, q, v.bottom, j)
                    var equal = True
                    for h in range(3):
                        if mw[h] + pb[h] - pa[h] != cw[h]:
                            equal = False
                    if equal:
                        chosen_i = i
                        chosen_j = j
                        break
                if chosen_i >= 0:
                    break
            if chosen_i < 0:
                raise Error("adjacency child has no reconstructed actual occurrence")
            out += "W " + String(v.top) + " " + String(v.bottom)
            for h in w:
                out += " " + String(h)
            out += " " + String(child.top) + " " + String(child.bottom)
            for h in cw:
                out += " " + String(h)
            out += " " + String(chosen_i) + " " + String(chosen_j) + "\n"
    return out^


def main() raises:
    var args = argv()
    if (len(args) != 4 and len(args) != 5) or (String(args[1]) != "plus" and String(args[1]) != "minus"):
        raise Error("usage: plus|minus GAP Q [witnesses|edges]")
    var mode = String(args[4]) if len(args) == 5 else String("")
    if mode != "" and mode != "witnesses" and mode != "edges":
        raise Error("unknown export mode")
    print(label_block(String(args[1]) == "plus", Int(String(args[2])), Int(String(args[3])), 20000, mode == "witnesses", mode == "edges"), end="")
