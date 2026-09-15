"""Exact census: first left-aligned depth against the contracting lower bound.

For every alphabet-3 PIP substitution with images of length at most 3, builds
the seed-patch overlap graph, computes the first left-aligned depth `b` of
every vertex (`psc.overlap_seed_patch`) and the contracting lower bound `m_0`
of manuscript Proposition 5.42 (`psc.overlap_contracting`), checks `m_0 <= b`
on every vertex and `m_0 = 0` exactly at offset zero, and reports the
distributions of `m_0` and of the excess `b - m_0`.  A nonproductive graph is
recorded before any depth statistic.  The Python oracle
`scripts/overlap_contracting_census.py` prints the same summary lines (all
but the specimen-count header).
"""

from psc.bpa import substitution_incidence
from finite_linear_algebra.mat3 import Mat3
from psc.pisot import is_pip
from psc.overlap_contracting import ContractingBound
from psc.overlap_seed_patch import (
    build_seed_overlap_graph_from_tables,
    build_seed_overlap_tables,
    first_left_aligned_depths,
    nonproductive_overlap_states,
)
from psc.perron_field3 import CubicElt


def image_words() -> List[List[Int]]:
    var out = List[List[Int]]()
    for a in range(3):
        var w1: List[Int] = [a]
        out.append(w1^)
    for a in range(3):
        for b in range(3):
            var w2: List[Int] = [a, b]
            out.append(w2^)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                var w3: List[Int] = [a, b, c]
                out.append(w3^)
    return out^


def histogram_line(label: String, h: List[Int]) -> String:
    var line = label
    for d in range(len(h)):
        if h[d] > 0:
            line += " " + String(d) + ":" + String(h[d])
    return line


def main() raises:
    var words = image_words()
    var n_pip = 0
    var n_vertices = 0
    var n_nonproductive = 0
    var n_failed = 0
    var n_complex = 0
    var n_real = 0
    var max_m0 = 0
    var max_excess = 0
    var max_m0_complex = 0
    var max_excess_complex = 0
    var max_m0_real = 0
    var max_excess_real = 0
    var hist_m0 = List[Int]()
    var hist_excess = List[Int]()
    var hist_spec_excess = List[Int]()
    var hist_spec_m0 = List[Int]()
    for _ in range(128):
        hist_m0.append(0)
        hist_excess.append(0)
        hist_spec_excess.append(0)
        hist_spec_m0.append(0)

    for i in range(len(words)):
        for j in range(len(words)):
            for k in range(len(words)):
                var sigma = List[List[Int]]()
                sigma.append(words[i].copy())
                sigma.append(words[j].copy())
                sigma.append(words[k].copy())
                if not is_pip(Mat3(substitution_incidence(sigma))):
                    continue
                n_pip += 1
                try:
                    var tables = build_seed_overlap_tables(sigma)
                    var g = build_seed_overlap_graph_from_tables(tables, 20000)
                    if g.capped:
                        raise Error("seed-patch overlap graph capped")
                    if len(nonproductive_overlap_states(g)) > 0:
                        n_nonproductive += 1
                        print("NONPRODUCTIVE overlap specimen:", i, j, k)
                        continue
                    var left = first_left_aligned_depths(g)
                    var cb = ContractingBound(tables)
                    var cache = Dict[CubicElt, Int]()
                    var worst_e = 0
                    var worst_m = 0
                    for v in range(g.size()):
                        var t = g.states[v].shift
                        var m0: Int
                        if t in cache:
                            m0 = cache[t]
                        else:
                            m0 = cb.least_level(g, t)
                            cache[t] = m0
                        if m0 < 0 or m0 > left[v]:
                            raise Error("contracting bound exceeds the left-aligned depth")
                        if (m0 == 0) != t.is_zero():
                            raise Error("contracting bound vanishes off offset zero")
                        var e = left[v] - m0
                        if e >= len(hist_excess) or m0 >= len(hist_m0):
                            raise Error("histogram range exceeded")
                        hist_excess[e] = hist_excess[e] + 1
                        hist_m0[m0] = hist_m0[m0] + 1
                        if e > worst_e:
                            worst_e = e
                        if m0 > worst_m:
                            worst_m = m0
                        n_vertices += 1
                    hist_spec_excess[worst_e] = hist_spec_excess[worst_e] + 1
                    hist_spec_m0[worst_m] = hist_spec_m0[worst_m] + 1
                    if worst_e > max_excess:
                        max_excess = worst_e
                    if worst_m > max_m0:
                        max_m0 = worst_m
                    if cb.is_complex:
                        n_complex += 1
                        if worst_m > max_m0_complex:
                            max_m0_complex = worst_m
                        if worst_e > max_excess_complex:
                            max_excess_complex = worst_e
                    else:
                        n_real += 1
                        if worst_m > max_m0_real:
                            max_m0_real = worst_m
                        if worst_e > max_excess_real:
                            max_excess_real = worst_e
                except e:
                    n_failed += 1
                    print("FAILED specimen:", i, j, k, " ", e)
                if n_pip % 500 == 0:
                    print("progress:", n_pip)

    print("PIP specimens:", n_pip, " failed:", n_failed, " nonproductive:", n_nonproductive)
    print("vertices checked:", n_vertices)
    print("maximum contracting lower bound m0:", max_m0)
    print(histogram_line("vertices by contracting lower bound m0:", hist_m0))
    print("maximum excess b - m0:", max_excess)
    print(histogram_line("vertices by excess b - m0:", hist_excess))
    print(histogram_line("specimens by maximal excess:", hist_spec_excess))
    print(histogram_line("specimens by maximal m0:", hist_spec_m0))
    print("complex-pair specimens:", n_complex, " maximal m0:", max_m0_complex, " maximal excess:", max_excess_complex)
    print("real-conjugate specimens:", n_real, " maximal m0:", max_m0_real, " maximal excess:", max_excess_real)
