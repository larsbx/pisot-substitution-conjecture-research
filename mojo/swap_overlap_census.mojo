"""Exact census of the seed-patch overlap graphs over the alphabet-3 PIP corpus.

For every primitive irreducible Pisot substitution on {0,1,2} with images of
length at most 3 (exact Sturm-sequence screening), builds the seed-patch
overlap graph of `psc.overlap_seed_patch` from the three swap seeds under a
cap of 20000 states and reports sizes and productivity.  The finiteness of
this graph is a theorem (docs/overlap-finiteness-and-coincidence-density-
2026-09-13.md); the cap is retained only as a fail-closed guard.  Overlap
productivity for every reachable overlap is the open Level-3 statement in its
G1-free form; a clean corpus is finite evidence only.
"""

from psc.bpa import substitution_incidence
from psc.mat3 import Mat3
from psc.pisot import is_pip
from psc.overlap_recurrence import zero_shift_free_recurrent_sccs
from psc.overlap_seed_patch import (
    build_seed_overlap_graph_from_tables,
    build_seed_overlap_tables,
    first_coincidence_depths,
    first_left_aligned_depths,
    nonproductive_overlap_states,
    strong_coincidence_depth_from,
)


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


def main() raises:
    var words = image_words()
    var n_pip = 0
    var n_built = 0
    var n_capped = 0
    var n_failed = 0
    var n_nonproductive_states = 0
    var n_nonproductive_specimens = 0
    var n_zero_shift_free_cycle_specimens = 0
    var n_zero_shift_free_cycle_sccs = 0
    var max_zero_shift_free_cycle_size = 0
    var largest = 0
    var total_states = 0
    var max_depth = 0
    var depth_histogram = List[Int]()
    var max_left = 0
    var left_histogram = List[Int]()
    var max_prefix_scc = 0
    var max_suffix_scc = 0
    var prefix_scc_histogram = List[Int]()
    var suffix_scc_histogram = List[Int]()
    for _ in range(128):
        depth_histogram.append(0)
        left_histogram.append(0)
        prefix_scc_histogram.append(0)
        suffix_scc_histogram.append(0)

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
                        n_capped += 1
                        print("CAPPED specimen:", i, j, k)
                        continue
                    n_built += 1
                    total_states += g.size()
                    if g.size() > largest:
                        largest = g.size()

                    # Necessary finite signature of the strict left-boundary
                    # zipper branch: after deleting coincidences and all
                    # offset-zero states, does any directed recurrence remain?
                    # Right-aligned states are intentionally retained here.
                    var zipper_sccs = zero_shift_free_recurrent_sccs(g)
                    if len(zipper_sccs) > 0:
                        n_zero_shift_free_cycle_specimens += 1
                        n_zero_shift_free_cycle_sccs += len(zipper_sccs)
                        for z in range(len(zipper_sccs)):
                            if len(zipper_sccs[z]) > max_zero_shift_free_cycle_size:
                                max_zero_shift_free_cycle_size = len(zipper_sccs[z])

                    var bad = len(nonproductive_overlap_states(g))
                    if bad > 0:
                        # A nonproductive graph is the mathematical event this
                        # census exists to detect; record it before any depth
                        # statistic, which is undefined on such a graph.
                        n_nonproductive_specimens += 1
                        n_nonproductive_states += bad
                        print("NONPRODUCTIVE overlap specimen:", i, j, k, " states:", bad)
                        continue
                    var depths = first_coincidence_depths(g)
                    var worst = 0
                    for d in range(len(depths)):
                        if depths[d] > worst:
                            worst = depths[d]
                    if worst >= len(depth_histogram):
                        raise Error("first-coincidence depth exceeds histogram range")
                    depth_histogram[worst] = depth_histogram[worst] + 1
                    if worst > max_depth:
                        max_depth = worst
                    var left = first_left_aligned_depths(g)
                    var worst_left = 0
                    for d in range(len(left)):
                        if left[d] < 0 or left[d] > depths[d]:
                            raise Error("left-aligned depth must be defined and at most the coincidence depth")
                        if left[d] > worst_left:
                            worst_left = left[d]
                    if worst_left >= len(left_histogram):
                        raise Error("first left-aligned depth exceeds histogram range")
                    left_histogram[worst_left] = left_histogram[worst_left] + 1
                    if worst_left > max_left:
                        max_left = worst_left
                    var prefix_scc = strong_coincidence_depth_from(depths, g, tables, False)
                    var suffix_scc = strong_coincidence_depth_from(depths, g, tables, True)
                    if prefix_scc < 0 or suffix_scc < 0:
                        raise Error("endpoint-aligned overlap without coincidence on a productive graph")
                    for d in range(len(depths)):
                        if depths[d] > left[d] + prefix_scc:
                            raise Error("coincidence depth exceeds left-aligned depth plus prefix strong-coincidence depth")
                    if prefix_scc >= len(prefix_scc_histogram) or suffix_scc >= len(suffix_scc_histogram):
                        raise Error("strong-coincidence depth exceeds histogram range")
                    prefix_scc_histogram[prefix_scc] = prefix_scc_histogram[prefix_scc] + 1
                    suffix_scc_histogram[suffix_scc] = suffix_scc_histogram[suffix_scc] + 1
                    if prefix_scc > max_prefix_scc:
                        max_prefix_scc = prefix_scc
                    if suffix_scc > max_suffix_scc:
                        max_suffix_scc = suffix_scc
                except e:
                    n_failed += 1
                    print("FAILED specimen:", i, j, k, " ", e)
                if n_pip % 500 == 0:
                    print("progress:", n_pip)

    print("PIP specimens:", n_pip)
    print("overlap graphs built:", n_built, " capped:", n_capped, " failed:", n_failed)
    print("largest seed-patch overlap graph:", largest)
    print("total seed-patch overlap states:", total_states)
    print("nonproductive overlap specimens:", n_nonproductive_specimens, " states:", n_nonproductive_states)
    print(
        "zero-shift-free recurrent overlap cycles: specimens:",
        n_zero_shift_free_cycle_specimens,
        " sccs:",
        n_zero_shift_free_cycle_sccs,
        " largest-scc:",
        max_zero_shift_free_cycle_size,
    )
    print("maximum first-coincidence depth:", max_depth)
    var line = String("specimens by maximal first-coincidence depth:")
    for d in range(len(depth_histogram)):
        if depth_histogram[d] > 0:
            line += " " + String(d) + ":" + String(depth_histogram[d])
    print(line)
    print("maximum first left-aligned depth:", max_left)
    var left_line = String("specimens by maximal first left-aligned depth:")
    for d in range(len(left_histogram)):
        if left_histogram[d] > 0:
            left_line += " " + String(d) + ":" + String(left_histogram[d])
    print(left_line)
    print("maximum prefix strong-coincidence depth:", max_prefix_scc)
    var prefix_line = String("specimens by prefix strong-coincidence depth:")
    for d in range(len(prefix_scc_histogram)):
        if prefix_scc_histogram[d] > 0:
            prefix_line += " " + String(d) + ":" + String(prefix_scc_histogram[d])
    print(prefix_line)
    print("maximum suffix strong-coincidence depth:", max_suffix_scc)
    var suffix_line = String("specimens by suffix strong-coincidence depth:")
    for d in range(len(suffix_scc_histogram)):
        if suffix_scc_histogram[d] > 0:
            suffix_line += " " + String(d) + ":" + String(suffix_scc_histogram[d])
    print(suffix_line)
