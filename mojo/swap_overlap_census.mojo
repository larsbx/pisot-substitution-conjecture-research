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
from psc.overlap_seed_patch import build_seed_overlap_graph, nonproductive_overlap_states


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
    var largest = 0
    var total_states = 0

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
                    var g = build_seed_overlap_graph(sigma, 20000)
                    if g.capped:
                        n_capped += 1
                        print("CAPPED specimen:", i, j, k)
                        continue
                    n_built += 1
                    total_states += g.size()
                    if g.size() > largest:
                        largest = g.size()
                    var bad = len(nonproductive_overlap_states(g))
                    if bad > 0:
                        n_nonproductive_specimens += 1
                        n_nonproductive_states += bad
                        print("NONPRODUCTIVE overlap specimen:", i, j, k, " states:", bad)
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
