"""Exact swap-discrepancy census over the alphabet-3 PIP corpus.

For every primitive irreducible Pisot substitution on {0,1,2} with images of
length at most 3 (exact Sturm-sequence screening), builds `B_sigma` from the
three swap seeds under a cap of 20000 states and reports the maximum
discrepancy and the longest reachable state.  Finite evidence only: the
bounded-discrepancy theorem is proved in
docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md and no
computation verifies its constant `D_sigma`.
"""

from psc.bpa import build, substitution_incidence
from psc.mat3 import Mat3
from psc.pisot import is_pip
from psc.swap_discrepancy import max_reachable_discrepancy, max_state_length


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
    var n_capped = 0
    var overall = 0
    var longest = 0
    var histogram = List[Int]()
    for _ in range(64):
        histogram.append(0)

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
                var a = build(sigma, 20000)
                if a.capped:
                    n_capped += 1
                    print("CAPPED specimen:", i, j, k)
                    continue
                var d = max_reachable_discrepancy(a)
                var n = max_state_length(a)
                if d >= len(histogram):
                    raise Error("discrepancy exceeds histogram range")
                histogram[d] = histogram[d] + 1
                if d > overall:
                    overall = d
                if n > longest:
                    longest = n

    print("PIP specimens:", n_pip, " capped:", n_capped)
    print("maximum reachable discrepancy:", overall)
    print("longest reachable state:", longest)
    var line = String("discrepancy histogram:")
    for d in range(len(histogram)):
        if histogram[d] > 0:
            line += " " + String(d) + ":" + String(histogram[d])
    print(line)
