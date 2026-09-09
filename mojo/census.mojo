"""Exhaustive census of primitive irreducible Pisot substitutions on {1,2,3}
with images of length at most 3.

For each PIP specimen it builds `B_sigma` and reports:
  * termination of the construction within the state cap  (hypothesis G1, in scope);
  * productivity: every reachable balanced pair reaches a coincidence
    (the SCC Producer conjecture, in scope).

Neither is a proof. A clean sweep is elimination of counterexamples over a
finite corpus; G1 and SCC Producer both remain open for alphabet 3.
"""

from psc.bpa import build, nonproductive_states, substitution_incidence
from psc.mat3 import Mat3
from psc.pisot import is_pip


def image_words() -> List[List[Int]]:
    """Every word over {0,1,2} of length 1, 2 or 3."""
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
    var n_terminated = 0
    var n_capped = 0
    var n_productive = 0
    var n_nonproductive = 0
    var max_size = 0

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
                    continue
                n_terminated += 1
                if a.size() > max_size:
                    max_size = a.size()
                if len(nonproductive_states(a)) == 0:
                    n_productive += 1
                else:
                    n_nonproductive += 1
                    print("NON-PRODUCTIVE specimen:", i, j, k)

    print("PIP specimens (images of length <= 3):", n_pip)
    print("  B_sigma construction terminated:", n_terminated, " capped:", n_capped)
    print("  largest |B_sigma|:", max_size)
    print("  productive:", n_productive, "  non-productive:", n_nonproductive)
