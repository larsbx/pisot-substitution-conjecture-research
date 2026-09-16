"""Exhaustive census of primitive irreducible Pisot substitutions on {1,2,3}
with images of length at most 3.

For each PIP specimen it builds `B_sigma` and reports:
  * termination of the construction within the state cap  (hypothesis G1, in scope);
  * productivity: every reachable balanced pair reaches a coincidence
    (the SCC Producer conjecture, in scope).

Neither is a proof. A clean sweep is elimination of counterexamples over a
finite corpus; G1 and SCC Producer both remain open for alphabet 3.
"""

from psc.bpa import build, nonproductive_states
from psc.corpus import STATE_CAP, pip_corpus
from psc.histogram import max_int


def main() raises:
    var corpus = pip_corpus()
    var n_terminated = 0
    var n_capped = 0
    var n_productive = 0
    var n_nonproductive = 0
    var max_size = 0

    for s in range(len(corpus)):
        ref spec = corpus[s]
        var a = build(spec.sigma, STATE_CAP)
        if a.capped:
            n_capped += 1
            continue
        n_terminated += 1
        max_size = max_int(max_size, a.size())
        if len(nonproductive_states(a)) == 0:
            n_productive += 1
        else:
            n_nonproductive += 1
            print("NON-PRODUCTIVE specimen:", spec.label())

    print("PIP specimens (images of length <= 3):", len(corpus))
    print("  B_sigma construction terminated:", n_terminated, " capped:", n_capped)
    print("  largest |B_sigma|:", max_size)
    print("  productive:", n_productive, "  non-productive:", n_nonproductive)
