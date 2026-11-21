"""The nonunit rank-two residue over the PIP corpus.

For every nonunit member: which written exclusions of coincidence rank two
apply (Theorem E, Theorem H3, the fixed-tiling parity), and whether the member
survives all three. Survivors are asserted to have `ER = K_{2,2}` and even
trace and determinant (Theorem R(1)-(3) of
docs/c4-nonunit-rank-two-residue-2026-11-21.md). Class counts under written
conditional theorems. `nilpotent_mod_two` counts the survivors with `chi_M = t^3`
modulo two, the class Theorem R(4) keeps; every corpus member has pure discrete spectrum by other
means, so a survivor is not an open case.
"""

from psc.corpus import pip_corpus
from psc.twin_fixed_points import residue_profile


def main() raises:
    var corpus = pip_corpus()
    var nonunit = 0
    var theorem_e = 0
    var tree = 0
    var parity = 0
    var survivors = 0
    var nilpotent = 0
    for s in range(len(corpus)):
        var m = corpus[s].incidence.copy()
        var det = m.det()
        if det == 1 or det == -1:
            continue
        nonunit += 1
        var r = residue_profile(corpus[s].sigma)
        theorem_e += Int(r.theorem_e)
        tree += Int(r.tree)
        parity += Int(r.odd_power != 0)
        if r.survives():
            if not r.complete_bipartite() or m.trace() % 2 != 0 or det % 2 != 0:
                raise Error("Theorem R violated: " + corpus[s].label())
            survivors += 1
            var e2 = m.charpoly()[1]
            nilpotent += Int(e2 % 2 == 0)
            print("survivor:", corpus[s].label(), "sigma", corpus[s].sigma, "tr", m.trace(), "e2", e2, "det", det)
    print("nonunit:", nonunit)
    print("theorem_e:", theorem_e)
    print("tree:", tree)
    print("odd_fixed_count:", parity)
    print("survivors:", survivors)
    print("nilpotent_mod_two:", nilpotent)
