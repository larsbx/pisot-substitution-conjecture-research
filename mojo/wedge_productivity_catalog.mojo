"""Exact bounded-corpus certificate for the K2-nonzero wedge-productivity case.

For every primitive irreducible Pisot substitution on three letters with
nonempty images of length at most three, this driver inspects every recurrent
noncoincident SCC.  A closed nonproductive SCC with nonzero K2 is emitted as a
replayable exact countermodel before the zero-survivor assertion can fail.
This is a finite-domain certificate, not a proof of general wedge productivity.
"""

from psc.bpa import Automaton, build, recurrent_noncoincident_sccs, substitution_incidence
from psc.mat3 import Mat3
from psc.pisot import is_pip
from psc.words import is_zero


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


def contains_index(comp: List[Int], x: Int) -> Bool:
    for i in range(len(comp)):
        if comp[i] == x:
            return True
    return False


def is_closed_nonproductive(automaton: Automaton, comp: List[Int]) -> Bool:
    """Exact strict-carrier condition on a recurrent noncoincident SCC."""
    for si in range(len(comp)):
        var state_index = comp[si]
        for ei in range(len(automaton.adj[state_index])):
            var child = automaton.adj[state_index][ei]
            if automaton.states[child].is_coincidence():
                return False
            if not contains_index(comp, child):
                return False
    return True


def has_nonzero_k2(automaton: Automaton, comp: List[Int]) -> Bool:
    for si in range(len(comp)):
        if not is_zero(automaton.states[comp[si]].k2()):
            return True
    return False


def emit_countermodel(
    sigma_i: Int,
    sigma_j: Int,
    sigma_k: Int,
    comp_id: Int,
    automaton: Automaton,
    comp: List[Int],
):
    """Emit enough exact data to reconstruct and independently replay a survivor."""
    print(
        "D2_COUNTERMODEL_BEGIN {\"i\":", sigma_i, ",\"j\":", sigma_j,
        ",\"k\":", sigma_k, ",\"component\":", comp_id,
        ",\"size\":", len(comp), "}"
    )
    for si in range(len(comp)):
        var state_index = comp[si]
        print("D2_COUNTERMODEL_STATE ", state_index, " ", automaton.states[state_index].key())
        for ei in range(len(automaton.adj[state_index])):
            print("D2_COUNTERMODEL_EDGE ", state_index, " ", automaton.adj[state_index][ei])
    print("D2_COUNTERMODEL_END")


def main() raises:
    var words = image_words()
    var n_pip = 0
    var n_recurrent_components = 0
    var n_closed_nonproductive = 0
    var n_strict_degree2 = 0

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

                var automaton = build(sigma, 20000)
                if automaton.capped:
                    print("WEDGE_INCONCLUSIVE_CAPPED", i, j, k)
                    raise Error("wedge-productivity catalogue is incomplete: state cap reached")

                var comps = recurrent_noncoincident_sccs(automaton)
                n_recurrent_components += len(comps)
                for ci in range(len(comps)):
                    ref comp = comps[ci]
                    if not is_closed_nonproductive(automaton, comp):
                        continue
                    n_closed_nonproductive += 1
                    if has_nonzero_k2(automaton, comp):
                        n_strict_degree2 += 1
                        emit_countermodel(i, j, k, ci, automaton, comp)

    print("bounded K2-nonzero wedge-productivity catalogue")
    print("PIP specimens:", n_pip)
    print("recurrent noncoincident components:", n_recurrent_components)
    print("closed nonproductive components:", n_closed_nonproductive)
    print("strict K2-nonzero components:", n_strict_degree2)
