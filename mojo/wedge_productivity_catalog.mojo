"""Exact bounded-corpus certificate for the K2-nonzero wedge-productivity case.

For every primitive irreducible Pisot substitution on three letters with
nonempty images of length at most three, this driver inspects every recurrent
noncoincident SCC.  A closed nonproductive SCC with nonzero K2 is emitted as a
replayable exact countermodel before the zero-survivor assertion can fail.
This is a finite-domain certificate, not a proof of general wedge productivity.
"""

from psc.bpa import Automaton, build, recurrent_noncoincident_sccs, substitution_incidence
from finite_linear_algebra.mat3 import Mat3
from psc.pisot import is_pip
from psc.words import ALPHABET, Pair, is_zero, k2


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
        if not is_zero(k2(automaton.states[comp[si]])):
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


def run_predicate_calibration() raises:
    """Positive strict-carrier control plus a negative leaking control."""
    # One-based 1->2, 2->123, 3->2. This substitution is primitive but not
    # Pisot and has a known reachable two-state strict component.
    var strict_sigma = List[List[Int]]()
    var strict_0: List[Int] = [1]
    var strict_1: List[Int] = [0, 1, 2]
    var strict_2: List[Int] = [1]
    strict_sigma.append(strict_0^)
    strict_sigma.append(strict_1^)
    strict_sigma.append(strict_2^)
    var strict_automaton = build(strict_sigma, 20000)
    if strict_automaton.capped:
        raise Error("strict calibration unexpectedly reached the state cap")

    var detected_strict = False
    var strict_comps = recurrent_noncoincident_sccs(strict_automaton)
    for ci in range(len(strict_comps)):
        ref comp = strict_comps[ci]
        if (
            len(comp) == 2
            and is_closed_nonproductive(strict_automaton, comp)
            and has_nonzero_k2(strict_automaton, comp)
        ):
            detected_strict = True
    if not detected_strict:
        raise Error("strict K2-nonzero calibration component was not detected")

    # Directly calibrate rejection of a noncoincident K2-nonzero carrier
    # candidate that produces a coincidence child.
    var leaking_states = List[Pair]()
    var source_u: List[Int] = [0, 1]
    var source_v: List[Int] = [1, 0]
    leaking_states.append(Pair(source_u^, source_v^))
    var coincidence_u: List[Int] = [0]
    var coincidence_v: List[Int] = [0]
    leaking_states.append(Pair(coincidence_u^, coincidence_v^))
    var leaking_adj = List[List[Int]]()
    var source_edges: List[Int] = [0, 1]
    var coincidence_edges = List[Int]()
    leaking_adj.append(source_edges^)
    leaking_adj.append(coincidence_edges^)
    var leaking_automaton = Automaton(leaking_states, leaking_adj, False, ALPHABET)
    var leaking_comp: List[Int] = [0]
    if not has_nonzero_k2(leaking_automaton, leaking_comp):
        raise Error("leaking K2-nonzero calibration lost its wedge defect")
    if is_closed_nonproductive(leaking_automaton, leaking_comp):
        raise Error("coincidence-producing calibration was misclassified as strict")

    print("CALIBRATION strict K2-nonzero component detected: 1")
    print("CALIBRATION coincidence-producing component rejected: 1")


def main() raises:
    run_predicate_calibration()
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
