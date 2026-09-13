"""Exact catalogue of reachable K2-zero / K3-nonzero BPA states in the 4554 PIP corpus.

This is a focused companion to defect_degree_census.mojo.  It prints every
reachable noncoincident state whose first scattered-subword defect is degree 3,
with substitution indices and recurrent/sink flags.  Finite evidence only.
"""

from psc.bpa import Automaton, build, recurrent_noncoincident_sccs, substitution_incidence
from psc.mat3 import Mat3
from psc.pisot import is_pip
from psc.tensor3 import theta
from psc.words import Pair, is_zero


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


def is_degree3(p: Pair) -> Bool:
    return is_zero(p.k2()) and not is_zero(p.k3())


def has_coincidence_child(automaton: Automaton, state_index: Int) -> Bool:
    for ei in range(len(automaton.adj[state_index])):
        if automaton.states[automaton.adj[state_index][ei]].is_coincidence():
            return True
    return False


def productive_within_two(automaton: Automaton, state_index: Int) -> Bool:
    if has_coincidence_child(automaton, state_index):
        return True
    for ei in range(len(automaton.adj[state_index])):
        var child = automaton.adj[state_index][ei]
        if has_coincidence_child(automaton, child):
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


def is_first_degree3_component(automaton: Automaton, comp: List[Int]) -> Bool:
    var has_k3 = False
    for si in range(len(comp)):
        ref p = automaton.states[comp[si]]
        if not is_zero(p.k2()):
            return False
        if not is_zero(p.k3()):
            has_k3 = True
    return has_k3


def emit_countermodel(
    sigma_i: Int,
    sigma_j: Int,
    sigma_k: Int,
    comp_id: Int,
    automaton: Automaton,
    comp: List[Int],
):
    """Replayable exact record; emitted before the summary can fail closed."""
    print(
        "D3_COUNTERMODEL_BEGIN {\"i\":", sigma_i, ",\"j\":", sigma_j,
        ",\"k\":", sigma_k, ",\"component\":", comp_id,
        ",\"size\":", len(comp), "}"
    )
    for si in range(len(comp)):
        var state_index = comp[si]
        print("D3_COUNTERMODEL_STATE ", state_index, " ", automaton.states[state_index].key())
        for ei in range(len(automaton.adj[state_index])):
            print("D3_COUNTERMODEL_EDGE ", state_index, " ", automaton.adj[state_index][ei])
    print("D3_COUNTERMODEL_END")


def main() raises:
    var words = image_words()
    var n_pip = 0
    var n_degree3 = 0
    var n_degree3_recurrent = 0
    var n_degree3_sink = 0
    var n_specimens = 0
    var max_length = 0
    var n_noncentralizer = 0
    var n_productive_within_two = 0
    var n_strict_degree3_components = 0

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
                    print("INCONCLUSIVE_CAPPED", i, j, k)
                    continue

                var recurrent_flag = List[Bool]()
                var sink_flag = List[Bool]()
                for _ in range(automaton.size()):
                    recurrent_flag.append(False)
                    sink_flag.append(False)

                var comps = recurrent_noncoincident_sccs(automaton)
                for ci in range(len(comps)):
                    ref comp = comps[ci]
                    for si in range(len(comp)):
                        recurrent_flag[comp[si]] = True
                    var has_exit = False
                    for si in range(len(comp)):
                        var state_index = comp[si]
                        for ei in range(len(automaton.adj[state_index])):
                            var child = automaton.adj[state_index][ei]
                            if not automaton.states[child].is_coincidence() and not contains_index(comp, child):
                                has_exit = True
                    if not has_exit:
                        for si in range(len(comp)):
                            sink_flag[comp[si]] = True
                    if is_closed_nonproductive(automaton, comp) and is_first_degree3_component(automaton, comp):
                        n_strict_degree3_components += 1
                        emit_countermodel(i, j, k, ci, automaton, comp)

                var specimen_has_degree3 = False
                for state_index in range(automaton.size()):
                    ref p = automaton.states[state_index]
                    if p.is_coincidence() or not is_degree3(p):
                        continue
                    specimen_has_degree3 = True
                    n_degree3 += 1
                    if recurrent_flag[state_index]:
                        n_degree3_recurrent += 1
                    if sink_flag[state_index]:
                        n_degree3_sink += 1
                    if p.length() > max_length:
                        max_length = p.length()
                    var m = Mat3(substitution_incidence(sigma))
                    var a = theta(p.k3())
                    var centralizer = m * a == a * m
                    if not centralizer:
                        n_noncentralizer += 1
                    var productive2 = productive_within_two(automaton, state_index)
                    if productive2:
                        n_productive_within_two += 1
                    print(
                        "D3_STATE_JSON {\"i\":", i, ",\"j\":", j, ",\"k\":", k,
                        ",\"state\":\"", p.key(), "\",\"length\":", p.length(),
                        ",\"recurrent\":", 1 if recurrent_flag[state_index] else 0,
                        ",\"sink\":", 1 if sink_flag[state_index] else 0,
                        ",\"centralizer\":", 1 if centralizer else 0,
                        ",\"productive_within_two\":", 1 if productive2 else 0, "}"
                    )
                if specimen_has_degree3:
                    n_specimens += 1

    print("C4 degree-3 state catalogue")
    print("PIP specimens:", n_pip)
    print("PIP specimens with degree3 state:", n_specimens)
    print("degree3 states:", n_degree3)
    print("degree3 recurrent states:", n_degree3_recurrent)
    print("degree3 sink states:", n_degree3_sink)
    print("maximum degree3 state length:", max_length)
    print("degree3 noncentralizer states:", n_noncentralizer)
    print("degree3 productive within two:", n_productive_within_two)
    print("strict first-degree3 components:", n_strict_degree3_components)
