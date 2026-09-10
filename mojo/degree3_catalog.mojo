"""Exact catalogue of reachable K2-zero / K3-nonzero BPA states in the 4554 PIP corpus.

This is a focused companion to defect_degree_census.mojo.  It prints every
reachable noncoincident state whose first scattered-subword defect is degree 3,
with substitution indices and recurrent/sink flags.  Finite evidence only.
"""

from psc.bpa import build, recurrent_noncoincident_sccs, substitution_incidence
from psc.mat3 import Mat3
from psc.pisot import is_pip
from psc.words import Pair


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


def n2_stream(w: List[Int]) -> List[Int]:
    var seen: List[Int] = [0, 0, 0]
    var out = List[Int]()
    for _ in range(9):
        out.append(0)
    for pos in range(len(w)):
        var b = w[pos]
        for a in range(3):
            out[3 * a + b] += seen[a]
        seen[b] += 1
    return out^


def n3_stream(w: List[Int]) -> List[Int]:
    var seen: List[Int] = [0, 0, 0]
    var pref2 = List[Int]()
    var out = List[Int]()
    for _ in range(9):
        pref2.append(0)
    for _ in range(27):
        out.append(0)
    for pos in range(len(w)):
        var c = w[pos]
        for a in range(3):
            for b in range(3):
                out[9 * a + 3 * b + c] += pref2[3 * a + b]
        for a in range(3):
            pref2[3 * a + c] += seen[a]
        seen[c] += 1
    return out^


def is_degree3(p: Pair) -> Bool:
    return n2_stream(p.u) == n2_stream(p.v) and n3_stream(p.u) != n3_stream(p.v)


def main() raises:
    var words = image_words()
    var n_pip = 0
    var n_degree3 = 0
    var n_degree3_recurrent = 0
    var n_degree3_sink = 0
    var n_specimens = 0
    var max_length = 0

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
                    print(
                        "D3_STATE_JSON {\"i\":", i, ",\"j\":", j, ",\"k\":", k,
                        ",\"state\":\"", p.key(), "\",\"length\":", p.length(),
                        ",\"recurrent\":", 1 if recurrent_flag[state_index] else 0,
                        ",\"sink\":", 1 if sink_flag[state_index] else 0, "}"
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
