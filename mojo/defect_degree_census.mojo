"""Exact first scattered-subword defect census over the 4554 PIP corpus.

Every noncoincident balanced-pair state has K1=0. This census computes K2,
K3 and K4 with streaming exact integer recurrences and classifies the first
nonzero defect as degree 2, 3, 4, or >=5. Counts are separated into:

- every reachable noncoincident BPA state;
- recurrent noncoincident SCC states;
- states belonging to noncoincident sink SCCs.

The census is finite evidence only. It does not prove a degree bound for PIP
balanced-pair states and does not prove G1, C1, C4, or PSC.
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


def n4_stream(w: List[Int]) -> List[Int]:
    var seen: List[Int] = [0, 0, 0]
    var pref2 = List[Int]()
    var pref3 = List[Int]()
    var out = List[Int]()
    for _ in range(9):
        pref2.append(0)
    for _ in range(27):
        pref3.append(0)
    for _ in range(81):
        out.append(0)

    for pos in range(len(w)):
        var d = w[pos]
        for a in range(3):
            for b in range(3):
                for c in range(3):
                    out[27 * a + 9 * b + 3 * c + d] += pref3[9 * a + 3 * b + c]
        for a in range(3):
            for b in range(3):
                pref3[9 * a + 3 * b + d] += pref2[3 * a + b]
        for a in range(3):
            pref2[3 * a + d] += seen[a]
        seen[d] += 1
    return out^


def first_defect_degree(p: Pair) -> Int:
    """Return 2,3,4, or 5 where 5 means no defect through degree four."""
    if n2_stream(p.u) != n2_stream(p.v):
        return 2
    if n3_stream(p.u) != n3_stream(p.v):
        return 3
    if n4_stream(p.u) != n4_stream(p.v):
        return 4
    return 5


def increment(mut counts: List[Int], degree: Int):
    counts[degree] += 1


def print_counts(prefix: String, counts: List[Int]):
    print(prefix + " degree2: " + String(counts[2]))
    print(prefix + " degree3: " + String(counts[3]))
    print(prefix + " degree4: " + String(counts[4]))
    print(prefix + " degree5plus: " + String(counts[5]))


def main() raises:
    var words = image_words()
    var reachable_counts = List[Int]()
    var recurrent_counts = List[Int]()
    var sink_counts = List[Int]()
    for _ in range(6):
        reachable_counts.append(0)
        recurrent_counts.append(0)
        sink_counts.append(0)

    var n_pip = 0
    var n_capped = 0
    var total_noncoincident = 0
    var total_recurrent = 0
    var total_sink = 0
    var specimens_reachable_d4plus = 0
    var specimens_recurrent_d4plus = 0
    var specimens_sink_d4plus = 0
    var max_d4_length = 0
    var max_d5plus_length = 0
    var printed_d4_example = False
    var printed_d5_example = False

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
                    n_capped += 1
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

                    var noncoincident_exit = False
                    for si in range(len(comp)):
                        var state_index = comp[si]
                        for ei in range(len(automaton.adj[state_index])):
                            var child = automaton.adj[state_index][ei]
                            if not automaton.states[child].is_coincidence() and not contains_index(comp, child):
                                noncoincident_exit = True
                    if not noncoincident_exit:
                        for si in range(len(comp)):
                            sink_flag[comp[si]] = True

                var specimen_reachable_d4plus = False
                var specimen_recurrent_d4plus = False
                var specimen_sink_d4plus = False

                for state_index in range(automaton.size()):
                    ref p = automaton.states[state_index]
                    if p.is_coincidence():
                        continue

                    total_noncoincident += 1
                    var degree = first_defect_degree(p)
                    increment(reachable_counts, degree)

                    if degree >= 4:
                        specimen_reachable_d4plus = True
                    if degree == 4 and p.length() > max_d4_length:
                        max_d4_length = p.length()
                    if degree == 5 and p.length() > max_d5plus_length:
                        max_d5plus_length = p.length()

                    if degree == 4 and not printed_d4_example:
                        print(
                            "D4_EXAMPLE_JSON {\"i\":", i, ",\"j\":", j, ",\"k\":", k,
                            ",\"state\":\"", p.key(), "\",\"length\":", p.length(), "}"
                        )
                        printed_d4_example = True
                    if degree == 5 and not printed_d5_example:
                        print(
                            "D5PLUS_EXAMPLE_JSON {\"i\":", i, ",\"j\":", j, ",\"k\":", k,
                            ",\"state\":\"", p.key(), "\",\"length\":", p.length(), "}"
                        )
                        printed_d5_example = True

                    if recurrent_flag[state_index]:
                        total_recurrent += 1
                        increment(recurrent_counts, degree)
                        if degree >= 4:
                            specimen_recurrent_d4plus = True
                    if sink_flag[state_index]:
                        total_sink += 1
                        increment(sink_counts, degree)
                        if degree >= 4:
                            specimen_sink_d4plus = True

                if specimen_reachable_d4plus:
                    specimens_reachable_d4plus += 1
                if specimen_recurrent_d4plus:
                    specimens_recurrent_d4plus += 1
                if specimen_sink_d4plus:
                    specimens_sink_d4plus += 1

    print("C4 first-defect-degree census")
    print("PIP specimens:", n_pip, " capped:", n_capped)
    print("reachable noncoincident states:", total_noncoincident)
    print_counts("reachable", reachable_counts)
    print("recurrent noncoincident states:", total_recurrent)
    print_counts("recurrent", recurrent_counts)
    print("sink noncoincident states:", total_sink)
    print_counts("sink", sink_counts)
    print("PIP with reachable degree4plus state:", specimens_reachable_d4plus)
    print("PIP with recurrent degree4plus state:", specimens_recurrent_d4plus)
    print("PIP with sink degree4plus state:", specimens_sink_d4plus)
    print("maximum degree4 state length:", max_d4_length)
    print("maximum degree5plus state length:", max_d5plus_length)
