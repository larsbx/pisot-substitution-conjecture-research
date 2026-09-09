"""Exact C4-B calibration over the established alphabet-3 PIP corpus.

For every primitive irreducible Pisot substitution with image lengths <= 3,
classify the prefix/suffix endpoint maps into the seven C4-A types A..G. Then
inspect every recurrent noncoincident SCC and isolate noncoincident sink SCCs:
SCCs with no noncoincident child outside the component. A productive sink SCC
may still have a direct coincidence child; a hypothetical nonproductive sink
counterexample would not.

The output is finite evidence only. It does not prove C4, C1, G1, or PSC.
"""

from psc.bpa import build, recurrent_noncoincident_sccs, substitution_incidence, inherited_sync_positions, newborn_sync_positions
from psc.endpoint_core import endpoint_type, endpoint_type_name, prefix_endpoint_map, suffix_endpoint_map
from psc.mat3 import Mat3
from psc.pisot import is_pip


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


def main() raises:
    var words = image_words()
    var pip_pair_counts = List[Int]()
    var sink_pair_counts = List[Int]()
    for _ in range(49):
        pip_pair_counts.append(0)
        sink_pair_counts.append(0)

    var n_pip = 0
    var n_capped = 0
    var n_recurrent = 0
    var n_sink = 0
    var n_sink_direct_coincidence = 0
    var n_sink_no_direct_coincidence = 0
    var n_sink_newborn = 0
    var n_sink_inherited = 0
    var n_sink_any_sync = 0
    var n_sink_no_sync = 0

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

                var plus_type = endpoint_type(prefix_endpoint_map(sigma))
                var minus_type = endpoint_type(suffix_endpoint_map(sigma))
                pip_pair_counts[7 * plus_type + minus_type] += 1

                var a = build(sigma, 20000)
                if a.capped:
                    n_capped += 1
                    continue

                var comps = recurrent_noncoincident_sccs(a)
                for ci in range(len(comps)):
                    ref comp = comps[ci]
                    n_recurrent += 1
                    var noncoincident_exit = False
                    var direct_coincidence = False
                    var has_newborn = False
                    var has_inherited = False

                    for si in range(len(comp)):
                        var state_index = comp[si]
                        ref p = a.states[state_index]
                        if len(newborn_sync_positions(sigma, p)) > 0:
                            has_newborn = True
                        if len(inherited_sync_positions(sigma, p)) > 0:
                            has_inherited = True

                        for ei in range(len(a.adj[state_index])):
                            var child = a.adj[state_index][ei]
                            if a.states[child].is_coincidence():
                                direct_coincidence = True
                            elif not contains_index(comp, child):
                                noncoincident_exit = True

                    if noncoincident_exit:
                        continue

                    n_sink += 1
                    sink_pair_counts[7 * plus_type + minus_type] += 1
                    if direct_coincidence:
                        n_sink_direct_coincidence += 1
                    else:
                        n_sink_no_direct_coincidence += 1
                        print(
                            "SINK_NO_DIRECT_JSON {\"i\":", i,
                            ",\"j\":", j, ",\"k\":", k,
                            ",\"scc\":", ci, ",\"size\":", len(comp),
                            ",\"plus\":\"", endpoint_type_name(plus_type),
                            "\",\"minus\":\"", endpoint_type_name(minus_type), "\"}"
                        )

                    if has_newborn:
                        n_sink_newborn += 1
                    if has_inherited:
                        n_sink_inherited += 1
                    if has_newborn or has_inherited:
                        n_sink_any_sync += 1
                    else:
                        n_sink_no_sync += 1
                        print(
                            "SINK_NO_SYNC_JSON {\"i\":", i,
                            ",\"j\":", j, ",\"k\":", k,
                            ",\"scc\":", ci, ",\"size\":", len(comp),
                            ",\"plus\":\"", endpoint_type_name(plus_type),
                            "\",\"minus\":\"", endpoint_type_name(minus_type), "\"}"
                        )

    print("C4 endpoint-type sink-SCC census")
    print("PIP specimens:", n_pip, " capped:", n_capped)
    print("recurrent noncoincident SCCs:", n_recurrent)
    print("noncoincident sink SCCs:", n_sink)
    print("sink SCCs with direct coincidence child:", n_sink_direct_coincidence)
    print("sink SCCs without direct coincidence child:", n_sink_no_direct_coincidence)
    print("sink SCCs with newborn synchronization:", n_sink_newborn)
    print("sink SCCs with inherited synchronization:", n_sink_inherited)
    print("sink SCCs with any boundary synchronization:", n_sink_any_sync)
    print("sink SCCs with no boundary synchronization:", n_sink_no_sync)

    for plus_type in range(7):
        for minus_type in range(7):
            var idx = 7 * plus_type + minus_type
            if pip_pair_counts[idx] > 0:
                print(
                    "PIP_TYPE_PAIR " + endpoint_type_name(plus_type) + " " +
                    endpoint_type_name(minus_type) + " " + String(pip_pair_counts[idx])
                )
            if sink_pair_counts[idx] > 0:
                print(
                    "SINK_TYPE_PAIR " + endpoint_type_name(plus_type) + " " +
                    endpoint_type_name(minus_type) + " " + String(sink_pair_counts[idx])
                )
