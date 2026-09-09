"""Exact one-step census for the C3 newborn-boundary mechanism.

Corpus: every primitive irreducible Pisot substitution on {0,1,2} whose three
images have length 1, 2 or 3, i.e. the same 4554-specimen corpus as census.mojo.

Why one step is the right finite unit. Decompose any balanced pair P at all of
its zero-return cuts into irreducible blocks t_j. Under one more inflation, the
images of the old cuts are exactly the inherited cuts. Therefore every newborn
cut of sigma(P) lies strictly between two consecutive inherited cuts, hence
inside sigma(t_j), and is a one-step newborn cut of that irreducible block.

Consequently, in the counterexample regime relevant to C1 -- a closed,
nonproductive recurrent SCC -- any higher-inflation newborn escape must already
appear as a one-step newborn escape from some state of that SCC. This program
therefore scans every state of every recurrent noncoincident SCC once, instead
of inflating whole pairs exponentially.

For SCCs with no boundary-synchronization witness of either lineage, the census
also distinguishes a direct coincidence sibling, a noncoincident escape edge,
and a genuinely closed/no-direct-coincidence obstruction candidate. Only the
last class is relevant to the closed-nonproductive counterexample regime.

The scan is finite evidence and a diagnostic for the locality reduction. It is
not a proof of G1, C1, C2, C3, or PSC.
"""

from psc.bpa import build, recurrent_noncoincident_sccs, substitution_incidence, inherited_sync_positions, newborn_sync_positions
from psc.mat3 import Mat3
from psc.pisot import is_pip


def image_words() -> List[List[Int]]:
    """Every word over {0,1,2} of length 1, 2 or 3, in deterministic order."""
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


def contains_int(xs: List[Int], x: Int) -> Bool:
    for i in range(len(xs)):
        if xs[i] == x:
            return True
    return False


def main() raises:
    var words = image_words()
    var n_pip = 0
    var n_capped = 0
    var n_scc = 0
    var n_states = 0

    var scc_with_newborn = 0
    var scc_without_newborn = 0
    var scc_with_inherited = 0
    var scc_with_both = 0
    var scc_with_neither = 0
    var scc_with_clean_newborn = 0

    var states_with_newborn = 0
    var states_with_inherited = 0
    var states_with_clean_newborn = 0

    # Audit the no-synchronization residual class.
    var no_sync_singleton = 0
    var no_sync_with_direct_coincidence = 0
    var no_sync_with_noncoincident_exit = 0
    var no_sync_closed_candidate = 0

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
                    print(
                        "CAPPED_JSON {\"type\":\"capped\",\"i\":",
                        i, ",\"j\":", j, ",\"k\":", k, "}"
                    )
                    continue

                var comps = recurrent_noncoincident_sccs(a)
                for ci in range(len(comps)):
                    ref comp = comps[ci]
                    n_scc += 1
                    n_states += len(comp)

                    var has_newborn = False
                    var has_inherited = False
                    var has_clean_newborn = False

                    for si in range(len(comp)):
                        ref p = a.states[comp[si]]
                        var inherited_hits = inherited_sync_positions(sigma, p)
                        var newborn_hits = newborn_sync_positions(sigma, p)

                        if len(inherited_hits) > 0:
                            has_inherited = True
                            states_with_inherited += 1
                        if len(newborn_hits) > 0:
                            has_newborn = True
                            states_with_newborn += 1
                        if len(inherited_hits) == 0 and len(newborn_hits) > 0:
                            has_clean_newborn = True
                            states_with_clean_newborn += 1

                    if has_newborn:
                        scc_with_newborn += 1
                    else:
                        scc_without_newborn += 1
                        print(
                            "NO_NEWBORN_JSON {\"type\":\"no_newborn\",\"i\":",
                            i, ",\"j\":", j, ",\"k\":", k,
                            ",\"scc\":", ci, ",\"size\":", len(comp), "}"
                        )

                    if has_inherited:
                        scc_with_inherited += 1
                    if has_newborn and has_inherited:
                        scc_with_both += 1
                    if not has_newborn and not has_inherited:
                        scc_with_neither += 1

                        var has_direct_coincidence = False
                        var has_noncoincident_exit = False
                        for si in range(len(comp)):
                            var v = comp[si]
                            for ei in range(len(a.adj[v])):
                                var w = a.adj[v][ei]
                                if a.states[w].is_coincidence():
                                    has_direct_coincidence = True
                                elif not contains_int(comp, w):
                                    has_noncoincident_exit = True

                        if len(comp) == 1:
                            no_sync_singleton += 1
                        if has_direct_coincidence:
                            no_sync_with_direct_coincidence += 1
                        if has_noncoincident_exit:
                            no_sync_with_noncoincident_exit += 1
                        if not has_direct_coincidence and not has_noncoincident_exit:
                            no_sync_closed_candidate += 1

                        print(
                            "NO_SYNC_JSON {\"type\":\"no_sync\",\"i\":",
                            i, ",\"j\":", j, ",\"k\":", k,
                            ",\"scc\":", ci, ",\"size\":", len(comp),
                            ",\"direct_coincidence\":", 1 if has_direct_coincidence else 0,
                            ",\"noncoincident_exit\":", 1 if has_noncoincident_exit else 0,
                            ",\"state\":\"", a.states[comp[0]].key(), "\"}"
                        )
                    if has_clean_newborn:
                        scc_with_clean_newborn += 1

    print("C3 local one-step census")
    print("PIP specimens:", n_pip, " capped:", n_capped)
    print("recurrent noncoincident SCCs:", n_scc, " states:", n_states)
    print("SCCs with newborn synchronization:", scc_with_newborn)
    print("SCCs without newborn synchronization:", scc_without_newborn)
    print("SCCs with inherited synchronization:", scc_with_inherited)
    print("SCCs with both lineages synchronizing:", scc_with_both)
    print("SCCs with neither lineage synchronizing:", scc_with_neither)
    print("SCCs with clean-newborn state:", scc_with_clean_newborn)
    print("states with newborn synchronization:", states_with_newborn)
    print("states with inherited synchronization:", states_with_inherited)
    print("states with clean-newborn synchronization:", states_with_clean_newborn)
    print("no-sync SCCs that are singleton:", no_sync_singleton)
    print("no-sync SCCs with direct coincidence sibling:", no_sync_with_direct_coincidence)
    print("no-sync SCCs with noncoincident exit:", no_sync_with_noncoincident_exit)
    print("no-sync closed/no-direct-coincidence candidates:", no_sync_closed_candidate)
