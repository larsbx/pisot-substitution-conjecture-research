"""Exact finite-horizon census for the C3 newborn-boundary mechanism.

Corpus: every primitive irreducible Pisot substitution on {0,1,2} whose three
images have length 1, 2 or 3, i.e. the same 4554-specimen corpus as census.mojo.

For every recurrent noncoincident SCC, this program measures the least tested
inflation horizon at which an inherited zero-return boundary synchronizes and
the least horizon at which a newborn zero-return boundary synchronizes.

`clean newborn` is a deliberately weaker, finite diagnostic: along at least one
state's whole-pair inflation path, no inherited synchronizing boundary has been
seen before or at the first newborn synchronizing boundary. It must not be read
as the full C3 premise over all inherited boundaries/descendants.

No output of this program is a proof of G1, C1, C2 or C3.
"""

from psc.bpa import build, recurrent_noncoincident_sccs, substitution_incidence, inherited_sync_positions, newborn_sync_positions, inflate_pair
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


def main() raises:
    var horizon = 3
    var words = image_words()
    var n_pip = 0
    var n_capped = 0
    var n_scc = 0
    var n_states = 0

    var n_newborn_first = 0
    var n_inherited_first = 0
    var n_tie = 0
    var n_no_witness = 0
    var n_with_newborn = 0
    var n_without_newborn = 0
    var n_clean_newborn = 0

    # Index 0 is unused; histogram entries 1..horizon are SCC counts.
    var newborn_hist = List[Int]()
    for _ in range(horizon + 1):
        newborn_hist.append(0)

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

                    var first_inherited = horizon + 1
                    var first_newborn = horizon + 1
                    var first_clean_newborn = horizon + 1

                    for si in range(len(comp)):
                        var p = a.states[comp[si]].copy()
                        var inherited_clean = True

                        for n in range(1, horizon + 1):
                            var inherited_hits = inherited_sync_positions(sigma, p)
                            var newborn_hits = newborn_sync_positions(sigma, p)

                            if len(inherited_hits) > 0:
                                if n < first_inherited:
                                    first_inherited = n
                                inherited_clean = False

                            if len(newborn_hits) > 0:
                                if n < first_newborn:
                                    first_newborn = n
                                if inherited_clean and n < first_clean_newborn:
                                    first_clean_newborn = n

                            p = inflate_pair(sigma, p)

                    if first_newborn <= horizon:
                        n_with_newborn += 1
                        newborn_hist[first_newborn] += 1
                    else:
                        n_without_newborn += 1
                        print(
                            "NO_NEWBORN_JSON {\"type\":\"no_newborn\",\"i\":",
                            i, ",\"j\":", j, ",\"k\":", k,
                            ",\"scc\":", ci, ",\"size\":", len(comp),
                            ",\"horizon\":", horizon, "}"
                        )

                    if first_clean_newborn <= horizon:
                        n_clean_newborn += 1

                    if first_newborn < first_inherited:
                        n_newborn_first += 1
                    elif first_inherited < first_newborn:
                        n_inherited_first += 1
                    elif first_newborn <= horizon:
                        n_tie += 1
                    else:
                        n_no_witness += 1
                        print(
                            "NO_WITNESS_JSON {\"type\":\"no_witness\",\"i\":",
                            i, ",\"j\":", j, ",\"k\":", k,
                            ",\"scc\":", ci, ",\"size\":", len(comp),
                            ",\"horizon\":", horizon, "}"
                        )

    print("C3 finite horizon:", horizon)
    print("PIP specimens:", n_pip, " capped:", n_capped)
    print("recurrent noncoincident SCCs:", n_scc, " states:", n_states)
    print("first witness newborn:", n_newborn_first)
    print("first witness inherited:", n_inherited_first)
    print("first witness tie:", n_tie)
    print("no synchronization witness by horizon:", n_no_witness)
    print("SCCs with newborn synchronization:", n_with_newborn)
    print("SCCs without newborn synchronization:", n_without_newborn)
    print("SCCs with clean-newborn path:", n_clean_newborn)
    for n in range(1, horizon + 1):
        print("newborn first-horizon", n, ":", newborn_hist[n])
