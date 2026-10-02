"""Exploratory exhaustive sweep: bounded balanced-pair automata on a wider slice.

Not a census (`AGENTS.md`, "The census library"). Builds `B_sigma`
(`psc.bpa.build`) under the shared `STATE_CAP` for every PIP substitution on
{0,1,2} with total image length at most `TOTAL_LENGTH_CAP` and longest image
at most `MAX_LONGEST_IMAGE`: 14670 specimens, whose longest-image <= 3 part is
the standing corpus. It tests, as finite evidence only, a lost note's claim
that Level 2 (finite BPA) was closed for this slice
(docs/lost-depth-indexed-formulation-2026-10-01.md §3).

Enumeration is exhaustive and deterministic (no seed, no stride). Budget:
`STATE_CAP` states per automaton. Termination below the cap is finite BPA for
that specimen; a capped build is inconclusive and is named, and the run then
exits non-zero. A clean run proves nothing about G1 / G1b-2 in general.
"""

from psc.bpa import build, nonproductive_states
from psc.corpus import STATE_CAP, TOTAL_LENGTH_CAP, pip_corpus_total_length, report_progress
from psc.histogram import max_int


comptime MAX_LONGEST_IMAGE = 4


def main() raises:
    print(
        "exploratory sweep: B_sigma for PIP substitutions with total image length <=",
        TOTAL_LENGTH_CAP, " longest image <=", MAX_LONGEST_IMAGE, " state cap:", STATE_CAP,
    )
    var corpus = pip_corpus_total_length(TOTAL_LENGTH_CAP)
    var specimens = List[Int](length=MAX_LONGEST_IMAGE + 1, fill=0)
    var terminated = List[Int](length=MAX_LONGEST_IMAGE + 1, fill=0)
    var largest = List[Int](length=MAX_LONGEST_IMAGE + 1, fill=0)
    var nonproductive = List[Int](length=MAX_LONGEST_IMAGE + 1, fill=0)
    var n_capped = 0
    var n_failed = 0
    var visited = 0
    for s in range(len(corpus)):
        ref spec = corpus[s]
        var longest = spec.longest_image()
        if longest > MAX_LONGEST_IMAGE:
            continue
        specimens[longest] += 1
        visited += 1
        try:
            var a = build(spec.sigma, STATE_CAP)
            if a.capped:
                n_capped += 1
                print("CAPPED specimen:", spec.label())
                continue
            terminated[longest] += 1
            largest[longest] = max_int(largest[longest], a.size())
            if len(nonproductive_states(a)) > 0:
                nonproductive[longest] += 1
                print("NON-PRODUCTIVE specimen:", spec.label())
        except e:
            n_failed += 1
            print("FAILED specimen:", spec.label(), " ", e)
        report_progress(visited)

    print("specimens:", visited, " capped:", n_capped, " failed:", n_failed)
    for longest in range(1, MAX_LONGEST_IMAGE + 1):
        print(
            "longest image", longest,
            ": specimens:", specimens[longest],
            " terminated:", terminated[longest],
            " largest |B_sigma|:", largest[longest],
            " non-productive:", nonproductive[longest],
        )
    if n_capped > 0 or n_failed > 0:
        raise Error(
            "incomplete sweep: " + String(n_capped) + " capped and "
            + String(n_failed) + " failed specimens"
        )
