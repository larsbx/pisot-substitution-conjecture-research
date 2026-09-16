"""Exact census of the seed-patch overlap graphs over the alphabet-3 PIP corpus.

For every primitive irreducible Pisot substitution on {0,1,2} with images of
length at most 3 (exact Sturm-sequence screening), builds the seed-patch
overlap graph of `psc.overlap_seed_patch` from the three swap seeds under a
cap of 20000 states and reports sizes and productivity.  The finiteness of
this graph is a theorem (docs/overlap-finiteness-and-coincidence-density-
2026-09-13.md); the cap is retained only as a fail-closed guard.  Overlap
productivity for every reachable overlap is the open Level-3 statement in its
G1-free form; a clean corpus is finite evidence only.
"""

from psc.corpus import STATE_CAP, pip_corpus, report_progress
from psc.histogram import Histogram, max_int
from psc.overlap_recurrence import zero_shift_free_recurrent_sccs
from psc.overlap_seed_patch import (
    SeedOverlapAutomaton,
    SeedOverlapTables,
    build_seed_overlap_graph_from_tables,
    build_seed_overlap_tables,
    first_coincidence_depths,
    first_left_aligned_depths,
    nonproductive_overlap_states,
    strong_coincidence_depth_from,
)


struct DepthProfile(Copyable, Movable):
    """Per-specimen maxima of the four depth statistics on a productive graph."""

    var coincidence: Int
    var left_aligned: Int
    var prefix_strong: Int
    var suffix_strong: Int

    def __init__(out self, coincidence: Int, left_aligned: Int, prefix_strong: Int, suffix_strong: Int):
        self.coincidence = coincidence
        self.left_aligned = left_aligned
        self.prefix_strong = prefix_strong
        self.suffix_strong = suffix_strong


def depth_profile(tables: SeedOverlapTables, g: SeedOverlapAutomaton) raises -> DepthProfile:
    """Depth maxima with the exact inequalities `0 <= b <= c <= b + prefix`
    checked on every vertex (a violation is a kernel defect, so it raises)."""
    var depths = first_coincidence_depths(g)
    var left = first_left_aligned_depths(g)
    var prefix_scc = strong_coincidence_depth_from(depths, g, tables, False)
    var suffix_scc = strong_coincidence_depth_from(depths, g, tables, True)
    if prefix_scc < 0 or suffix_scc < 0:
        raise Error("endpoint-aligned overlap without coincidence on a productive graph")
    var worst = 0
    var worst_left = 0
    for v in range(len(depths)):
        if left[v] < 0 or left[v] > depths[v]:
            raise Error("left-aligned depth must be defined and at most the coincidence depth")
        if depths[v] > left[v] + prefix_scc:
            raise Error("coincidence depth exceeds left-aligned depth plus prefix strong-coincidence depth")
        worst = max_int(worst, depths[v])
        worst_left = max_int(worst_left, left[v])
    return DepthProfile(worst, worst_left, prefix_scc, suffix_scc)


def main() raises:
    var corpus = pip_corpus()
    var n_built = 0
    var n_capped = 0
    var n_failed = 0
    var n_nonproductive_states = 0
    var n_nonproductive_specimens = 0
    var n_zipper_specimens = 0
    var n_zipper_sccs = 0
    var max_zipper_size = 0
    var largest = 0
    var total_states = 0
    var coincidence = Histogram()
    var left_aligned = Histogram()
    var prefix_strong = Histogram()
    var suffix_strong = Histogram()

    for s in range(len(corpus)):
        ref spec = corpus[s]
        try:
            var tables = build_seed_overlap_tables(spec.sigma)
            var g = build_seed_overlap_graph_from_tables(tables, STATE_CAP)
            if g.capped:
                n_capped += 1
                print("CAPPED specimen:", spec.label())
                continue
            n_built += 1
            total_states += g.size()
            largest = max_int(largest, g.size())

            # Necessary finite signature of the strict left-boundary zipper
            # branch: after deleting coincidences and all offset-zero states,
            # does any directed recurrence remain?  Right-aligned states are
            # intentionally retained here.
            var zipper_sccs = zero_shift_free_recurrent_sccs(g)
            if len(zipper_sccs) > 0:
                n_zipper_specimens += 1
                n_zipper_sccs += len(zipper_sccs)
                for z in range(len(zipper_sccs)):
                    max_zipper_size = max_int(max_zipper_size, len(zipper_sccs[z]))

            var bad = len(nonproductive_overlap_states(g))
            if bad > 0:
                # A nonproductive graph is the mathematical event this census
                # exists to detect; record it before any depth statistic,
                # which is undefined on such a graph.
                n_nonproductive_specimens += 1
                n_nonproductive_states += bad
                print("NONPRODUCTIVE overlap specimen:", spec.label(), " states:", bad)
                continue
            var profile = depth_profile(tables, g)
            coincidence.record(profile.coincidence)
            left_aligned.record(profile.left_aligned)
            prefix_strong.record(profile.prefix_strong)
            suffix_strong.record(profile.suffix_strong)
        except e:
            n_failed += 1
            print("FAILED specimen:", spec.label(), " ", e)
        report_progress(s + 1)

    print("PIP specimens:", len(corpus))
    print("overlap graphs built:", n_built, " capped:", n_capped, " failed:", n_failed)
    print("largest seed-patch overlap graph:", largest)
    print("total seed-patch overlap states:", total_states)
    print("nonproductive overlap specimens:", n_nonproductive_specimens, " states:", n_nonproductive_states)
    print(
        "zero-shift-free recurrent overlap cycles: specimens:", n_zipper_specimens,
        " sccs:", n_zipper_sccs, " largest-scc:", max_zipper_size,
    )
    print("maximum first-coincidence depth:", coincidence.maximum())
    print(coincidence.line("specimens by maximal first-coincidence depth:"))
    print("maximum first left-aligned depth:", left_aligned.maximum())
    print(left_aligned.line("specimens by maximal first left-aligned depth:"))
    print("maximum prefix strong-coincidence depth:", prefix_strong.maximum())
    print(prefix_strong.line("specimens by prefix strong-coincidence depth:"))
    print("maximum suffix strong-coincidence depth:", suffix_strong.maximum())
    print(suffix_strong.line("specimens by suffix strong-coincidence depth:"))
