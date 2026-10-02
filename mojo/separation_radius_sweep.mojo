"""Exploratory exhaustive sweep: collar separation radii above the census cap.

Not a census (`AGENTS.md`, "The census library"). Over the 24486 PIP
substitutions on {0,1,2} with total image length at most `TOTAL_LENGTH_CAP`
(`psc.corpus.pip_corpus_total_length`), computes the least collar radius at
which every occurrence's one-step ancestry is determined
(`psc.overlap_collar.separation_radius`, docs/p1-overlap-collar-2026-09-16.md)
with cap `RADIUS_CAP`, and crosses it with seed-patch collapse by level
`COLLAPSE_LEVEL`. The swap-overlap survey caps the radius at 6; this sweep
asks what lies beyond that cap (docs/lost-depth-indexed-formulation-2026-10-01.md
§6).

Enumeration is exhaustive and deterministic (no seed, no stride). Budgets:
`STATE_CAP` overlap states, `COLLARED_STATE_CAP` collared states per radius,
`RADIUS_CAP`, `COLLAPSE_LEVEL`. A survivor at `RADIUS_CAP` is reported as a
survivor, not as an unresolvable collision; a specimen that exhausts a state
budget is named, and the run then exits non-zero. A complete run is finite
evidence about this class at these caps only.
"""

from psc.corpus import (
    MAX_IMAGE_LENGTH,
    STATE_CAP,
    TOTAL_LENGTH_CAP,
    pip_corpus_total_length,
    report_progress,
)
from psc.histogram import Histogram, max_int
from psc.overlap_collar import collapsing_seed_pair_count, separation_radius
from psc.overlap_seed_patch import PerronCache, build_seed_overlap_graph_from_tables


comptime RADIUS_CAP = 12
comptime COLLAPSE_LEVEL = 12
comptime COLLARED_STATE_CAP = 1000000


struct RadiusTable(Copyable, Movable):
    """Separation radii of one slice, with survivors at the cap split by
    whether some seed patch collapses by `COLLAPSE_LEVEL`."""

    var radius: Histogram
    var survivors_collapsing: Int
    var survivors_not_collapsing: Int
    var resolved_collapsing: Int

    def __init__(out self):
        self.radius = Histogram(RADIUS_CAP + 1)
        self.survivors_collapsing = 0
        self.survivors_not_collapsing = 0
        self.resolved_collapsing = 0

    def absorb(mut self, radius: Int, collapsing: Bool) raises:
        if radius < 0:
            if collapsing:
                self.survivors_collapsing += 1
            else:
                self.survivors_not_collapsing += 1
            return
        self.radius.record(radius)
        self.resolved_collapsing += 1 if collapsing else 0

    def print_lines(self, name: String):
        print(self.radius.line(name + " specimens by separation radius:"))
        print(
            name, "survivors at radius", RADIUS_CAP,
            ": collapsing by level", COLLAPSE_LEVEL, ":", self.survivors_collapsing,
            " not collapsing:", self.survivors_not_collapsing,
            " resolved yet collapsing:", self.resolved_collapsing,
        )


def longest_image(sigma: List[List[Int]]) -> Int:
    return max_int(max_int(len(sigma[0]), len(sigma[1])), len(sigma[2]))


def main() raises:
    print(
        "exploratory sweep: PIP substitutions with total image length <=", TOTAL_LENGTH_CAP,
        " radius cap:", RADIUS_CAP, " collapse level:", COLLAPSE_LEVEL,
        " collared state cap:", COLLARED_STATE_CAP,
    )
    var corpus = pip_corpus_total_length(TOTAL_LENGTH_CAP)
    var perron = PerronCache()
    var whole = RadiusTable()
    var standing = RadiusTable()
    var n_capped = 0
    var n_failed = 0
    var max_resolved = 0
    for s in range(len(corpus)):
        ref spec = corpus[s]
        try:
            var tables = perron.tables_for(spec.sigma)
            var g = build_seed_overlap_graph_from_tables(tables, STATE_CAP)
            if g.capped:
                n_capped += 1
                print("CAPPED specimen:", spec.label())
                continue
            var radius = separation_radius(tables, g, RADIUS_CAP, COLLARED_STATE_CAP)
            var collapsing = collapsing_seed_pair_count(spec.sigma, COLLAPSE_LEVEL) > 0
            if radius < 0 and not collapsing:
                print("SURVIVOR without a collapsing patch at radius", RADIUS_CAP, ":", spec.label())
            if radius > 6:
                print("separation radius", radius, "above the survey cap:", spec.label())
            max_resolved = max_int(max_resolved, radius)
            whole.absorb(radius, collapsing)
            if longest_image(spec.sigma) <= MAX_IMAGE_LENGTH:
                standing.absorb(radius, collapsing)
        except e:
            n_failed += 1
            print("FAILED specimen:", spec.label(), " ", e)
        report_progress(s + 1)

    print("PIP specimens:", len(corpus), " capped:", n_capped, " failed:", n_failed)
    print("maximum resolved separation radius:", max_resolved)
    whole.print_lines("total-length class")
    standing.print_lines("standing slice")
    if n_capped > 0 or n_failed > 0:
        raise Error(
            "incomplete sweep: " + String(n_capped) + " capped and "
            + String(n_failed) + " failed specimens"
        )
