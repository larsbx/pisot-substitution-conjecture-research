"""Exact census of valuation ascent over the catch-up-free class.

For each catch-up-free specimen (Lemma P) of the standing corpus, or of the
24,486 specimens of total image length at most 8 with `total`,
`psc.valuation_ascent` decides one-step valuation ascent on the box graph and
measures the ascent depth. VA would give T2
(docs/p1b-vertex-coincidence-box-2026-10-02.md §5.6c); a single failing
vertex refutes it as a local mechanism for that specimen. Folded in canonical
order on `parallel_fold`.

Usage: `mojo run -I . valuation_ascent_census.mojo [total]`.
"""

from std.sys import argv
from parallel_fold.map_fold import parallel_map_fold
from psc.corpus import Specimen, TOTAL_LENGTH_CAP, pip_corpus, pip_corpus_total_length
from psc.histogram import Histogram, max_int
from psc.one_tile import catch_up_free
from psc.valuation_ascent import valuation_ascent

comptime WORKERS = 4


struct AscentCensus(Copyable, Movable):
    var free: Int
    var vertices: Int
    var failures: Int
    var holding: Int  # specimens on which one-step VA holds
    var depths: List[Int]  # max ascent depth per free specimen
    var k0: List[Int]
    var by_nu: List[Int]
    var failed_index: Int

    def __init__(out self):
        self.free = 0
        self.vertices = 0
        self.failures = 0
        self.holding = 0
        self.depths = List[Int]()
        self.k0 = List[Int]()
        self.by_nu = List[Int](length=64, fill=0)
        self.failed_index = -1


def merge(a: AscentCensus, b: AscentCensus) -> AscentCensus:
    var out = a.copy()
    out.free += b.free
    out.vertices += b.vertices
    out.failures += b.failures
    out.holding += b.holding
    out.depths += b.depths.copy()
    out.k0 += b.k0.copy()
    for k in range(64):
        out.by_nu[k] += b.by_nu[k]
    if b.failed_index >= 0 and (out.failed_index < 0 or b.failed_index < out.failed_index):
        out.failed_index = b.failed_index
    return out^


def main() raises:
    var args = argv()
    var corpus = pip_corpus_total_length(TOTAL_LENGTH_CAP) if len(args) > 1 and String(args[1]) == "total" else pip_corpus()

    def one(s: Int) {corpus} -> AscentCensus:
        var out = AscentCensus()
        if not catch_up_free(corpus[s].sigma):
            return out^
        try:
            var v = valuation_ascent(corpus[s].sigma)
            out.free = 1
            out.vertices = v.vertices
            out.failures = v.one_step_failures
            out.holding = 1 if v.one_step_failures == 0 else 0
            out.depths.append(v.max_ascent_depth)
            out.k0.append(v.max_valuation)
            for k in range(len(v.failures_by_valuation)):
                out.by_nu[k] += v.failures_by_valuation[k]
        except:
            out.failed_index = s
        return out^

    var r = parallel_map_fold(one, merge, AscentCensus(), len(corpus), WORKERS)
    if r.failed_index >= 0:
        _ = valuation_ascent(corpus[r.failed_index].sigma)
        raise Error("valuation ascent census: worker failure did not replay")
    var depth = Histogram(128)
    var k0 = Histogram(64)
    for i in range(len(r.depths)):
        depth.record(r.depths[i])
        k0.record(r.k0[i])
    print("Valuation ascent census, specimens:", len(corpus), " catch-up-free:", r.free)
    print("vertices:", r.vertices, " one-step failures:", r.failures, " specimens where one-step VA holds:", r.holding)
    var line = String("one-step failures by valuation:")
    for k in range(64):
        if r.by_nu[k] > 0:
            line += " " + String(k) + ":" + String(r.by_nu[k])
    print(line)
    print(k0.line("catch-up-free specimens by K0 (largest nonzero valuation):"))
    print(depth.line("catch-up-free specimens by largest ascent depth:"))
