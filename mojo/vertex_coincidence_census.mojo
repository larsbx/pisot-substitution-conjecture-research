"""Exact census: PeriodicPairVertexCoincidence for every r, over a PIP corpus.

For each specimen, `psc.vertex_coincidence` builds the box graph of Proposition V
(docs/p1b-vertex-coincidence-box-2026-10-02.md) and decides whether every
vertex has an offset-zero descendant. That holds exactly when, for every
r >= 1, every pair of Phi^r-fixed tilings T(i, P), T(j, Q) + <l, w0> with
integral centre offset shares a vertex. A failing specimen would be a strict
zipper and is printed with its witness vertex; a capped graph is reported as
capped and is not a verdict.

Usage: `mojo run -I . vertex_coincidence_census.mojo [total]` surveys the 4554
standing specimens, or with `total` the 24486 specimens of total image length
at most 8. Specimens are folded in canonical order on `parallel_fold`, so the
record does not depend on the worker count.
"""

from std.sys import argv
from parallel_fold.map_fold import parallel_map_fold
from psc.corpus import Specimen, TOTAL_LENGTH_CAP, pip_corpus, pip_corpus_total_length
from psc.vertex_coincidence import decide_vertex_coincidence

comptime WORKERS = 4


struct VertexCensus(Copyable, Movable):
    var specimens: Int
    var holds: Int
    var capped: Int
    var failing: List[Int]
    var failed_index: Int
    var max_states: Int
    var max_states_index: Int
    var max_recurrent: Int
    var max_recurrent_index: Int
    var max_deepest: Int
    var max_deepest_index: Int
    var recurrent_total: Int

    def __init__(out self):
        self.specimens = 0
        self.holds = 0
        self.capped = 0
        self.failing = List[Int]()
        self.failed_index = -1
        self.max_states = 0
        self.max_states_index = -1
        self.max_recurrent = 0
        self.max_recurrent_index = -1
        self.max_deepest = -1
        self.max_deepest_index = -1
        self.recurrent_total = 0


def merge(a: VertexCensus, b: VertexCensus) -> VertexCensus:
    var out = a.copy()
    out.specimens += b.specimens
    out.holds += b.holds
    out.capped += b.capped
    for i in range(len(b.failing)):
        out.failing.append(b.failing[i])
    if b.failed_index >= 0 and (out.failed_index < 0 or b.failed_index < out.failed_index):
        out.failed_index = b.failed_index
    # strict comparisons keep the first specimen in canonical order
    if b.max_states > out.max_states:
        out.max_states = b.max_states
        out.max_states_index = b.max_states_index
    if b.max_recurrent > out.max_recurrent:
        out.max_recurrent = b.max_recurrent
        out.max_recurrent_index = b.max_recurrent_index
    if b.max_deepest > out.max_deepest:
        out.max_deepest = b.max_deepest
        out.max_deepest_index = b.max_deepest_index
    out.recurrent_total += b.recurrent_total
    return out^


def evaluate(index: Int, spec: Specimen) -> VertexCensus:
    var out = VertexCensus()
    out.specimens = 1
    try:
        var v = decide_vertex_coincidence(spec.sigma)
        if v.capped:
            out.capped = 1
            return out^
        if v.holds:
            out.holds = 1
        else:
            out.failing.append(index)
        out.max_states = v.states
        out.max_states_index = index
        out.max_recurrent = v.recurrent
        out.max_recurrent_index = index
        out.max_deepest = v.deepest
        out.max_deepest_index = index
        out.recurrent_total = v.recurrent
    except:
        out.failed_index = index
    return out^


def main() raises:
    var args = argv()
    var total = len(args) > 1 and String(args[1]) == "total"
    var corpus = pip_corpus_total_length(TOTAL_LENGTH_CAP) if total else pip_corpus()

    def one(s: Int) {corpus} -> VertexCensus:
        return evaluate(s, corpus[s])

    var r = parallel_map_fold(one, merge, VertexCensus(), len(corpus), WORKERS)
    if r.failed_index >= 0:
        # replay sequentially so the kernel's own error is raised
        _ = decide_vertex_coincidence(corpus[r.failed_index].sigma)
        raise Error("vertex coincidence census: worker failure did not replay")
    print("Vertex coincidence census (Proposition V), specimens:", r.specimens)
    print("holds for every r:", r.holds, " capped:", r.capped, " fails:", len(r.failing))
    for i in range(len(r.failing)):
        var spec = corpus[r.failing[i]].copy()
        print("STRICT ZIPPER specimen:", spec.label(), decide_vertex_coincidence(spec.sigma).witness)
    if r.max_states_index >= 0:
        print("largest box graph:", r.max_states, "states, specimen", corpus[r.max_states_index].label())
        print("most recurrent vertices:", r.max_recurrent, "specimen", corpus[r.max_recurrent_index].label())
        print("deepest recurrent first left-aligned depth:", r.max_deepest, "specimen", corpus[r.max_deepest_index].label())
        print("recurrent vertices in total:", r.recurrent_total)
