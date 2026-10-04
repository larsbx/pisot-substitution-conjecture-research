"""Exact census: PeriodicPairVertexCoincidence for every r, over a PIP corpus.

For each specimen, `psc.vertex_coincidence` builds the box graph of Proposition V
(docs/p1b-vertex-coincidence-box-2026-10-02.md) and decides whether every
vertex has an offset-zero descendant. That holds exactly when, for every
r >= 1, every pair of Phi^r-fixed tilings T(i, P), T(j, Q) + <l, w0> with
integral centre offset shares a vertex. A failing specimen would be a strict
zipper and is printed with its witness vertex; a capped graph is reported as
capped and is not a verdict.

Usage: `mojo run -I . vertex_coincidence_census.mojo [total | len4 START END] [records]`
surveys the 4554 standing specimens; with `total` the 24486 specimens of total
image length at most 8; with `len4 START END` the slice `[START, END)` of the
135990 specimens with images of length at most 4 (labels index
`image_words_up_to(4)`), so that long survey can run in resumable chunks. With a final
`records`, one `K_V record: i j k K_V` line per specimen follows the summary. Specimens are folded in canonical order on `parallel_fold`, so the
record does not depend on the worker count.
"""

from std.sys import argv
from parallel_fold.map_fold import parallel_map_fold
from psc.corpus import (
    Specimen,
    TOTAL_LENGTH_CAP,
    arithmetic_regime,
    image_words_up_to,
    pip_corpus,
    pip_corpus_total_length,
    screened_triples,
)
from psc.vertex_coincidence import decide_vertex_coincidence

comptime WORKERS = 4
comptime DEPTH_SLOTS = 64
comptime REGIMES = 4


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
    # one (index, K_V) pair per evaluated specimen, in canonical order
    var depths: List[Int]
    # K_V histogram by arithmetic regime: depth_by_regime[regime * DEPTH_SLOTS + K_V]
    var depth_by_regime: List[Int]

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
        self.depths = List[Int]()
        self.depth_by_regime = List[Int](length=REGIMES * DEPTH_SLOTS, fill=0)


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
    for k in range(len(b.depths)):
        out.depths.append(b.depths[k])
    for k in range(len(out.depth_by_regime)):
        out.depth_by_regime[k] += b.depth_by_regime[k]
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
        out.depths.append(index)
        out.depths.append(v.deepest)
        if v.deepest < 0 or v.deepest >= DEPTH_SLOTS:
            raise Error("K_V outside the histogram")
        out.depth_by_regime[arithmetic_regime(spec.incidence) * DEPTH_SLOTS + v.deepest] += 1
    except:
        out.failed_index = index
    return out^


def main() raises:
    var args = argv()
    var mode = String(args[1]) if len(args) > 1 else String("")
    var corpus = List[Specimen]()
    if mode == "total":
        corpus = pip_corpus_total_length(TOTAL_LENGTH_CAP)
    elif mode == "len4":
        if len(args) != 4 and len(args) != 5:
            raise Error("usage: len4 START END [records]")
        var full = screened_triples(image_words_up_to(4), 12)
        var start = Int(String(args[2]))
        var end = min(Int(String(args[3])), len(full))
        if start < 0 or start > end:
            raise Error("len4 slice lies outside the corpus")
        print("images of length <= 4: specimens", len(full), "slice", start, end)
        for s in range(start, end):
            corpus.append(full[s].copy())
    else:
        corpus = pip_corpus()

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
        var names: List[String] = ["nonunimodular", "unimodular real", "unimodular complex", "zero discriminant"]
        for g in range(REGIMES):
            var line = String("K_V by specimen, ") + names[g] + ":"
            var any = False
            for k in range(DEPTH_SLOTS):
                var n = r.depth_by_regime[g * DEPTH_SLOTS + k]
                if n > 0:
                    line += " " + String(k) + ":" + String(n)
                    any = True
            if any:
                print(line)
    if String(args[len(args) - 1]) == "records":
        # per-specimen K_V, for offline analysis against spectral data
        for k in range(0, len(r.depths), 2):
            print("K_V record:", corpus[r.depths[k]].label(), r.depths[k + 1])
