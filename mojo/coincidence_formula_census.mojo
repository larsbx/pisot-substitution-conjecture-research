"""Strong coincidence decided by formula, against the overlap graph, per pair.

For **every** specimen this decides `SC(i, j)` for each pair of letters by the
search of `psc.coincidence_formula`, which is cheap enough that sampling would
be a false economy, and then checks the answer twice over against two things
that share no step with it:

* **Each witness, directly.** A shortest accepted word splits into two
  Dumont-Thomas paths; `path_prefix_parikh` and `path_letter` recompute the
  Parikh vectors and the letters from the substitution alone. A witness that
  does not check is a defect, not a finding.
* **Each level, against the overlap graph.** A left-aligned non-coincidence
  vertex `(i, j, 0)` of the seed-patch overlap automaton is productive exactly
  when the pair is eventually coincident, and its first-coincidence depth is
  the least number of inflations that reaches one. That depth and the shortest
  witness are computed from different objects -- exact cubic tile geometry on
  one side, an integer Parikh difference on the other -- and must agree. This
  one *is* sampled, because building the graph is what costs, and the two
  counts are reported apart so a reader can see which claim covers what.

The exploration carries no budget outcome: its state set is finite by the
argument in `psc.coincidence_formula`, so a cap is a guard against a defect in
that file and exceeding it raises. This driver catches nothing, so anything
that raises aborts the census rather than being counted as an inconclusive
specimen.

Deciding the condition per specimen is not deciding it for the family. Strong
coincidence for alphabet-3 Pisot substitutions is open, and a clean sweep here
is elimination of counterexamples over a finite corpus and nothing more.
"""

from psc.coincidence_formula import (
    coincidence_witness,
    pair_paths,
    path_letter,
    path_prefix_parikh,
)
from psc.corpus import STATE_CAP, pip_corpus, report_progress
from psc.dumont_thomas import max_image_length
from psc.histogram import Histogram, max_int
from psc.overlap_seed_patch import (
    PerronCache,
    build_seed_overlap_graph_from_tables,
    first_coincidence_depths,
)
from psc.words import ALPHABET

# The formula is cheap, so every specimen is decided; the overlap graph is not,
# so the cross-check is sampled. Keeping them apart is the point: the verdict
# covers the corpus, and the agreement covers a sample of it.
comptime COMPARE_STRIDE = 30


def main() raises:
    var corpus = pip_corpus()
    var perron = PerronCache()
    var decided = 0
    var capped_graphs = 0
    var compared = 0
    var pairs = 0
    var witnesses = 0
    var bad_witnesses = 0
    var depth_matches = 0
    var depth_mismatches = 0
    var without_coincidence = 0
    var deepest = 0
    var levels = Histogram(256)

    for s in range(len(corpus)):
        ref spec = corpus[s]
        decided += 1
        var radix = max_image_length(spec.sigma)

        # Every ordered pair, so a left-aligned overlap vertex is found in
        # whichever orientation the graph happens to carry it.
        var mine = List[Int]()
        for i in range(ALPHABET):
            for j in range(ALPHABET):
                pairs += 1
                var found = coincidence_witness(spec.sigma, i, j)
                if found.empty:
                    mine.append(-1)
                    continue
                var level = len(found.word)
                mine.append(level)
                levels.record(level)
                deepest = max_int(deepest, level)

                # The witness, recomputed from the substitution alone.
                witnesses += 1
                var paths = pair_paths(radix, found.word)
                var top = path_prefix_parikh(spec.sigma, i, paths[0])
                var bottom = path_prefix_parikh(spec.sigma, j, paths[1])
                var agrees = path_letter(spec.sigma, i, paths[0]) == path_letter(
                    spec.sigma, j, paths[1]
                )
                for letter in range(ALPHABET):
                    if top[letter] != bottom[letter]:
                        agrees = False
                if not agrees:
                    bad_witnesses += 1
                    print("BAD WITNESS", spec.label(), i, j)

        # Strong coincidence is every pair coinciding, and the per-pair levels
        # are already in hand: asking the module again would rebuild the same
        # three automata to learn the same thing.
        var all_pairs = True
        for i in range(ALPHABET):
            for j in range(i + 1, ALPHABET):
                if mine[i * ALPHABET + j] < 0:
                    all_pairs = False
        if not all_pairs:
            without_coincidence += 1
            print("NO STRONG COINCIDENCE", spec.label())

        if s % COMPARE_STRIDE != 0:
            report_progress(s, len(corpus))
            continue
        var tables = perron.tables_for(spec.sigma)
        var graph = build_seed_overlap_graph_from_tables(tables, STATE_CAP)
        if graph.capped:
            capped_graphs += 1
            print("CAPPED OVERLAP GRAPH", spec.label())
            report_progress(s, len(corpus))
            continue
        compared += 1
        var depths = first_coincidence_depths(graph)
        for v in range(graph.size()):
            ref state = graph.states[v]
            if state.is_coincidence() or not state.shift.is_zero():
                continue
            if depths[v] == mine[state.top * ALPHABET + state.bottom]:
                depth_matches += 1
            else:
                depth_mismatches += 1
                print("DEPTH MISMATCH", spec.label(), state.top, state.bottom,
                      " overlap:", depths[v],
                      " formula:", mine[state.top * ALPHABET + state.bottom])
        report_progress(s, len(corpus))

    print("corpus:", len(corpus), " specimens decided:", decided,
          " compare stride:", COMPARE_STRIDE)
    print("ordered pairs decided:", pairs, " witnesses checked:", witnesses,
          " witnesses that did not check:", bad_witnesses)
    print("specimens without strong coincidence:", without_coincidence)
    print("overlap graphs compared:", compared, " capped:", capped_graphs)
    print("left-aligned depths equal to the witness level:", depth_matches,
          " different:", depth_mismatches)
    print("deepest coincidence level:", deepest)
    print(levels.line("pairs by coincidence level"))
