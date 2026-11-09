"""The `K_2 = 0` window search for strict systems off the PIP corpus
(exploratory, labelled; docs/c4-closed-component-search-2026-11-07.md, gate
docs/c4-solidify-stop-go-2026-11-07.md §4.6).

`P_L` is the complete list of normalised irreducible noncoincident ternary
pairs with `K_2 = 0` and length at most `L`, read from the exact census of
experiment A (`psc.binomial_pairs.census_length`). For each specimen the
greatest fixed point of `X -> {T in X : children(T) <= X}` below `P_L` is
computed (`psc.closed_component_search.window_specimen`): it is empty iff the
specimen has no strict system whose states all have `K_2 = 0` and length at
most `L`. That is a WINDOW OBSERVATION, never a verdict. Alongside, the
strong-coincidence profile decides "no strict system at all" where all three
letter pairs carry a witness on one side (Theorem A(4) or its reversal): a
VERDICT where a witness exists, undecided otherwise.

Passes, over the primitive substitutions with images of length 1..3 outside
the PIP corpus, in `psc.corpus.image_words` order:

* `domain` (always): the non-synchronizing specimens of the one-outside and
  reducible classes, the window domain of the gate;
* `r3` (default on): the non-synchronizing both-outside specimens, as a
  consistency check of Theorem R3 only (a nonempty limit is a defect and
  raises); nothing is reported for them as an observation;
* `endpoint` (with PASSES = all): every synchronizing specimen, as a
  consistency check of the endpoint filter (a nonempty limit raises).

The reducible strict systems with `K_2 != 0` are not searched for (gate §0,
row B3): they are the 28 pinned carriers of
`tests/test_c4_quotient_spectrum.mojo`, whose seeds have `K_2 != 0`
(pinned by `tests/test_c4_closed_component_search.mojo`).

Fail closed: a specimen whose computation raises aborts the run (the first
one is replayed serially so its error surfaces); a consistency violation
prints the specimen's records and raises.

Usage:
  mojo run -I . c4_closed_component_search.mojo [L [WORDS [START STOP [STRIDE [PASSES]]]]]
Defaults: L = 13, WORDS = 20000 letters per witness word, the whole
off-corpus list (28,764 specimens), stride 1, PASSES = `domain+r3`
(`all` adds the endpoint pass). The regression slices of
`tests/test_c4_closed_component_search.mojo` are `11 20000 0 28764 1` and
`13 20000 0 28764 21` (domain and R3 passes). The PIP corpus is not searched:
the 1,542 non-synchronizing PIP specimens of the gate's scratch window are
outside experiment B.
"""

from std.sys import argv
from parallel_fold.map_fold import parallel_map_fold
from psc.closed_component_search import (
    CLASS_BOTH_OUTSIDE,
    CLASS_COUNT,
    CLASS_ONE_OUTSIDE,
    CLASS_REDUCIBLE,
    OffCorpusSpecimen,
    WindowRecord,
    class_name,
    emit_component,
    is_synchronizing,
    k2_zero_universe,
    off_corpus_specimens,
    window_specimen,
)
from psc.corpus import pip_corpus
from psc.symmetry import substitution_key

comptime WORKERS = 4
comptime PASS_DOMAIN = 0
comptime PASS_R3 = 1
comptime PASS_ENDPOINT = 2
comptime PASS_COUNT = 3


def pass_of(s: OffCorpusSpecimen) -> Int:
    if s.in_window_domain():
        return PASS_DOMAIN
    if not s.synchronizing and s.klass == CLASS_BOTH_OUTSIDE:
        return PASS_R3
    return PASS_ENDPOINT


def pass_name(p: Int) -> String:
    if p == PASS_DOMAIN:
        return "domain"
    if p == PASS_R3:
        return "r3-consistency"
    return "endpoint-consistency"


struct Tally(Copyable, Movable):
    """Counts indexed by `CLASS_COUNT * pass + class`."""

    var specimens: List[Int]
    var sc_left: List[Int]
    var sc_right: List[Int]
    var sc_either: List[Int]
    var first_pass_specimens: List[Int]
    var first_pass_pairs: List[Int]
    var survivor_specimens: List[Int]
    var components: List[Int]
    var first_pass_rows: List[Int]   # (index, first_pass, rounds, survivors) per specimen with first_pass > 0
    var found: List[Int]             # specimen indices with a nonempty limit
    var violations: List[Int]
    var failed: List[Int]

    def __init__(out self):
        self.specimens = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.sc_left = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.sc_right = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.sc_either = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.first_pass_specimens = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.first_pass_pairs = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.survivor_specimens = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.components = List[Int](length=PASS_COUNT * CLASS_COUNT, fill=0)
        self.first_pass_rows = List[Int]()
        self.found = List[Int]()
        self.violations = List[Int]()
        self.failed = List[Int]()


def _add_into(mut a: List[Int], b: List[Int]):
    for i in range(len(a)):
        a[i] += b[i]


def merge(a: Tally, b: Tally) -> Tally:
    var out = a.copy()
    _add_into(out.specimens, b.specimens)
    _add_into(out.sc_left, b.sc_left)
    _add_into(out.sc_right, b.sc_right)
    _add_into(out.sc_either, b.sc_either)
    _add_into(out.first_pass_specimens, b.first_pass_specimens)
    _add_into(out.first_pass_pairs, b.first_pass_pairs)
    _add_into(out.survivor_specimens, b.survivor_specimens)
    _add_into(out.components, b.components)
    out.first_pass_rows += b.first_pass_rows.copy()
    out.found += b.found.copy()
    out.violations += b.violations.copy()
    out.failed += b.failed.copy()
    return out^


def tally_of(index: Int, slot: Int, r: WindowRecord) -> Tally:
    var t = Tally()
    t.specimens[slot] = 1
    t.sc_left[slot] = Int(r.left_all())
    t.sc_right[slot] = Int(r.right_all())
    t.sc_either[slot] = Int(r.coincidence_excludes())
    if r.first_pass > 0:
        t.first_pass_specimens[slot] = 1
        t.first_pass_pairs[slot] = r.first_pass
        t.first_pass_rows += [index, r.first_pass, r.rounds, r.survivors]
    if r.survivors > 0:
        t.survivor_specimens[slot] = 1
        t.components[slot] = len(r.components)
        t.found.append(index)
    if len(r.violations) > 0:
        t.violations.append(index)
    return t^


def _fields(s: OffCorpusSpecimen) -> String:
    return (
        s.specimen.json_fields() + ",\"sigma\":\"" + substitution_key(s.specimen.sigma) + "\""
        + ",\"class\":\"" + class_name(s.klass) + "\",\"synchronizing\":" + ("true" if s.synchronizing else "false")
    )


def main() raises:
    var args = argv()
    var L = Int(args[1]) if len(args) > 1 else 13
    var word_budget = Int(args[2]) if len(args) > 2 else 20000
    var domain = off_corpus_specimens()
    var start = Int(args[3]) if len(args) > 3 else 0
    var stop = Int(args[4]) if len(args) > 4 else len(domain)
    var stride = Int(args[5]) if len(args) > 5 else 1
    var passes = String(args[6]) if len(args) > 6 else String("domain+r3")
    if start < 0 or stop > len(domain) or start >= stop or stride <= 0:
        raise Error("slice outside the off-corpus list")
    if passes != "domain" and passes != "domain+r3" and passes != "all":
        raise Error("PASSES is domain, domain+r3 or all")
    var run_r3 = passes != "domain"
    var run_endpoint = passes == "all"

    var universe = k2_zero_universe(L)
    print("K2 = 0 window search: primitive substitutions on {0,1,2}, images of length 1..3, outside the PIP corpus")
    print("P_L (experiment A, complete): L =", L, " pairs", universe.size(), " K2 = 0 on every member:", universe.second_order_zero)
    var by_length = String("P_L by length:")
    for n in range(2, L + 1):
        if universe.count_of_length(n) > 0:
            by_length += " " + String(n) + ":" + String(universe.count_of_length(n))
    print(by_length)
    print("witness word budget", word_budget, " slice", start, stop, "stride", stride, " passes", passes)

    # The partition of the gate's table (stop/go §4.3 item 2), exactly.
    var pip = pip_corpus()
    var pip_nonsync = 0
    for s in range(len(pip)):
        if not is_synchronizing(pip[s].sigma):
            pip_nonsync += 1
    print("PARTITION PIP (not searched):", len(pip), " non-synchronizing", pip_nonsync)
    for klass in [CLASS_ONE_OUTSIDE, CLASS_BOTH_OUTSIDE, CLASS_REDUCIBLE]:
        var total = 0
        var nonsync = 0
        for s in range(len(domain)):
            if domain[s].klass == klass:
                total += 1
                if not domain[s].synchronizing:
                    nonsync += 1
        print("PARTITION", class_name(klass) + ":", total, " non-synchronizing", nonsync)

    var count = (stop - start + stride - 1) // stride

    def one(i: Int) {domain, universe, word_budget, start, stride, run_r3, run_endpoint} -> Tally:
        var s = start + i * stride
        var p = pass_of(domain[s])
        if (p == PASS_R3 and not run_r3) or (p == PASS_ENDPOINT and not run_endpoint):
            return Tally()
        try:
            var r = window_specimen(domain[s].specimen.sigma, domain[s].klass, domain[s].synchronizing, universe, word_budget)
            return tally_of(s, CLASS_COUNT * p + domain[s].klass, r)
        except:
            var t = Tally()
            t.failed.append(s)
            return t^

    var r = parallel_map_fold(one, merge, Tally(), count, WORKERS)
    if len(r.failed) > 0:
        for i in range(min(len(r.failed), 8)):
            print("WINDOW_FAILED", domain[r.failed[i]].specimen.label(), substitution_key(domain[r.failed[i]].specimen.sigma))
        var s = r.failed[0]
        _ = window_specimen(domain[s].specimen.sigma, domain[s].klass, domain[s].synchronizing, universe, word_budget)
        raise Error("window search: " + String(len(r.failed)) + " specimens raised")

    for p in range(PASS_COUNT):
        for klass in [CLASS_ONE_OUTSIDE, CLASS_BOTH_OUTSIDE, CLASS_REDUCIBLE]:
            var slot = CLASS_COUNT * p + klass
            if r.specimens[slot] == 0:
                continue
            print(
                "PASS", pass_name(p), class_name(klass), " specimens", r.specimens[slot],
                " strong coincidence: all left-witnessed", r.sc_left[slot], " all right-witnessed", r.sc_right[slot],
                " either (no strict system at all, verdict)", r.sc_either[slot],
                " | window L =", L, ": specimens with a first-pass survivor", r.first_pass_specimens[slot],
                " first-pass pairs", r.first_pass_pairs[slot], " nonempty limit", r.survivor_specimens[slot],
                " strict carriers", r.components[slot],
            )

    # One exact line per specimen with a first-pass survivor (the oracle input).
    for t in range(len(r.first_pass_rows) // 4):
        var s = r.first_pass_rows[4 * t]
        print(
            "WINDOW_SPECIMEN {" + _fields(domain[s]) + ",\"L\":" + String(L)
            + ",\"first_pass\":" + String(r.first_pass_rows[4 * t + 1]) + ",\"rounds\":" + String(r.first_pass_rows[4 * t + 2])
            + ",\"survivors\":" + String(r.first_pass_rows[4 * t + 3]) + "}"
        )

    # Every strict carrier found, as an exact record.
    for t in range(len(r.found)):
        var s = r.found[t]
        var rec = window_specimen(domain[s].specimen.sigma, domain[s].klass, domain[s].synchronizing, universe, word_budget)
        print("WINDOW_FOUND", domain[s].specimen.label(), substitution_key(domain[s].specimen.sigma), class_name(domain[s].klass),
              "survivors", rec.survivors, "carriers", len(rec.components), rec.violation_line())
        for c in range(len(rec.components)):
            emit_component("CCS", _fields(domain[s]), c, domain[s].specimen.sigma, rec.components[c])

    if len(r.violations) > 0:
        for i in range(len(r.violations)):
            var s = r.violations[i]
            var rec = window_specimen(domain[s].specimen.sigma, domain[s].klass, domain[s].synchronizing, universe, word_budget)
            print("VIOLATION", domain[s].specimen.label(), substitution_key(domain[s].specimen.sigma), class_name(domain[s].klass), rec.violation_line())
        raise Error("window search: " + String(len(r.violations)) + " specimens contradict a consistency check")
    print("consistency checks (Theorem A(4) and reversal, endpoint filter, R2, R3, R3'): no violations")

    var dom_specimens = 0
    var dom_sc = 0
    var dom_found = 0
    for klass in [CLASS_ONE_OUTSIDE, CLASS_REDUCIBLE]:
        dom_specimens += r.specimens[CLASS_COUNT * PASS_DOMAIN + klass]
        dom_sc += r.sc_either[CLASS_COUNT * PASS_DOMAIN + klass]
        dom_found += r.survivor_specimens[CLASS_COUNT * PASS_DOMAIN + klass]
    print("VERDICT (Theorem A(4) or its reversal): no strict system at all, any length, any K2:", dom_sc, "of", dom_specimens, "domain specimens")
    if dom_found == 0:
        print("WINDOW OBSERVATION (not a verdict): no strict system with K2 = 0 on every state and every state of length <=", L,
              "among", dom_specimens, "domain specimens")
    else:
        print("WINDOW OBSERVATION (not a verdict):", dom_found, "domain specimens carry a K2 = 0 strict system with all states of length <=", L)
    print("not searched: reducible strict systems with K2 != 0 (gate §0 row B3; the 28 pinned carriers of tests/test_c4_quotient_spectrum.mojo)")
