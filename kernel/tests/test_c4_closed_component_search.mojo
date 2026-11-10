"""Regression of the `K_2 = 0` window search off the PIP corpus.

Contract: docs/c4-closed-component-search-2026-11-07.md; gate
docs/c4-solidify-stop-go-2026-11-07.md §4.3, §4.5, §4.6, §4.7. Pinned:

* the exact partition of the gate's §4.3 table (class x endpoint flag) and
  the root classification it rests on, cross-checked against the Routh count
  `psc.pisot_screen.roots_outside_unit_circle` wherever that count decides
  (its three refused cubics are pinned);
* `P_L` is experiment A's complete `K_2 = 0` list (per-length counts, the six
  length-7 seeds), with exact lookups and fail-closed construction;
* the streamed child kernel agrees with the package's `children`;
* the fixed-point controls of gate §4.5: permutation substitutions keep all
  of `P_L` (the `cyc3Norm` system survives alone), `ex:nonpisot` keeps its
  four ordered `K_2 != 0` states (two normalised) with the filter off and
  loses them with it on;
* the find path: `emit_component`, `ordered_children` and `lift_size` on
  `cyc3Norm` (lift `m`) and `ex:nonpisot` (lift `2m`);
* the 28 pinned reducible carriers of `test_c4_quotient_spectrum.mojo`: every
  seed, indeed every one of their 123 ordered closure states, has
  `K_2 != 0`, so none lies in `P_L`, and the filter-off iteration keeps each
  closure whole;
* the budget-exhaustion control `(1, 2, 001)` reports `BUDGET_LENGTH`;
* every consistency violation name fires on a positive control, and a
  mislabelled class fails closed;
* the whole window domain and the R3 pass at `L = 11`, and the stride-21
  slice of both at `L = 13`, pinned.

The 28-carrier table is imported from `test_c4_quotient_spectrum` (resolved
by `run_tests.sh`'s `-I tests`), so the two tests read one table.
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import Mat3
from psc.bounded_bpa import BUDGET_LENGTH, build_bounded
from psc.bpa import children, sigma3, substitution_incidence
from psc.c4_cut_attractor import strict_closure
from psc.closed_component_search import (
    CLASS_BOTH_OUTSIDE,
    CLASS_NOT_PRIMITIVE,
    CLASS_ONE_OUTSIDE,
    CLASS_PIP,
    CLASS_REDUCIBLE,
    ImageTable,
    OffCorpusSpecimen,
    PairUniverse,
    carrier_violations,
    child_indices,
    coincidence_profile,
    component_automaton,
    conjugates_outside,
    core_automaton,
    det_power_below_perron,
    emit_component,
    first_pair_mask_of,
    greatest_fixed_point,
    is_synchronizing,
    k2_zero_universe,
    last_pair_mask_of,
    lift_size,
    off_corpus_specimens,
    ordered_children,
    r3prime_violation,
    specimen_class,
    specimen_violations,
    strict_carriers,
    universe_of,
    window_specimen,
    WindowComponent,
)
from psc.corpus import pip_corpus
from psc.defect_degree import DEGREE_FIVE_PLUS
from psc.pisot import CubicScreen
from psc.pisot_screen import ROUTH_UNDECIDED, roots_outside_unit_circle
from psc.seeds import length7_seeds
from psc.words import Pair, k2
from substitution_dynamics.balanced_pairs import normalise
from test_c4_quotient_spectrum import carriers


def _w(s: String) -> List[Int]:
    var out = List[Int]()
    for b in s.as_bytes():
        out.append(Int(b) - 48)
    return out^


def _sigma(a: String, b: String, c: String) -> List[List[Int]]:
    return [_w(a), _w(b), _w(c)]


def _k2_nonzero(p: Pair) -> Bool:
    var d = k2(p)
    for t in range(len(d)):
        if d[t] != 0:
            return True
    return False


def _class_of(sigma: List[List[Int]]) raises -> Int:
    var screen = CubicScreen()
    return specimen_class(screen, Mat3(substitution_incidence(sigma)))


def _raises_universe(max_length: Int, pairs: List[Pair]) -> Bool:
    try:
        _ = universe_of(max_length, pairs)
    except:
        return True
    return False


def test_domain_partition(domain: List[OffCorpusSpecimen]) raises:
    # gate §4.3 item 2, exactly: class sizes and non-synchronizing sizes
    assert_equal(len(domain), 28764)
    var total: List[Int] = [0, 0, 0, 0]
    var nonsync: List[Int] = [0, 0, 0, 0]
    var window = 0
    for s in range(len(domain)):
        total[domain[s].klass] += 1
        if not domain[s].synchronizing:
            nonsync[domain[s].klass] += 1
        if domain[s].in_window_domain():
            window += 1
        assert_equal(domain[s].specimen.index, s)
    assert_equal(total[CLASS_PIP], 0)
    assert_equal(total[CLASS_ONE_OUTSIDE], 3216)
    assert_equal(total[CLASS_BOTH_OUTSIDE], 3960)
    assert_equal(total[CLASS_REDUCIBLE], 21588)
    assert_equal(nonsync[CLASS_ONE_OUTSIDE], 1704)
    assert_equal(nonsync[CLASS_BOTH_OUTSIDE], 1812)
    assert_equal(nonsync[CLASS_REDUCIBLE], 10134)
    assert_equal(window, 1704 + 10134)
    var pip = pip_corpus()
    var pip_nonsync = 0
    for s in range(len(pip)):
        if not is_synchronizing(pip[s].sigma):
            pip_nonsync += 1
    assert_equal(len(pip), 4554)
    assert_equal(pip_nonsync, 1542)
    assert_equal(1542 + 1812 + 1704 + 10134, 15192)


def test_root_count_second_method(domain: List[OffCorpusSpecimen]) raises:
    # conjugates_outside (Sturm–Tarski) against psc.pisot_screen's Routh count
    # of |z| > 1, Perron root included, on every irreducible cubic of the
    # off-corpus list and of the PIP corpus: two exact in-library methods.
    # Where the Routh array hits a classical singularity it is undecided (no
    # evidence either way); those cases are pinned, and on them the
    # Sturm–Tarski count is the only exact method.
    var decided = 0
    var undecided = 0
    for s in range(len(domain)):
        if domain[s].klass != CLASS_ONE_OUTSIDE and domain[s].klass != CLASS_BOTH_OUTSIDE:
            continue
        var chi = domain[s].specimen.incidence.charpoly()
        assert_equal(conjugates_outside(chi), domain[s].klass)   # CLASS_ONE_OUTSIDE = 1, CLASS_BOTH_OUTSIDE = 2
        var routh = roots_outside_unit_circle(chi)
        if routh == ROUTH_UNDECIDED:
            assert_equal(chi, [-3, -6, 0, 1])                    # x^3 - 6x - 3, one-outside
            undecided += 1
            continue
        assert_equal(conjugates_outside(chi), routh - 1)
        decided += 1
    assert_equal(decided, 7158)
    assert_equal(undecided, 18)
    var pip = pip_corpus()
    var pip_decided = 0
    var pip_undecided = 0
    for s in range(len(pip)):
        var chi = pip[s].incidence.charpoly()
        assert_equal(conjugates_outside(chi), 0)
        var routh = roots_outside_unit_circle(chi)
        if routh == ROUTH_UNDECIDED:
            # x^3 - x^2 - 2x - 2 and x^3 - 2x^2 - x - 2: Pisot cubics the
            # Routh array refuses, like psc.pisot_screen's documented
            # x^3 - 3x^2 - 3x - 3 (a refusal is not a negative)
            assert_true(chi == [-2, -2, -1, 1] or chi == [-2, -1, -2, 1])
            pip_undecided += 1
            continue
        assert_equal(routh, 1)
        pip_decided += 1
    assert_equal(pip_decided, 4554 - 810)
    assert_equal(pip_undecided, 810)


def test_class_arithmetic() raises:
    # Tribonacci: Pisot, in the corpus
    assert_equal(conjugates_outside([-1, -1, -1, 1]), 0)
    assert_equal(_class_of(_sigma("01", "02", "0")), CLASS_PIP)
    # 12/0/20: chi = x^3 - x^2 - 2x + 1, roots ~ 1.80, -1.25, 0.445; det -1
    var s1 = _sigma("12", "0", "20")
    assert_equal(Mat3(substitution_incidence(s1)).charpoly(), [1, -2, -1, 1])
    assert_equal(conjugates_outside([1, -2, -1, 1]), 1)
    assert_equal(_class_of(s1), CLASS_ONE_OUTSIDE)
    assert_true(det_power_below_perron([1, -2, -1, 1], 1))
    # (1, 2, 001): chi = x^3 - x - 2, beta ~ 1.52, |alpha|^2 = 2 / beta > 1
    var s2 = _sigma("1", "2", "001")
    assert_equal(Mat3(substitution_incidence(s2)).charpoly(), [-2, -1, 0, 1])
    assert_equal(conjugates_outside([-2, -1, 0, 1]), 2)
    assert_equal(_class_of(s2), CLASS_BOTH_OUTSIDE)
    assert_false(det_power_below_perron([-2, -1, 0, 1], 1))
    # 1/22/011: chi = x^3 - 4x - 2, one-outside, |det| = 2 < beta ~ 2.21 < 4
    assert_equal(Mat3(substitution_incidence(_sigma("1", "22", "011"))).charpoly(), [-2, -4, 0, 1])
    assert_equal(_class_of(_sigma("1", "22", "011")), CLASS_ONE_OUTSIDE)
    assert_true(det_power_below_perron([-2, -4, 0, 1], 1))
    assert_false(det_power_below_perron([-2, -4, 0, 1], 2))
    # 01/02/111: chi = x^3 - x^2 - 4x + 3, one-outside, |det| = 3 > beta ~ 2.20
    assert_equal(Mat3(substitution_incidence(_sigma("01", "02", "111"))).charpoly(), [3, -4, -1, 1])
    assert_equal(_class_of(_sigma("01", "02", "111")), CLASS_ONE_OUTSIDE)
    assert_false(det_power_below_perron([3, -4, -1, 1], 1))
    # ex:nonpisot 1/012/1: chi = x (x - 2)(x + 1), reducible
    assert_equal(_class_of(_sigma("1", "012", "1")), CLASS_REDUCIBLE)
    var raised = False
    try:
        _ = conjugates_outside([0, -2, -1, 1])
    except:
        raised = True
    assert_true(raised)
    # permutation substitutions are not primitive
    assert_equal(_class_of(_sigma("1", "2", "0")), CLASS_NOT_PRIMITIVE)
    assert_equal(_class_of(_sigma("0", "1", "2")), CLASS_NOT_PRIMITIVE)
    # endpoint flags: Tribonacci's first letters are constant; 12/0/20 has the
    # first-letter map (1, 0, 2) and the last-letter map (2, 0, 0)
    assert_true(is_synchronizing(_sigma("01", "02", "0")))
    assert_false(is_synchronizing(s1))


def test_strong_coincidence() raises:
    # Tribonacci: every pair left-witnessed at level 1 (common first letter 0)
    var trib = coincidence_profile(_sigma("01", "02", "0"), 20000)
    assert_equal(trib.left, [1, 1, 1])
    assert_true(trib.excludes_strict_systems())
    # 12/0/20 within 20000 letters: only {1,2} is (right-)witnessed
    var p = coincidence_profile(_sigma("12", "0", "20"), 20000)
    assert_equal(p.left, [-1, -1, -1])
    assert_equal(p.right, [-1, -1, 1])
    assert_false(p.excludes_strict_systems())
    # 112/0/1: every pair left-witnessed, deep (levels 14, 1, 15): a verdict
    var deep = coincidence_profile(_sigma("112", "0", "1"), 20000)
    assert_equal(deep.left, [14, 1, 15])
    assert_equal(deep.right, [13, 12, 14])
    assert_true(deep.excludes_strict_systems())
    # 10/102/211 (a pinned strict carrier's specimen): left [1, -1, -1], right [-1, -1, 2]
    var carrier = coincidence_profile(_sigma("10", "102", "211"), 20000)
    assert_equal(carrier.left, [1, -1, -1])
    assert_equal(carrier.right, [-1, -1, 2])
    # ... and its strict closure avoids them (Theorem A(4) and its reversal):
    # first-letter pairs {1,2} only, last-letter pairs {0,1}, {0,2}
    var closure = strict_closure(_sigma("10", "102", "211"), Pair(_w("102"), _w("210")))
    assert_equal(closure.size(), 4)
    assert_equal(first_pair_mask_of(closure.states), 4)
    assert_equal(first_pair_mask_of(closure.states), closure.first_pair_mask())
    assert_equal(last_pair_mask_of(closure.states), 3)
    assert_equal(first_pair_mask_of(closure.states) & carrier.left_mask(), 0)
    assert_equal(last_pair_mask_of(closure.states) & carrier.right_mask(), 0)
    # a word budget below one image length leaves every pair undecided
    var tiny = coincidence_profile(_sigma("12", "0", "20"), 1)
    assert_equal(tiny.left, [-1, -1, -1])
    assert_equal(tiny.right, [-1, -1, -1])
    var raised = False
    try:
        _ = coincidence_profile(_sigma("12", "0", "20"), 0)
    except:
        raised = True
    assert_true(raised)


def test_universe_is_experiment_a() raises:
    var u = k2_zero_universe(10)
    assert_true(u.second_order_zero)
    assert_equal(u.size(), 6 + 24 + 198 + 1230)
    for n in range(2, 7):
        assert_equal(u.count_of_length(n), 0)
    assert_equal(u.count_of_length(7), 6)
    assert_equal(u.count_of_length(8), 24)
    assert_equal(u.count_of_length(9), 198)
    assert_equal(u.count_of_length(10), 1230)
    # the six length-7 members are the six seeds of psc.seeds
    var seeds = length7_seeds()
    for i in range(len(seeds)):
        var j = u.index_of(seeds[i])
        assert_true(j >= 0)
        assert_true(u.pair(j) == normalise(seeds[i]))
        assert_equal(u.index_of(Pair(seeds[i].v, seeds[i].u)), j)
    # every member is found at its own index
    for i in range(u.size()):
        assert_equal(u.index_of(u.pair(i)), i)
    # a K2 != 0 irreducible pair is not a member
    assert_equal(u.index_of(Pair(_w("012"), _w("120"))), -1)
    # fail closed on construction
    var good = Pair(_w("0112201"), _w("1200112"))
    assert_false(_raises_universe(7, [good.copy()]))
    assert_true(_raises_universe(7, [good.copy(), good.copy()]))           # duplicate
    assert_true(_raises_universe(7, [Pair(good.v, good.u)]))             # not normalised
    assert_true(_raises_universe(7, [Pair(_w("0110"), _w("1001"))]))     # reducible
    assert_true(_raises_universe(6, [good.copy()]))                      # too long
    assert_true(_raises_universe(7, [Pair(_w("00"), _w("00"))]))         # coincident
    assert_true(_raises_universe(40, [good.copy()]))                     # beyond the code range


def _check_against_package(sigma: List[List[Int]], u: PairUniverse) raises -> Int:
    """Every member: `child_indices` succeeds iff every package child is a
    member, and then lists them in factor order. Returns the successes."""
    var images = ImageTable(sigma)
    var out = List[Int]()
    var ok = 0
    for i in range(u.size()):
        var got = child_indices(images, u, i, out)
        var cs = children(sigma, u.pair(i))
        var expect = List[Int]()
        var all_in = True
        for c in range(len(cs)):
            var j = -1 if cs[c].is_coincidence() else u.index_of(cs[c])
            if j < 0:
                all_in = False
            expect.append(j)
        assert_equal(got, all_in)
        if got:
            assert_equal(out, expect)
            ok += 1
    return ok


def test_streamed_children_match_package() raises:
    var u = k2_zero_universe(11)
    assert_equal(_check_against_package(_sigma("0", "1", "2"), u), u.size())
    assert_equal(_check_against_package(_sigma("1", "2", "0"), u), u.size())
    # one-outside and reducible domain specimens with first-pass survivors at L = 11
    assert_equal(_check_against_package(_sigma("12", "0", "20"), u), 1)
    assert_equal(_check_against_package(_sigma("112", "0", "1"), u), 2)
    assert_equal(_check_against_package(_sigma("10", "102", "211"), u), 0)
    assert_equal(_check_against_package(_sigma("01", "02", "0"), u), 0)


def test_fixed_point_controls() raises:
    var u = k2_zero_universe(9)
    # permutation substitutions keep all of P_L (each pair's only child is a relabelling)
    var ident = greatest_fixed_point(_sigma("0", "1", "2"), u)
    assert_equal(ident.survivors(), u.size())
    var cyc = greatest_fixed_point(_sigma("1", "2", "0"), u)
    assert_equal(cyc.first_pass, u.size())
    assert_equal(cyc.survivors(), u.size())
    assert_equal(cyc.rounds, 0)
    # cyc3Norm (Lean SectorBridge): wTPair and its two relabellings, alone
    var w = Pair(_w("0112201"), _w("1200112"))
    var t1 = Pair(_w("1220012"), _w("2011220"))
    var t2 = Pair(_w("0122001"), _w("2001120"))
    var cu = universe_of(7, [w.copy(), t1.copy(), t2.copy()])
    var core = greatest_fixed_point(_sigma("1", "2", "0"), cu)
    assert_equal(core.survivors(), 3)
    var a = core_automaton(cu, core)
    var carriers_found = strict_carriers(a)
    assert_equal(len(carriers_found), 1)
    assert_equal(len(carriers_found[0]), 3)
    var states = List[Pair]()
    for s in range(3):
        states.append(a.states[carriers_found[0][s]].copy())
    var comp = WindowComponent(_sigma("1", "2", "0"), states^)
    assert_equal(comp.ordered_size, 3)
    assert_equal(comp.degree, 3)
    assert_equal(comp.longest, 7)
    # the find path: the exact record of a carrier, on cyc3Norm in the order
    # (wTPair, t1, t2). sigma(w) = t1, sigma(t1) = swap(t2), sigma(t2) =
    # swap(w): one child each, at k = 0, orientations 0, 1, 1; the lift from
    # w is {w, t1, swap(t2)}, of size 3 = m (an even number of swaps)
    var fixed = WindowComponent(_sigma("1", "2", "0"), [w.copy(), t1.copy(), t2.copy()])
    assert_equal(fixed.ordered_size, 3)
    assert_equal(fixed.first_mask, 7)           # first letters {0,1} (w), {1,2} (t1), {0,2} (t2)
    var rows = ordered_children(_sigma("1", "2", "0"), component_automaton(_sigma("1", "2", "0"), fixed.states))
    assert_equal(rows, [0, 0, 1, 0, 1, 0, 2, 1, 2, 0, 0, 1])
    assert_equal(lift_size(3, rows), 3)
    emit_component("CCS_TEST", "\"sigma\":\"1/2/0\"", 0, _sigma("1", "2", "0"), fixed)
    # the same three states lose a member when one is missing: a removal round
    var partial = universe_of(7, [w.copy(), t1.copy()])
    var gone = greatest_fixed_point(_sigma("1", "2", "0"), partial)
    assert_equal(gone.first_pass, 1)
    assert_equal(gone.rounds, 1)
    assert_equal(gone.survivors(), 0)
    # ex:nonpisot 1/012/1: its strict closure of (01, 10), four ordered states
    var ex = _sigma("1", "012", "1")
    var closure = strict_closure(ex, Pair(_w("01"), _w("10")))
    assert_equal(closure.size(), 4)
    var normal = List[Pair]()
    for t in range(closure.size()):
        var q = normalise(closure.states[t])
        var known = False
        for s in range(len(normal)):
            if normal[s] == q:
                known = True
        if not known:
            normal.append(q^)
        assert_true(_k2_nonzero(closure.states[t]))
        assert_equal(u.index_of(closure.states[t]), -1)   # filter on: not in P_L
    assert_equal(len(normal), 2)                            # (01, 10) and (12, 21)
    var off = universe_of(4, normal)
    var kept = greatest_fixed_point(ex, off)                # filter off: all kept
    assert_equal(kept.survivors(), 2)
    assert_false(off.second_order_zero)
    # the find path on a double cover: m = 2 normalised states, ordered lift 4
    var double = WindowComponent(ex, normal.copy())
    assert_equal(double.ordered_size, 4)
    assert_equal(double.degree, 2)
    assert_equal(lift_size(2, ordered_children(ex, component_automaton(ex, double.states))), 4)
    emit_component("CCS_TEST", "\"sigma\":\"1/012/1\"", 1, ex, double)
    # filter on, the window of ex:nonpisot at L = 9 is empty
    assert_equal(greatest_fixed_point(ex, u).survivors(), 0)
    # a supplied component that is not closed raises
    var raised = False
    try:
        _ = component_automaton(_sigma("1", "2", "0"), [w.copy()])
    except:
        raised = True
    assert_true(raised)


def test_pinned_carriers_have_k2_nonzero_seeds() raises:
    # gate §0 row B3: the 28 class representatives of test_c4_quotient_spectrum
    var cs = carriers()
    assert_equal(len(cs), 28)
    var u = k2_zero_universe(9)
    var ordered_states = 0
    var in_window_domain = 0
    for k in range(len(cs)):
        var seed = Pair(cs[k].u, cs[k].v)
        assert_true(_k2_nonzero(seed))
        assert_equal(_class_of(cs[k].sigma), CLASS_REDUCIBLE)
        if not is_synchronizing(cs[k].sigma):
            in_window_domain += 1
        var closure = strict_closure(cs[k].sigma, seed)
        assert_equal(closure.size(), cs[k].size)
        ordered_states += closure.size()
        var normal = List[Pair]()
        var longest = 2
        for t in range(closure.size()):
            assert_true(_k2_nonzero(closure.states[t]))
            if closure.states[t].length() <= u.max_length:
                assert_equal(u.index_of(closure.states[t]), -1)
            longest = max(longest, closure.states[t].length())
            var q = normalise(closure.states[t])
            var known = False
            for s in range(len(normal)):
                if normal[s] == q:
                    known = True
            if not known:
                normal.append(q^)
        # filter off: the iteration seeded with the carrier's own states keeps them all
        var off = universe_of(longest, normal)
        assert_equal(greatest_fixed_point(cs[k].sigma, off).survivors(), len(normal))
        # filter on: the K2 = 0 window of the same specimen is empty at L = 9
        assert_equal(greatest_fixed_point(cs[k].sigma, u).survivors(), 0)
    assert_equal(ordered_states, 123)
    assert_equal(in_window_domain, 28)


def test_budget_exhaustion_control() raises:
    # gate §4.5: swap-seeded closures of (1, 2, 001), chi = x^3 - x - 2, never close
    var b = build_bounded(sigma3(_sigma("1", "2", "001")), 20000, 1000)
    assert_equal(b.exhausted, BUDGET_LENGTH)
    assert_true(b.graph.capped)


def _has(violations: List[String], name: String) -> Bool:
    for v in range(len(violations)):
        if violations[v] == name:
            return True
    return False


def test_consistency_checks_are_named() raises:
    var u = k2_zero_universe(9)
    var cyc = _sigma("1", "2", "0")
    # a nonempty limit labelled both-outside and synchronizing is named, twice
    var r = window_specimen(cyc, CLASS_BOTH_OUTSIDE, True, u, 20000)
    assert_equal(r.survivors, u.size())
    assert_true(len(r.components) > 0)
    assert_true(_has(r.violations, "R3"))
    assert_true(_has(r.violations, "endpoint"))
    assert_false(_has(r.violations, "A4-all-pairs"))
    assert_false(r.coincidence_excludes())
    # labelled reducible and non-synchronizing it is a clean (non-primitive) find
    var clean = window_specimen(cyc, CLASS_REDUCIBLE, False, u, 20000)
    assert_equal(len(clean.violations), 0)
    # labelled one-outside, the R3' check needs an irreducible cubic: fail closed
    var raised = False
    try:
        _ = window_specimen(cyc, CLASS_ONE_OUTSIDE, False, u, 20000)
    except:
        raised = True
    assert_true(raised)
    # an erasing substitution is refused
    var erasing = False
    try:
        _ = window_specimen(_sigma("01", "", "2"), CLASS_REDUCIBLE, False, u, 20000)
    except:
        erasing = True
    assert_true(erasing)


def _r3prime_raises(chi: List[Int], degree: Int) -> Bool:
    try:
        _ = r3prime_violation(chi, degree)
    except:
        return True
    return False


def test_every_violation_name_fires() raises:
    # Positive controls: no carrier was found in any run, so each named check
    # is shown to fire here, on the real path where an input exists and on
    # the factored check functions otherwise.
    # (a) real path: ex:nonpisot 1/012/1 with the universe of its two
    # normalised K2 != 0 states, mislabelled both-outside: R3 and R2 fire;
    # its first- and last-letter pairs carry no witness (Theorem A(4))
    var ex = _sigma("1", "012", "1")
    var off = universe_of(4, [Pair(_w("01"), _w("10")), Pair(_w("12"), _w("21"))])
    var r = window_specimen(ex, CLASS_BOTH_OUTSIDE, False, off, 20000)
    assert_equal(r.survivors, 2)
    assert_equal(len(r.components), 1)
    assert_equal(r.components[0].degree, 2)
    assert_equal(r.violations, ["R3", "R2"])
    # labelled reducible, it is clean; labelled one-outside, the R3' check
    # refuses the reducible cubic x (x - 2)(x + 1) whatever the degree
    assert_equal(len(window_specimen(ex, CLASS_REDUCIBLE, False, off, 20000).violations), 0)
    var raised = False
    try:
        _ = window_specimen(ex, CLASS_ONE_OUTSIDE, False, off, 20000)
    except:
        raised = True
    assert_true(raised)
    # (b) specimen-level checks
    assert_equal(specimen_violations(CLASS_REDUCIBLE, False, False), List[String]())
    assert_equal(specimen_violations(CLASS_ONE_OUTSIDE, False, True), ["A4-all-pairs"])
    assert_equal(specimen_violations(CLASS_REDUCIBLE, True, False), ["endpoint"])
    assert_equal(specimen_violations(CLASS_BOTH_OUTSIDE, True, True), ["A4-all-pairs", "endpoint", "R3"])
    # (c) R3' on real one-outside cubics: 12/0/20 (|det| = 1 < beta),
    # 1/22/011 (|det| = 2 < beta), 01/02/111 (|det| = 3 > beta)
    var unimodular: List[Int] = [1, -2, -1, 1]
    var det2: List[Int] = [-2, -4, 0, 1]
    var det3: List[Int] = [3, -4, -1, 1]
    assert_equal(r3prime_violation(unimodular, 2), "R3prime-degree")
    assert_equal(r3prime_violation(unimodular, 3), "")
    assert_equal(r3prime_violation(unimodular, 4), "")
    assert_equal(r3prime_violation(det2, 3), "")
    assert_equal(r3prime_violation(det2, 4), "R3prime-unimodular")
    assert_equal(r3prime_violation(det3, 3), "R3prime-det-power")
    assert_equal(r3prime_violation(det3, 4), "R3prime-unimodular")
    assert_equal(r3prime_violation(det3, DEGREE_FIVE_PLUS), "")
    assert_true(_r3prime_raises([0, -2, -1, 1], 3))           # reducible: every branch refuses
    assert_true(_r3prime_raises([0, -2, -1, 1], 2))
    assert_true(_r3prime_raises([0, -2, -1, 1], DEGREE_FIVE_PLUS))
    assert_true(_r3prime_raises(unimodular, 1))
    # (d) carrier-level checks (masks in pair_bit order {0,1}=1, {0,2}=2, {1,2}=4)
    assert_equal(carrier_violations(CLASS_REDUCIBLE, det3, 1, 2, 4, 1, 2), List[String]())
    assert_equal(carrier_violations(CLASS_REDUCIBLE, det3, 4, 0, 4, 7, 3), ["A4-left"])
    assert_equal(carrier_violations(CLASS_REDUCIBLE, det3, 0, 2, 7, 2, 3), ["A4-right"])
    assert_equal(carrier_violations(CLASS_BOTH_OUTSIDE, det3, 0, 0, 7, 7, 2), ["R2"])
    assert_equal(carrier_violations(CLASS_BOTH_OUTSIDE, det3, 0, 0, 7, 7, 3), List[String]())
    assert_equal(carrier_violations(CLASS_ONE_OUTSIDE, det3, 0, 0, 7, 7, 2), ["R2", "R3prime-degree"])
    assert_equal(carrier_violations(CLASS_ONE_OUTSIDE, det3, 0, 0, 7, 7, 3), ["R3prime-det-power"])
    assert_equal(carrier_violations(CLASS_ONE_OUTSIDE, det2, 0, 0, 7, 7, 4), ["R3prime-unimodular"])
    assert_equal(carrier_violations(CLASS_ONE_OUTSIDE, unimodular, 3, 4, 3, 4, 4), ["A4-left", "A4-right"])


def test_window_at_eleven(domain: List[OffCorpusSpecimen]) raises:
    # the whole window domain and the R3 pass at L = 11, serially
    var u = k2_zero_universe(11)
    assert_equal(u.size(), 9102)
    var specimens: List[Int] = [0, 0, 0, 0]
    var sc: List[Int] = [0, 0, 0, 0]
    var first_specimens: List[Int] = [0, 0, 0, 0]
    var first_pairs: List[Int] = [0, 0, 0, 0]
    var nonempty = 0
    for s in range(len(domain)):
        var r3 = not domain[s].synchronizing and domain[s].klass == CLASS_BOTH_OUTSIDE
        if not domain[s].in_window_domain() and not r3:
            continue
        var r = window_specimen(domain[s].specimen.sigma, domain[s].klass, domain[s].synchronizing, u, 20000)
        assert_equal(len(r.violations), 0)
        specimens[domain[s].klass] += 1
        sc[domain[s].klass] += Int(r.coincidence_excludes())
        if r.first_pass > 0:
            first_specimens[domain[s].klass] += 1
            first_pairs[domain[s].klass] += r.first_pass
        if r.survivors > 0:
            nonempty += 1
    assert_equal(specimens, [0, 1704, 1812, 10134])
    assert_equal(sc, [0, 456, 216, 5298])
    assert_equal(first_specimens, [0, 12, 48, 24])
    assert_equal(first_pairs, [0, 12, 108, 36])
    assert_equal(nonempty, 0)


def test_window_at_thirteen_slice(domain: List[OffCorpusSpecimen]) raises:
    # the headline length, on the stride-21 slice of the off-corpus list
    # (domain and R3 passes; driver `13 20000 0 28764 21 domain+r3`, replayed
    # whole by the oracle's `window 13 0 28764 21`)
    var u = k2_zero_universe(13)
    assert_equal(u.size(), 382782)
    assert_equal(u.count_of_length(12), 50406)
    assert_equal(u.count_of_length(13), 323274)
    var specimens: List[Int] = [0, 0, 0, 0]
    var sc: List[Int] = [0, 0, 0, 0]
    var first_specimens: List[Int] = [0, 0, 0, 0]
    var first_pairs: List[Int] = [0, 0, 0, 0]
    var nonempty = 0
    for s in range(0, len(domain), 21):
        var r3 = not domain[s].synchronizing and domain[s].klass == CLASS_BOTH_OUTSIDE
        if not domain[s].in_window_domain() and not r3:
            continue
        var r = window_specimen(domain[s].specimen.sigma, domain[s].klass, domain[s].synchronizing, u, 20000)
        assert_equal(len(r.violations), 0)
        specimens[domain[s].klass] += 1
        sc[domain[s].klass] += Int(r.coincidence_excludes())
        if r.first_pass > 0:
            first_specimens[domain[s].klass] += 1
            first_pairs[domain[s].klass] += r.first_pass
            assert_equal(r.rounds, 1)
        if r.survivors > 0:
            nonempty += 1
    assert_equal(specimens, [0, 99, 80, 478])
    assert_equal(sc, [0, 28, 9, 265])
    assert_equal(first_specimens, [0, 9, 8, 15])
    assert_equal(first_pairs, [0, 21, 135, 48])
    assert_equal(nonempty, 0)


def main() raises:
    var domain = off_corpus_specimens()
    test_domain_partition(domain)
    test_root_count_second_method(domain)
    test_class_arithmetic()
    test_strong_coincidence()
    test_universe_is_experiment_a()
    test_streamed_children_match_package()
    test_fixed_point_controls()
    test_pinned_carriers_have_k2_nonzero_seeds()
    test_budget_exhaustion_control()
    test_consistency_checks_are_named()
    test_every_violation_name_fires()
    test_window_at_eleven(domain)
    test_window_at_thirteen_slice(domain)
    print("test_c4_closed_component_search: ok")
    require_contract("K2 = 0 window search off the PIP corpus (gate docs/c4-solidify-stop-go-2026-11-07.md §4.6): the partition one-outside 3216 / both-outside 3960 / reducible 21588 with non-synchronizing 1704 / 1812 / 10134 (PIP 4554 / 1542), its Sturm–Tarski root count equal to the Routh count of psc.pisot_screen wherever that decides (7158 of 7176 off-corpus irreducible specimens, 3744 of 4554 PIP; it refuses x^3 - 6x - 3 and two PIP cubics); P_L is experiment A's complete K2 = 0 list (7:6 8:24 9:198 10:1230 11:7644, P_13 = 382782 with 12:50406 13:323274); the streamed children equal the package's; permutation substitutions keep all of P_L, cyc3Norm survives alone, ex:nonpisot keeps its four ordered K2 != 0 states (two normalised) with the filter off and loses them with it on; the exact record of a found carrier (ordered child rows, lift size m or 2m) on cyc3Norm and ex:nonpisot; the 28 pinned reducible carriers have K2 != 0 on every seed and on all 123 ordered closure states; (1, 2, 001) exhausts BUDGET_LENGTH; every consistency violation name (A4-all-pairs, A4-left, A4-right, endpoint, R2, R3, R3prime-degree, R3prime-det-power, R3prime-unimodular) fires on a positive control and a reducible cubic labelled one-outside raises; at L = 11 the window domain and the both-outside R3 pass have empty limits (strong-coincidence verdicts 456 / 216 / 5298, first-pass survivors in 12 / 48 / 24 specimens); on the stride-21 slice at L = 13 (99 / 80 / 478 specimens) the limits are empty (first-pass survivors in 9 / 8 / 15 specimens, 21 / 135 / 48 pairs, one removal round each); window statements are observations, never verdicts")
