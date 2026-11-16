"""Exact regression for the two FC3 families (psc.c4_fc3_family).

docs/c4-fc3-family-2026-11-16.md. The families

    sigma_{r,s,n} = (1^r, 0 1^n 2, 0 1^s),      tau_n = (1, 2 1^n 0, 0 1)

are pinned on a finite grid; the statement for all parameters is the
recorded proof of the note (not machine-checked, independent human review
pending), and nothing here proves it.

Grid. `sigma_{r,s,n}` for `1 <= r <= 5`, `0 <= s <= 2`, `1 <= n <= 3r+s+6`
(240 members: everything below the PIP3 threshold `r+s+1`, the range between
it and the (F) threshold `3r+s`, and seven values of `n` from `3r+s` on), and
`tau_n` for `1 <= n <= 16`.

Asserted from the note (closed forms and its lists), member by member:

(i)   the image words; `det M = r`, `tr M = n`, `e_2(M) = -(r+s)`,
      `chi = t^3 - n t^2 - (r+s) t - r`; primitivity; `psc.pisot` accepts
      every member with `n >= r+s+1` and every `tau_n`, with
      `chi(n) < 0 < chi(n+1)`;
(ii)  the endpoint maps `g = (1,0,0)`, `g_R = (1,2,1)` (`s >= 1`) or
      `(1,2,0)` (`s = 0`), for `tau_n` `g = (1,2,0)`, `g_R = (1,0,1)`, and the
      numbers of periodic letters;
(iii) `dim H^1 = 4` (`s >= 1`), `5` (`s = 0`, `tau_n`);
(iv)  (F) at every grid member with `n >= 3r+s` and at every `tau_n`; (F)
      at the small members the note decides one by one; the six members it
      lists as failing (F), with the number and periods of their interior
      cycles;
(v)   clauses (b), (c) and membership in the non-trivial part of the FC3
      class, as the note states them;
(vi)  the least strong-coincidence levels on the ranges the note states,
      and its explicit witnesses on the literal words.

Pinned from the exact computation here, where the note gives no value: what
the screens say below `n = r+s+1` (20 members rejected); the members where
the Routh screen refuses; the complete list of grid members failing (F) (ten,
four beyond the six of the note); the base states and address data of their
interior cycles; the certified radii; the transients of the trapped states;
the witness levels off the stated ranges.

Which decision is which. `psc.c4_geometric_f.decide_geometric_f` and
`fc3_profile` are certified for images of at most six letters and refuse the
rest: of the 105 grid members with `n >= 3r+s` they accept three
(`sigma_{1,0,3}`, `sigma_{1,0,4}`, `sigma_{1,1,4}`), and no `tau_n` with
`n >= 5`. Those refusals are asserted. Beyond six letters (F) is decided by
`psc.c4_fc3_family.decide_f_screened` (the box of `stable_radii` on the
coefficient-screened tables, walked with `psc.leftmost_chain.leftmost_step`).
What guards that decision:

- on every standing corpus specimen (4,554; three letters at most, both
  decisions exist) the screened walk in the canonical box returns the
  canonical interior cycles, and on every 23rd `decide_f_screened` end to
  end returns the canonical verdict and radii;
- on the 44 grid members of at most six letters it returns the canonical
  verdict, radii and cycle periods, the ten failures included;
- its radii on the long-image members are pinned, and twice the radii hold
  no further cycle on any of them;
- on six long-image members the literal box graph of Corollary LC5
  (`build_box_graph`, independent radii, no code of `psc.c4_fc3_family`) has
  no terminal leftmost cycle.

Not pinned and not claimed: anything for parameters off the grid; the
trapping lemma of the written proof; the conclusion `cr = 1` of Theorem FC3
(conditional on its imports); pure discrete spectrum; any new C4 case (the
witnesses of (vi) make C4 elementary on the families); relations between
members by powers. No claim status changes.

Run time: about a minute and a half on one core (the corpus calibration is
half of it).

Replay:
`cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_fc3_family.mojo`
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import Mat3
from psc import pisot_screen
from psc.bpa import apply_substitution, substitution_incidence
from psc.c4_fc3_family import (
    FAMILY_MAX_PARAMETER,
    FamilyFDecision,
    checked_charpoly,
    clause_b,
    clause_c,
    decide_f_audited,
    decide_f_screened,
    decide_family_f,
    eval_cubic,
    family_charpoly,
    family_facts,
    family_fc3_profile,
    interior_periods_in_box,
    longest_image,
    nontrivial_fc3_member,
    screened_fc3_profile,
    sigma_family,
    sigma_kappa_sign,
    sigma_trapping_sign,
    tau_family,
    tau_trapping_sign,
    trapped_transients,
    within_audited_domain,
)
from psc.c4_geometric_f import (
    FC3Profile,
    OrbitMemo,
    PrototileMap,
    PrototileState,
    StableRadiiCache,
    decide_geometric_f,
    decide_geometric_f_with,
    fc3_profile,
    interior_address,
)
from psc.closed_component_search import coincidence_profile
from psc.coincidence_formula import coincidence_level
from psc.corpus import pip_corpus
from psc.field3 import discriminant
from psc.leftmost_chain import terminal_leftmost_cycles
from psc.overlap_seed_patch import build_seed_overlap_tables_screened
from psc.pisot import is_irreducible_cubic, is_pisot_charpoly, is_primitive
from psc.symmetry import canonical_substitution, reversed_substitution, substitution_key
from psc.vertex_coincidence import build_box_graph

# The grid.
comptime R_MAX = 5
comptime S_MAX = 2
comptime N_EXTRA = 6
comptime TAU_MAX = 16

# Word budget of the literal witness search and the longest image for which
# the coincidence automaton is also run. The automaton is exact at every
# length; it is slow on some long-image members (about 26 s for the six pair
# questions of sigma_{5,2,17}).
comptime WITNESS_WORD_BUDGET = 2000000
comptime AUTOMATON_IMAGE_BOUND = 14

# Step budget of the trapped-state replay.
comptime TRAP_STEPS = 64

# Every CORPUS_STRIDE-th corpus specimen runs `decide_f_screened` end to end
# (its own `stable_radii`); every specimen runs the screened walk in the
# canonical box.
comptime CORPUS_STRIDE = 23

# Range of the first coordinate scanned when the trapped states are listed
# through the canonical `PrototileMap` (see `_canonical_trap`).
comptime TRAP_SCAN = 80


def _name(r: Int, s: Int, n: Int) -> String:
    return "(" + String(r) + "," + String(s) + "," + String(n) + ")"


def _joined(values: List[Int]) -> String:
    var out = String("")
    for i in range(len(values)):
        if i > 0:
            out += ","
        out += String(values[i])
    return out


def _state_text(s: PrototileState) -> String:
    return "(" + String(s.letter) + ";" + String(s.v0) + "," + String(s.v1) + "," + String(s.v2) + ")"


def _is_run(w: List[Int], start: Int, stop: Int, letter: Int) -> Bool:
    for k in range(start, stop):
        if w[k] != letter:
            return False
    return True


def _audited_refuses(sigma: List[List[Int]], expected: String) -> Bool:
    """`decide_geometric_f` refuses `sigma` with a message containing
    `expected`; any other outcome is not the refusal under test."""
    try:
        _ = decide_geometric_f(sigma)
        return False
    except e:
        return expected in String(e)


def _profile_refuses(sigma: List[List[Int]], expected: String) -> Bool:
    try:
        _ = fc3_profile(sigma)
        return False
    except e:
        return expected in String(e)


def _screened_refuses(sigma: List[List[Int]], expected: String) -> Bool:
    try:
        _ = decide_f_screened(sigma)
        return False
    except e:
        return expected in String(e)


def _screened_profile_refuses(sigma: List[List[Int]], expected: String) -> Bool:
    try:
        _ = screened_fc3_profile(sigma)
        return False
    except e:
        return expected in String(e)


def _sorted(values: List[Int]) -> List[Int]:
    var out = values.copy()
    for i in range(1, len(out)):
        var x = out[i]
        var j = i
        while j > 0 and out[j - 1] > x:
            out[j] = out[j - 1]
            j -= 1
        out[j] = x
    return out^


def _canonical_trap(sigma: List[List[Int]], c_lo: Int) raises -> List[Int]:
    """`[states, longest, absorbed]` over the states `(j, (a, b, c))`,
    `(a, b, c) != 0`, `b` in `{0,1}`, `c_lo <= c <= 1`, through the canonical
    state map: `PrototileMap.is_state` and `OrbitMemo.transient`, which
    returns `-1` when the orbit enters an interior cycle of the verdict. For
    images of at most six letters only.

    For fixed `(b, c)` the position `a ell_0 + b ell_1 + c ell_2` increases
    with `a`. It is negative at `a = -TRAP_SCAN` and beyond every tile at
    `a = TRAP_SCAN` (both asserted), so every state has `|a| < TRAP_SCAN`."""
    var m = PrototileMap(sigma)
    var boxes = StableRadiiCache()
    var verdict = decide_geometric_f_with(m, boxes)
    var memo = OrbitMemo(verdict)
    var states = 0
    var longest = 0
    var absorbed = 0
    for b in range(0, 2):
        for c in range(c_lo, 2):
            assert_true(m.sign(m.position(PrototileState(0, -TRAP_SCAN, b, c))) < 0)
            assert_true(m.sign(m.position(PrototileState(0, TRAP_SCAN, b, c))) > 0)
            for j in range(3):
                assert_false(m.is_state(PrototileState(j, TRAP_SCAN, b, c)))
            for a in range(-TRAP_SCAN + 1, TRAP_SCAN):
                for j in range(3):
                    var state = PrototileState(j, a, b, c)
                    if state.is_vertex() or not m.is_state(state):
                        continue
                    states += 1
                    var steps = memo.transient(m, state)
                    if steps < 0:
                        absorbed += 1
                    elif steps > longest:
                        longest = steps
    return [states, longest, absorbed]


def _automaton_levels(sigma: List[List[Int]]) raises -> List[Int]:
    return [coincidence_level(sigma, 0, 1), coincidence_level(sigma, 0, 2), coincidence_level(sigma, 1, 2)]


def _power_images(sigma: List[List[Int]], level: Int) -> List[List[Int]]:
    """`sigma^level(a)` for the three letters, as literal words."""
    var out = List[List[Int]]()
    for a in range(3):
        var w: List[Int] = [a]
        for _ in range(level):
            w = apply_substitution(sigma, w)
        out.append(w^)
    return out^


def _is_witness(images: List[List[Int]], a: Int, b: Int, length: Int, parikh: List[Int], letter: Int) -> Bool:
    """The two words `images[a]`, `images[b]` carry `letter` at index `length`
    after prefixes whose Parikh vector is `parikh`: a strong-coincidence
    witness, read off the literal words."""
    if length < 0 or length >= len(images[a]) or length >= len(images[b]):
        return False
    if images[a][length] != letter or images[b][length] != letter:
        return False
    var top: List[Int] = [0, 0, 0]
    var bottom: List[Int] = [0, 0, 0]
    for k in range(length):
        top[images[a][k]] += 1
        bottom[images[b][k]] += 1
    return top == parikh and bottom == parikh


def _check_sigma_witnesses(sigma: List[List[Int]], r: Int, s: Int, n: Int) raises:
    """The explicit witnesses of Proposition 5 for `sigma_{r,s,n}`, on the
    literal words: left for `n >= r + 1`, right for `s >= 1` and `n >= s`
    (suffixes are prefixes of the reversed substitution)."""
    var level1 = _power_images(sigma, 1)
    var level2 = _power_images(sigma, 2)
    var level3 = _power_images(sigma, 3)
    var zero: List[Int] = [0, 0, 0]
    var prefix: List[Int] = [1, r, 0]
    # {1,2}: both images begin with 0.
    assert_true(_is_witness(level1, 1, 2, 0, zero, 0))
    # {0,1}: prefixes 0 1^r of sigma^2(0) and 1^r 0 of sigma^2(1), then 1.
    assert_true(_is_witness(level2, 0, 1, r + 1, prefix, 1))
    # {0,2}: the same prefixes, at level 2 for s >= 1 and level 3 for s = 0.
    if s >= 1:
        assert_true(_is_witness(level2, 0, 2, r + 1, prefix, 1))
    else:
        assert_false(_is_witness(level2, 0, 2, r + 1, prefix, 1))
        assert_true(_is_witness(level3, 0, 2, r + 1, prefix, 1))
    if s >= 1:
        var rev = reversed_substitution(sigma)
        var right1 = _power_images(rev, 1)
        var right2 = _power_images(rev, 2)
        var right3 = _power_images(rev, 3)
        var suffix: List[Int] = [s, s * n, s]
        # {0,2}: both images end with 1.
        assert_true(_is_witness(right1, 0, 2, 0, zero, 1))
        # {1,2}: suffixes of Parikh (s, sn, s), both preceded by 1.
        assert_true(_is_witness(right2, 1, 2, s * (n + 2), suffix, 1))
        # {0,1}: the same suffixes one level up.
        assert_true(_is_witness(right3, 0, 1, s * (n + 2), suffix, 1))


def _check_tau_witnesses(tau: List[List[Int]], n: Int) raises:
    """The explicit left witnesses of Proposition 5 for `tau_n`, `n >= 2`."""
    var level2 = _power_images(tau, 2)
    var level3 = _power_images(tau, 3)
    # {0,2}: prefixes 21 and 12, then 1.
    assert_true(_is_witness(level2, 0, 2, 2, [0, 1, 1], 1))
    # {1,2}: prefixes 12 and 21, then 1.
    assert_true(_is_witness(level3, 1, 2, 2, [0, 1, 1], 1))
    # {0,1}: prefixes 0 1 2 1^n and 1 2 1^n 0, then 0.
    assert_true(_is_witness(level3, 0, 1, n + 3, [1, n + 1, 1], 0))


def test_constructors() raises:
    assert_equal(substitution_key(sigma_family(1, 1, 1)), "1/012/01")
    assert_equal(substitution_key(sigma_family(3, 0, 2)), "111/0112/0")
    assert_equal(substitution_key(sigma_family(2, 2, 1)), "11/012/011")
    assert_equal(substitution_key(tau_family(1)), "1/210/01")
    assert_equal(substitution_key(tau_family(3)), "1/21110/01")
    var first = sigma_family(1, 1, 1)
    assert_equal(first[0], List[Int]([1]))
    assert_equal(first[1], List[Int]([0, 1, 2]))
    assert_equal(first[2], List[Int]([0, 1]))
    # The first member of the proved regime with a nonunit determinant.
    assert_equal(substitution_key(sigma_family(3, 1, 10)), "111/011111111112/01")
    assert_equal(substitution_key(tau_family(5)), "1/2111110/01")
    assert_equal(family_charpoly(3, 1, 10), List[Int]([-3, -4, -10, 1]))
    assert_equal(eval_cubic([-3, -4, -10, 1], 10), -43)
    assert_equal(eval_cubic([-3, -4, -10, 1], 11), 74)

    var refused = 0
    try:
        _ = sigma_family(0, 1, 5)
    except e:
        refused += 1
    try:
        _ = sigma_family(1, -1, 5)
    except e:
        refused += 1
    try:
        _ = sigma_family(1, 1, 0)
    except e:
        refused += 1
    try:
        _ = sigma_family(1, 1, FAMILY_MAX_PARAMETER + 1)
    except e:
        refused += 1
    try:
        _ = tau_family(0)
    except e:
        refused += 1
    try:
        _ = tau_family(FAMILY_MAX_PARAMETER + 1)
    except e:
        refused += 1
    assert_equal(refused, 6)
    assert_equal(longest_image(sigma_family(1, 1, FAMILY_MAX_PARAMETER)), 64)

    # Malformed input is a refusal here, before any kernel view can abort.
    var malformed = 0
    try:
        _ = family_facts([[0, 1], [1, 0]])
    except e:
        malformed += 1
    try:
        _ = family_facts([[0, 3], [0, 2], [0]])
    except e:
        malformed += 1
    try:
        _ = decide_family_f([[0, 1], List[Int](), [0]])
    except e:
        malformed += 1
    assert_equal(malformed, 3)
    # Not primitive: 0 -> 00, 1 -> 11, 2 -> 22.
    var not_primitive = False
    try:
        _ = family_facts([[0, 0], [1, 1], [2, 2]])
    except e:
        not_primitive = "not primitive" in String(e)
    assert_true(not_primitive)


def test_entry_point_domains() raises:
    """Which canonical entry points take a seven-letter image. `sigma_{1,1,4}`
    and `tau_4` (six letters) are the last members `psc.c4_geometric_f`
    accepts; `sigma_{1,1,5}` and `tau_5` (seven) are refused, and so is the
    first nonunit member of the proved regime."""
    assert_true(within_audited_domain(sigma_family(1, 1, 4)))
    assert_true(within_audited_domain(tau_family(4)))
    assert_true(decide_geometric_f(sigma_family(1, 1, 4)).holds)
    assert_true(decide_geometric_f(tau_family(4)).holds)
    var long_members: List[List[List[Int]]] = [sigma_family(1, 1, 5), tau_family(5), sigma_family(3, 1, 10)]
    for i in range(len(long_members)):
        assert_false(within_audited_domain(long_members[i]))
        assert_true(_audited_refuses(long_members[i], "certified only for"))
        assert_true(_profile_refuses(long_members[i], "certified only for"))
        var refused = False
        try:
            _ = decide_f_audited(long_members[i])
        except e:
            refused = "certified only for" in String(e)
        assert_true(refused)
        # The screened decision and profile accept them.
        var d = decide_f_screened(long_members[i])
        assert_true(d.holds)
        assert_false(d.audited)
        _ = screened_fc3_profile(long_members[i])

    # A state cap is an exhausted budget, never a verdict.
    var capped = False
    try:
        _ = decide_f_screened(sigma_family(3, 1, 10), 1)
    except e:
        capped = "state cap reached" in String(e)
    assert_true(capped)
    var bad_cap = False
    try:
        _ = decide_f_screened(sigma_family(3, 1, 10), 0)
    except e:
        bad_cap = "state cap must be positive" in String(e)
    assert_true(bad_cap)
    var bad_box = False
    try:
        _ = interior_periods_in_box(build_seed_overlap_tables_screened(tau_family(5)), [1, 1])
    except e:
        bad_box = "malformed box radii" in String(e)
    assert_true(bad_box)
    var bad_range = False
    try:
        _ = trapped_transients(tau_family(5), 1, 0, 0, 1, TRAP_STEPS)
    except e:
        bad_range = "empty range" in String(e)
    assert_true(bad_range)

    # A box a caller names is a search, not a verdict. With radii (0, 0, 0)
    # the candidates are the states (j, (a, 0, 0)). For 111/0112/0 each of
    # them reaches a vertex state, so the search is empty although the member
    # fails (F) with an interior 14-cycle. For 11/012/01 the same box holds
    # the state (1, (1, 0, 0)) of its interior 5-cycle and finds it: an
    # undersized box can go either way, which is why it carries no verdict.
    var failing = sigma_family(3, 0, 2)
    var narrow = interior_periods_in_box(build_seed_overlap_tables_screened(failing), [0, 0, 0])
    assert_true(narrow.candidates > 0)
    assert_equal(len(narrow.periods), 0)
    assert_false(decide_f_screened(failing).holds)
    var lucky = interior_periods_in_box(build_seed_overlap_tables_screened(sigma_family(2, 1, 1)), [0, 0, 0])
    assert_equal(lucky.periods, List[Int]([5]))


struct GridTotals(Copyable, Movable):
    var members: Int
    var above_pip_threshold: Int
    var pip3: Int
    var reducible: String
    var not_pisot: String
    var routh_refused: String
    var routh_refused_above: String
    var regime: Int
    var regime_audited: String
    var audited: Int
    var screened: Int
    var holds: Int
    var failing: String
    var class_members: Int
    var regime_class_b: Int
    var regime_class_c_only: Int
    var regime_not_members: Int
    var screened_radius_sum: Int
    var screened_radius_max: Int
    var screened_candidates: Int
    var doubled_candidates: Int
    var complex_pairs: Int
    var witness_in_range: Int
    var witness_out_of_range: Int
    var left_level_max: Int
    var right_level_max: Int
    var automaton_checked: Int
    var kappa_below_one: Int
    var trapped_states: Int
    var regime_longest: Int
    var lemma_q_longest: Int
    var trap_cross_checked: Int
    var trap_absorbed: Int

    def __init__(out self):
        self.members = 0
        self.above_pip_threshold = 0
        self.pip3 = 0
        self.reducible = String("")
        self.not_pisot = String("")
        self.routh_refused = String("")
        self.routh_refused_above = String("")
        self.regime = 0
        self.regime_audited = String("")
        self.audited = 0
        self.screened = 0
        self.holds = 0
        self.failing = String("")
        self.class_members = 0
        self.regime_class_b = 0
        self.regime_class_c_only = 0
        self.regime_not_members = 0
        self.screened_radius_sum = 0
        self.screened_radius_max = 0
        self.screened_candidates = 0
        self.doubled_candidates = 0
        self.complex_pairs = 0
        self.witness_in_range = 0
        self.witness_out_of_range = 0
        self.left_level_max = 0
        self.right_level_max = 0
        self.automaton_checked = 0
        self.kappa_below_one = 0
        self.trapped_states = 0
        self.regime_longest = 0
        self.lemma_q_longest = 0
        self.trap_cross_checked = 0
        self.trap_absorbed = 0


def _check_long_image_decision(sigma: List[List[Int]], d: FamilyFDecision, mut totals: GridTotals) raises:
    """A member beyond six letters: the canonical entry points refuse it, the
    screened decision is the one taken, and twice its radii hold no further
    cycle."""
    assert_false(d.audited)
    assert_true(_audited_refuses(sigma, "certified only for"))
    assert_true(_profile_refuses(sigma, "certified only for"))
    var tables = build_seed_overlap_tables_screened(sigma)
    var doubled: List[Int] = [2 * d.radii[0], 2 * d.radii[1], 2 * d.radii[2]]
    var wide = interior_periods_in_box(tables, doubled)
    assert_equal(len(wide.periods), d.cycles())
    assert_true(wide.candidates >= d.candidates)
    totals.screened += 1
    totals.screened_radius_sum += d.radii[0] + d.radii[1] + d.radii[2]
    for a in range(3):
        if d.radii[a] > totals.screened_radius_max:
            totals.screened_radius_max = d.radii[a]
    totals.screened_candidates += d.candidates
    totals.doubled_candidates += wide.candidates
    if discriminant(tables.field) < 0:
        totals.complex_pairs += 1


def _check_audited_decision(sigma: List[List[Int]], d: FamilyFDecision, mut totals: GridTotals) raises:
    """A member of at most six letters: the decision is the canonical one, and
    the screened walk reproduces it."""
    assert_true(d.audited)
    var canonical = decide_geometric_f(sigma)
    assert_equal(canonical.holds, d.holds)
    assert_equal(canonical.radii, d.radii)
    assert_equal(len(canonical.cycles), d.cycles())
    var screened = decide_f_screened(sigma)
    assert_false(screened.audited)
    assert_equal(screened.holds, d.holds)
    assert_equal(screened.radii, d.radii)
    assert_equal(screened.periods, d.periods)
    assert_true(screened.candidates >= d.candidates)
    totals.audited += 1


def _check_profile(
    sigma: List[List[Int]], det: Int, trace: Int, e2: Int, h1: Int, left: Int, right: Int
) raises -> FC3Profile:
    var p = family_fc3_profile(sigma)
    assert_equal(p.determinant, det)
    assert_equal(p.trace, trace)
    assert_equal(p.e2, e2)
    assert_equal(p.h1_dimension, h1)
    assert_equal(p.left_periodic, left)
    assert_equal(p.right_periodic, right)
    assert_false(p.endpoint_trivial())
    if within_audited_domain(sigma):
        # Inside the audited domain the profile is `fc3_profile`, and the
        # screened one is the same six numbers.
        var q = screened_fc3_profile(sigma)
        assert_equal(q.determinant, p.determinant)
        assert_equal(q.trace, p.trace)
        assert_equal(q.e2, p.e2)
        assert_equal(q.h1_dimension, p.h1_dimension)
        assert_equal(q.left_periodic, p.left_periodic)
        assert_equal(q.right_periodic, p.right_periodic)
    return p


def test_sigma_grid() raises -> GridTotals:
    var totals = GridTotals()
    for r in range(1, R_MAX + 1):
        for s in range(0, S_MAX + 1):
            for n in range(1, 3 * r + s + N_EXTRA + 1):
                var sigma = sigma_family(r, s, n)
                totals.members += 1

                # (i) words, matrix, characteristic polynomial, primitivity.
                assert_equal(len(sigma[0]), r)
                assert_true(_is_run(sigma[0], 0, r, 1))
                assert_equal(len(sigma[1]), n + 2)
                assert_equal(sigma[1][0], 0)
                assert_true(_is_run(sigma[1], 1, n + 1, 1))
                assert_equal(sigma[1][n + 1], 2)
                assert_equal(len(sigma[2]), s + 1)
                assert_equal(sigma[2][0], 0)
                assert_true(_is_run(sigma[2], 1, s + 1, 1))
                var m = Mat3(substitution_incidence(sigma))
                assert_equal(m.e, List[Int]([0, 1, 1, r, n, s, 0, 1, 0]))
                assert_true(is_primitive(m))
                var chi: List[Int] = [-r, -(r + s), -n, 1]
                assert_equal(m.charpoly(), chi)
                assert_equal(family_charpoly(r, s, n), chi)
                assert_equal(checked_charpoly(sigma), chi)
                var facts = family_facts(sigma)
                assert_equal(facts.charpoly, chi)
                assert_equal(facts.determinant(), r)
                assert_equal(m.det(), r)
                assert_equal(facts.trace(), n)
                assert_equal(facts.e2(), -(r + s))
                assert_equal(facts.irreducible, is_irreducible_cubic(chi))
                assert_equal(facts.pisot, is_pisot_charpoly(chi))

                # (ii), (iii): endpoint maps and dim H^1, at every member.
                assert_equal(facts.first_letters, List[Int]([1, 0, 0]))
                assert_equal(facts.left_periodic, 2)
                if s >= 1:
                    assert_equal(facts.last_letters, List[Int]([1, 2, 1]))
                    assert_equal(facts.right_periodic, 2)
                    assert_equal(facts.h1_dimension, 4)
                else:
                    assert_equal(facts.last_letters, List[Int]([1, 2, 0]))
                    assert_equal(facts.right_periodic, 3)
                    assert_equal(facts.h1_dimension, 5)

                # (i) the screens. Theorem 1: PIP3 for n >= r+s+1.
                if n >= r + s + 1:
                    totals.above_pip_threshold += 1
                    assert_true(facts.pip3())
                    assert_true(eval_cubic(chi, n) < 0)
                    assert_true(eval_cubic(chi, n + 1) > 0)
                # chi(-1) = s - 1 - n: -1 is a root exactly when n = s - 1.
                assert_equal(eval_cubic(chi, -1), s - 1 - n)
                assert_equal(facts.irreducible, n != s - 1)
                # The Routh screen agrees with the cubic decision wherever it
                # answers; it refuses exactly at n = 2r - s - 3 on PIP3 members.
                if facts.routh == pisot_screen.SCREEN_REFUSED:
                    assert_true(facts.pip3())
                    assert_equal(n, 2 * r - s - 3)
                    totals.routh_refused += " " + _name(r, s, n)
                    if n >= r + s + 1:
                        totals.routh_refused_above += " " + _name(r, s, n)
                else:
                    assert_equal(facts.routh == pisot_screen.SCREEN_PISOT, facts.pisot)
                    assert_true(n != 2 * r - s - 3 or not facts.pip3())
                if not facts.pip3():
                    # Below the threshold only; refused by every decision here.
                    assert_true(n <= r + s)
                    if not facts.irreducible:
                        totals.reducible += " " + _name(r, s, n)
                        assert_true(_screened_refuses(sigma, "reducible"))
                        assert_true(_screened_profile_refuses(sigma, "reducible"))
                    else:
                        totals.not_pisot += " " + _name(r, s, n)
                        assert_true(_screened_refuses(sigma, "not Pisot"))
                        assert_true(_screened_profile_refuses(sigma, "not Pisot"))
                    assert_true(within_audited_domain(sigma))
                    assert_true(_audited_refuses(sigma, "primitive irreducible Pisot"))
                    assert_true(_profile_refuses(sigma, "primitive irreducible Pisot"))
                    continue
                totals.pip3 += 1

                # (iv) property (F).
                var d = decide_family_f(sigma)
                assert_equal(d.audited, within_audited_domain(sigma))
                assert_equal(d.audited, n <= 4)
                if d.audited:
                    _check_audited_decision(sigma, d, totals)
                else:
                    _check_long_image_decision(sigma, d, totals)
                if d.holds:
                    totals.holds += 1
                    assert_equal(d.cycles(), 0)
                else:
                    totals.failing += " " + _name(r, s, n) + ":" + _joined(d.periods)
                    # Every failure lies below n = r + s, far from the regime.
                    assert_true(n <= r + s - 1)
                    assert_true(d.audited)
                var in_regime = n >= 3 * r + s
                if in_regime:
                    totals.regime += 1
                    assert_true(d.holds)  # Theorem 2(a) on the grid
                    if d.audited:
                        totals.regime_audited += " " + _name(r, s, n)

                # The finite parts of the written proof of (F).
                var trapping = sigma_trapping_sign(r, s, n)
                var kappa = sigma_kappa_sign(r, s, n)
                assert_true(trapping != 0 and kappa != 0)
                if n >= r + s + 1:
                    # Lemma R: eps + 2 r theta < 1 exactly when n >= 3r + s.
                    assert_equal(trapping < 0, in_regime)
                if trapping < 0:
                    assert_true(kappa < 0)
                var trap = trapped_transients(sigma, 0, 1, 0, 1, TRAP_STEPS)
                assert_true(trap.states > 0)
                if d.audited:
                    # The same states through the canonical state map: an
                    # unresolved state is one absorbed by an interior cycle.
                    var canonical = _canonical_trap(sigma, 0)
                    assert_equal(canonical[0], trap.states)
                    assert_equal(canonical[1], trap.longest)
                    assert_equal(canonical[2], trap.unresolved)
                    totals.trap_cross_checked += 1
                    totals.trap_absorbed += trap.unresolved
                if kappa < 0:
                    # Lemma Q: every state with b, c in {0,1} is a vertex
                    # state after at most four steps.
                    totals.kappa_below_one += 1
                    assert_equal(trap.unresolved, 0)
                    assert_true(trap.longest <= 4)
                    if trap.longest > totals.lemma_q_longest:
                        totals.lemma_q_longest = trap.longest
                if in_regime:
                    assert_true(kappa < 0)
                    assert_equal(trap.longest, 4)
                    totals.trapped_states += trap.states
                    if trap.longest > totals.regime_longest:
                        totals.regime_longest = trap.longest

                # (v) the arithmetic profile and the class.
                var p = _check_profile(sigma, r, n, -(r + s), 4 if s >= 1 else 5, 2, 2 if s >= 1 else 3)
                var odd = r % 2 == 1
                assert_equal(clause_b(p), odd and s >= 1)
                assert_equal(clause_c(p), odd and (n + r + s) % 2 == 1)
                var member = nontrivial_fc3_member(p, d.holds)
                assert_equal(member, d.holds and odd and (s >= 1 or (n + r) % 2 == 1))
                if member:
                    totals.class_members += 1
                if in_regime:
                    if odd and s >= 1:
                        assert_true(member and clause_b(p))
                        totals.regime_class_b += 1
                    elif odd and n % 2 == 0:
                        assert_true(member and clause_c(p) and not clause_b(p))
                        totals.regime_class_c_only += 1
                    else:
                        # even determinant, or s = 0 with n odd: not reported
                        assert_false(member)
                        assert_false(clause_b(p))
                        assert_false(clause_c(p))
                        totals.regime_not_members += 1

                # (vi) strong-coincidence witnesses, literal words.
                var w = coincidence_profile(sigma, WITNESS_WORD_BUDGET)
                for k in range(3):
                    assert_true(w.left[k] >= 1 and w.right[k] >= 1)
                    if w.left[k] > totals.left_level_max:
                        totals.left_level_max = w.left[k]
                    if w.right[k] > totals.right_level_max:
                        totals.right_level_max = w.right[k]
                if s >= 1 and n >= max(r + 1, s):
                    assert_equal(w.left, List[Int]([2, 2, 1]))
                    assert_equal(w.right, List[Int]([3, 1, 2]))
                    _check_sigma_witnesses(sigma, r, s, n)
                    totals.witness_in_range += 1
                elif s == 0 and n >= r + 1:
                    assert_equal(w.left, List[Int]([2, 3, 1]))
                    # Right witnesses for s = 0 are not part of Proposition 5;
                    # the search finds them at levels 3, 4, 4.
                    assert_equal(w.right, List[Int]([3, 4, 4]))
                    _check_sigma_witnesses(sigma, r, s, n)
                    totals.witness_in_range += 1
                else:
                    totals.witness_out_of_range += 1
                assert_true(w.excludes_strict_systems())
                if longest_image(sigma) <= AUTOMATON_IMAGE_BOUND:
                    assert_equal(_automaton_levels(sigma), w.left)
                    assert_equal(_automaton_levels(reversed_substitution(sigma)), w.right)
                    totals.automaton_checked += 1
    return totals^


struct TauTotals(Copyable, Movable):
    var members: Int
    var audited: Int
    var screened: Int
    var class_members: Int
    var screened_radius_sum: Int
    var trapped_states: Int
    var small_longest: String
    var automaton_checked: Int

    def __init__(out self):
        self.members = 0
        self.audited = 0
        self.screened = 0
        self.class_members = 0
        self.screened_radius_sum = 0
        self.trapped_states = 0
        self.small_longest = String("")
        self.automaton_checked = 0


def test_tau() raises -> TauTotals:
    var totals = TauTotals()
    var scratch = GridTotals()
    for n in range(1, TAU_MAX + 1):
        var tau = tau_family(n)
        totals.members += 1
        assert_equal(len(tau[0]), 1)
        assert_equal(tau[0][0], 1)
        assert_equal(len(tau[1]), n + 2)
        assert_equal(tau[1][0], 2)
        assert_true(_is_run(tau[1], 1, n + 1, 1))
        assert_equal(tau[1][n + 1], 0)
        assert_equal(tau[2], List[Int]([0, 1]))
        # Same incidence matrix as sigma_{1,1,n}, a different substitution.
        var twin = sigma_family(1, 1, n)
        assert_equal(substitution_incidence(tau), substitution_incidence(twin))
        assert_true(tau != twin)
        var chi: List[Int] = [-1, -2, -n, 1]
        var facts = family_facts(tau)
        assert_equal(facts.charpoly, chi)
        assert_equal(family_charpoly(1, 1, n), chi)
        assert_true(is_primitive(Mat3(substitution_incidence(tau))))
        # Theorem 1: tau_n is PIP3 for every n >= 1.
        assert_true(facts.pip3())
        assert_equal(facts.routh, pisot_screen.SCREEN_PISOT)
        assert_true(eval_cubic(chi, n) < 0)
        if n >= 3:
            assert_true(eval_cubic(chi, n + 1) > 0)
        # Theorem 3.
        assert_equal(facts.first_letters, List[Int]([1, 2, 0]))
        assert_equal(facts.last_letters, List[Int]([1, 0, 1]))
        assert_equal(facts.left_periodic, 3)
        assert_equal(facts.right_periodic, 2)
        assert_equal(facts.h1_dimension, 5)

        # Theorem 2(b) for n >= 5, and the individual decisions n = 1..4.
        var d = decide_family_f(tau)
        assert_true(d.holds)
        assert_equal(d.audited, n <= 4)
        if d.audited:
            _check_audited_decision(tau, d, scratch)
            totals.audited += 1
        else:
            _check_long_image_decision(tau, d, scratch)
            totals.screened += 1
            totals.screened_radius_sum += d.radii[0] + d.radii[1] + d.radii[2]
        # The trapping hypothesis 5 theta + 2 theta^2 < 1 holds exactly from n = 5.
        assert_equal(tau_trapping_sign(n) > 0, n >= 5)
        # The table: b in {0,1}, c in {-1,0,1}; at most six steps.
        var trap = trapped_transients(tau, 0, 1, -1, 1, TRAP_STEPS)
        assert_equal(trap.unresolved, 0)
        if d.audited:
            var canonical = _canonical_trap(tau, -1)
            assert_equal(canonical[0], trap.states)
            assert_equal(canonical[1], trap.longest)
            assert_equal(canonical[2], 0)
        if n >= 5:
            assert_equal(trap.longest, 6)
            totals.trapped_states += trap.states
        else:
            totals.small_longest += " " + String(n) + ":" + String(trap.longest)

        # Clause (c) only, and only for odd n.
        var p = _check_profile(tau, 1, n, -2, 5, 3, 2)
        assert_false(clause_b(p))
        assert_equal(clause_c(p), n % 2 == 1)
        assert_equal(nontrivial_fc3_member(p, d.holds), n % 2 == 1)
        if n % 2 == 1:
            totals.class_members += 1

        # Witnesses.
        var w = coincidence_profile(tau, WITNESS_WORD_BUDGET)
        if n >= 2:
            assert_equal(w.left, List[Int]([3, 2, 3]))
            assert_equal(w.right, List[Int]([2, 1, 2]))
            _check_tau_witnesses(tau, n)
        else:
            assert_equal(w.left, List[Int]([3, 4, 5]))
            assert_equal(w.right, List[Int]([5, 1, 4]))
        assert_true(w.excludes_strict_systems())
        if longest_image(tau) <= AUTOMATON_IMAGE_BOUND:
            assert_equal(_automaton_levels(tau), w.left)
            assert_equal(_automaton_levels(reversed_substitution(tau)), w.right)
            totals.automaton_checked += 1
    return totals^


def _expect_cycles(r: Int, s: Int, n: Int, expected: List[String]) raises -> Int:
    """`sigma_{r,s,n}` fails (F) by the canonical module, with exactly the
    interior cycles `expected`: each entry is `base state:period:p(P)`, the
    least state of the cycle, its period and the Parikh vector of the prefix
    of its interior address. Every state of every cycle replays
    `(M^k - I) v = p(P)` at an interior occurrence (`interior_address` raises
    otherwise), the cycle closes under `PrototileMap.step`, and it leaves the
    set `b, c in {0,1}` the trapping lemma confines periodic states to.
    Returns the number of interior states."""
    var sigma = sigma_family(r, s, n)
    var m = PrototileMap(sigma)
    var v = decide_geometric_f(sigma)
    assert_false(v.holds)
    assert_equal(len(v.cycles), len(expected))
    # Neither hypothesis of the written proof holds here.
    assert_true(sigma_trapping_sign(r, s, n) > 0)
    assert_true(sigma_kappa_sign(r, s, n) > 0)
    assert_true(n < 3 * r + s)
    var found = Dict[String, Int]()
    var states = 0
    for c in range(len(v.cycles)):
        var k = v.cycles[c].period()
        var outside = 0
        for t in range(k):
            var state = v.cycles[c].states[t]
            assert_false(state.is_vertex())
            assert_true(m.is_state(state))
            var step = m.step(state)
            assert_equal(step.child, v.cycles[c].states[(t + 1) % k])
            assert_equal(step.index, v.cycles[c].indices[t])
            var a = interior_address(m, v.cycles[c], t)
            assert_equal(a.period, k)
            assert_equal(a.letter, state.letter)
            assert_equal(a.prefix_parikh[0] + a.prefix_parikh[1] + a.prefix_parikh[2], a.prefix_length)
            assert_true(a.prefix_length >= 1 and a.prefix_length <= a.image_length - 2)
            if state.v1 < 0 or state.v1 > 1 or state.v2 < 0 or state.v2 > 1:
                outside += 1
        assert_true(outside > 0)
        states += k
        var base = interior_address(m, v.cycles[c], 0)
        var key = _state_text(v.cycles[c].states[0]) + ":" + String(k) + ":" + _joined(base.prefix_parikh)
        found[key] = found.get(key, 0) + 1
    for i in range(len(expected)):
        assert_true(expected[i] in found)
        assert_equal(found[expected[i]], 1)
    return states


def test_members_failing_f() raises -> Int:
    """The six members the note lists as failing (F), and the four further
    ones on the grid. All have `n <= r + s - 1`: the hypothesis `n >= 3r + s`
    of the theorem is not decorative."""
    var states = 0
    states += _expect_cycles(2, 1, 1, ["(0;0,0,1):5:23,41,16"])
    states += _expect_cycles(3, 0, 2, ["(0;-2,2,1):14:1525760,3749736,1164264"])
    states += _expect_cycles(3, 1, 2, ["(0;1,-1,1):8:2028,5376,1569"])
    states += _expect_cycles(3, 2, 3, ["(1;-1,1,1):5:297,1039,240"])
    states += _expect_cycles(
        5, 1, 4,
        [
            "(0;-3,4,-1):8:89071,397823,74949",
            "(0;1,0,-2):14:518222266,2314588554,436067381",
            "(0;0,-1,3):8:10758,48054,9052",
            "(0;1,-1,1):8:33932,151556,28553",
        ],
    )
    states += _expect_cycles(5, 0, 4, ["(0;-4,4,1):23:1384666273029884,5981553401658307,1159789589428833"])
    # Not in the note's list; decided here by the canonical module.
    states += _expect_cycles(3, 2, 2, ["(0;0,0,1):5:113,319,88"])
    states += _expect_cycles(
        4, 1, 3,
        [
            "(0;-1,1,1):8:14094,49956,11463",
            "(0;3,-3,1):8:5226,18528,4251",
            "(0;1,-3,6):8:15069,53415,12255",
            "(0;1,-1,1):8:9660,34242,7857",
        ],
    )
    states += _expect_cycles(4, 2, 3, ["(1;-1,1,1):5:279,1032,228"])
    states += _expect_cycles(5, 2, 4, ["(0;1,-1,1):8:59065,272120,49910"])

    # The interior 5-cycle of 11/012/01, by hand. M has rows (0,1,1), (2,1,1),
    # (0,1,0). (0; 0,0,1): M v = (1,1,0), sub-tile 1 of sigma(0) = 1.1 after
    # the prefix 1, v' = (1,0,0) on a tile 1. (1; 1,0,0): M v = (0,2,0),
    # sub-tile 2 of sigma(1) = 01.2, v' = (-1,1,0) on a tile 2. (2; -1,1,0):
    # M v = (1,-1,1), sub-tile 0 of sigma(2) = .01, on a tile 0. (0; 1,-1,1):
    # M v = (0,2,-1), sub-tile 1, v' = (0,1,-1) on a tile 1. (1; 0,1,-1):
    # M v = (0,0,1), sub-tile 0 of sigma(1): back to (0; 0,0,1).
    var m = PrototileMap(sigma_family(2, 1, 1))
    var walk: List[PrototileState] = [
        PrototileState(0, 0, 0, 1), PrototileState(1, 1, 0, 0), PrototileState(2, -1, 1, 0),
        PrototileState(0, 1, -1, 1), PrototileState(1, 0, 1, -1),
    ]
    var digits: List[Int] = [1, 2, 0, 1, 0]
    for t in range(5):
        var step = m.step(walk[t])
        assert_equal(step.child, walk[(t + 1) % 5])
        assert_equal(step.index, digits[t])
    # Outside its hypothesis the table lemma fails with it: nine of the ten
    # states of 11/012/01 with b, c in {0,1} have not reached a vertex state
    # after 64 steps, and the canonical `OrbitMemo` says why: they are
    # absorbed by the interior cycle.
    var trap = trapped_transients(sigma_family(2, 1, 1), 0, 1, 0, 1, TRAP_STEPS)
    assert_equal(trap.states, 10)
    assert_equal(trap.unresolved, 9)
    assert_equal(_canonical_trap(sigma_family(2, 1, 1), 0), List[Int]([10, 1, 9]))
    return states


def test_named_members() raises:
    """The members the note names, through the canonical module where it
    accepts them."""
    # (F) by decide_geometric_f: sigma_{1,1,n}, n = 1..4, tau_n, n = 1..4.
    for n in range(1, 5):
        assert_true(decide_geometric_f(sigma_family(1, 1, n)).holds)
        assert_true(decide_geometric_f(tau_family(n)).holds)
    # The smallest nonunit members with a canonical decision, det 3:
    # 111/01112/01, 111/011112/01, 111/011112/011 (clause (b)) and
    # 111/011112/0 (clause (c) only).
    var names: List[String] = ["111/01112/01", "111/011112/01", "111/011112/011", "111/011112/0"]
    var members: List[List[List[Int]]] = [
        sigma_family(3, 1, 3), sigma_family(3, 1, 4), sigma_family(3, 2, 4), sigma_family(3, 0, 4),
    ]
    for i in range(4):
        assert_equal(substitution_key(members[i]), names[i])
        assert_true(decide_geometric_f(members[i]).holds)
        var p = fc3_profile(members[i])
        assert_equal(p.determinant, 3)
        assert_equal(clause_b(p), i < 3)
        assert_true(clause_b(p) or clause_c(p))
        assert_true(nontrivial_fc3_member(p, True))
    # None of them is in the proved regime n >= 3r + s = 9 + s.
    # The first member of the proved regime with a nonunit determinant is out
    # of reach of the canonical module and is decided by the screened walk.
    var first = sigma_family(3, 1, 10)
    assert_equal(longest_image(first), 12)
    var d = decide_family_f(first)
    assert_true(d.holds)
    assert_false(d.audited)
    assert_equal(d.radii, List[Int]([4, 2, 2]))
    var p = family_fc3_profile(first)
    assert_equal(p.determinant, 3)
    assert_true(clause_b(p))
    assert_true(nontrivial_fc3_member(p, d.holds))
    # Radii of the screened box on four more long-image members.
    assert_equal(decide_f_screened(tau_family(5)).radii, List[Int]([3, 1, 2]))
    assert_equal(decide_f_screened(tau_family(16)).radii, List[Int]([5, 1, 1]))
    assert_equal(decide_f_screened(sigma_family(5, 2, 23)).radii, List[Int]([4, 1, 1]))
    assert_equal(decide_f_screened(sigma_family(5, 0, 15)).radii, List[Int]([4, 2, 2]))


def test_literal_box_graph() raises -> Int:
    """Six long-image members on the literal box graph of Corollary LC5:
    `psc.vertex_coincidence.build_box_graph` (the box of the independent
    Sturm-Tarski `box_radii`, closed under inflation) holds no terminal cycle
    of `psc.leftmost_chain`. That is (F) in the form of the bridge of
    `psc.c4_geometric_f`, computed without `stable_radii` and without the
    walk of `psc.c4_fc3_family`. Returns the number of box-graph states."""
    var members: List[List[List[Int]]] = [
        sigma_family(1, 1, 5), sigma_family(3, 1, 10), sigma_family(5, 2, 23), sigma_family(5, 0, 15),
        tau_family(5), tau_family(16),
    ]
    var states = 0
    for i in range(len(members)):
        assert_false(within_audited_domain(members[i]))
        var tables = build_seed_overlap_tables_screened(members[i])
        var graph = build_box_graph(tables)
        assert_false(graph.capped)
        assert_equal(len(terminal_leftmost_cycles(tables, graph, 0)), 0)
        assert_true(decide_f_screened(members[i]).holds)
        states += graph.size()
    return states


def test_screened_walk_on_the_corpus() raises -> List[Int]:
    """The screened walk against the canonical decision on the standing
    corpus (images of at most three letters, where both exist). On every
    specimen the screened tables are the audited ones and the walk in the
    canonical box returns the canonical number of interior cycles and their
    periods; on every `CORPUS_STRIDE`-th specimen `decide_f_screened`, with
    its own `stable_radii`, returns the canonical verdict, radii and periods.
    Returns `[specimens, with (F), cycles, interior states, three real
    roots, end-to-end replays]`."""
    var corpus = pip_corpus()
    var boxes = StableRadiiCache()
    var holds = 0
    var cycles = 0
    var interior = 0
    var real = 0
    var replays = 0
    for i in range(len(corpus)):
        var sigma = corpus[i].sigma.copy()
        var m = PrototileMap(sigma)
        var v = decide_geometric_f_with(m, boxes)
        var periods = List[Int]()
        for c in range(len(v.cycles)):
            periods.append(v.cycles[c].period())
            interior += v.cycles[c].period()
        periods = _sorted(periods)
        var tables = build_seed_overlap_tables_screened(sigma)
        assert_equal(tables.field.charpoly(), m.tables.field.charpoly())
        for a in range(3):
            assert_equal(tables.lengths.at(a), m.tables.lengths.at(a))
        var search = interior_periods_in_box(tables, v.radii)
        assert_equal(_sorted(search.periods), periods)
        assert_true(search.candidates >= v.candidates)
        if i % CORPUS_STRIDE == 0:
            var d = decide_f_screened(sigma)
            assert_equal(d.holds, v.holds)
            assert_equal(d.radii, v.radii)
            assert_equal(d.periods, periods)
            replays += 1
        if v.holds:
            holds += 1
        cycles += len(v.cycles)
        if discriminant(m.tables.field) > 0:
            real += 1
    return [len(corpus), holds, cycles, interior, real, replays]


def test_no_two_members_are_conjugate_or_mirror() raises -> Int:
    """No grid member is a relabelling of another grid member or of the
    reversal of one. Relations by powers are the written argument, not this
    test."""
    var owner = Dict[String, Int]()
    var index = 0
    var keys = 0
    var all = List[List[List[Int]]]()
    for r in range(1, R_MAX + 1):
        for s in range(0, S_MAX + 1):
            for n in range(1, 3 * r + s + N_EXTRA + 1):
                all.append(sigma_family(r, s, n))
    for n in range(1, TAU_MAX + 1):
        all.append(tau_family(n))
    for i in range(len(all)):
        var forms: List[String] = [
            substitution_key(canonical_substitution(all[i])),
            substitution_key(canonical_substitution(reversed_substitution(all[i]))),
        ]
        for k in range(2):
            if forms[k] in owner:
                assert_equal(owner[forms[k]], index)
            else:
                owner[forms[k]] = index
                keys += 1
        index += 1
    return keys


def main() raises:
    test_constructors()
    test_entry_point_domains()
    var grid = test_sigma_grid()
    var tau = test_tau()
    var interior_states = test_members_failing_f()
    test_named_members()
    var literal_states = test_literal_box_graph()
    var corpus = test_screened_walk_on_the_corpus()
    var keys = test_no_two_members_are_conjugate_or_mirror()

    # (i) the screens on the sigma grid.
    assert_equal(grid.members, 240)
    assert_equal(grid.above_pip_threshold, 180)
    assert_equal(grid.pip3, 220)
    assert_equal(grid.reducible, " (1,2,1) (2,2,1) (3,2,1) (4,2,1) (5,2,1)")
    assert_equal(
        grid.not_pisot,
        " (3,0,1) (3,1,1) (4,0,1) (4,0,2) (4,1,1) (4,1,2) (4,2,2)"
        + " (5,0,1) (5,0,2) (5,0,3) (5,1,1) (5,1,2) (5,1,3) (5,2,2) (5,2,3)",
    )
    assert_equal(grid.routh_refused, " (2,0,1) (3,0,3) (3,1,2) (4,0,5) (4,1,4) (4,2,3) (5,0,7) (5,1,6) (5,2,5)")
    assert_equal(grid.routh_refused_above, " (4,0,5) (5,0,7)")
    # (iv) property (F).
    assert_equal(grid.holds, 210)
    assert_equal(
        grid.failing,
        " (2,1,1):5 (3,0,2):14 (3,1,2):8 (3,2,2):5 (3,2,3):5 (4,1,3):8,8,8,8 (4,2,3):5"
        + " (5,0,4):23 (5,1,4):8,8,8,14 (5,2,4):8",
    )
    assert_equal(interior_states, 143)
    assert_equal(grid.regime, 105)
    assert_equal(grid.regime_audited, " (1,0,3) (1,0,4) (1,1,4)")
    assert_equal(grid.audited, 40)
    assert_equal(grid.screened, 180)
    assert_equal(grid.screened_radius_sum, 1552)
    assert_equal(grid.screened_radius_max, 13)
    assert_equal(grid.screened_candidates, 27599)
    assert_equal(grid.doubled_candidates, 94352)
    # Every long-image member has a complex conjugate pair: that branch of
    # `stable_radii` is the one these decisions exercise.
    assert_equal(grid.complex_pairs, 180)
    assert_equal(literal_states, 9074)
    # The screened walk on the standing corpus: 4,554 specimens, 1,794 with
    # (F), 3,756 interior cycles with 12,828 states (the pins of
    # test_c4_geometric_f), 648 specimens with three real roots.
    assert_equal(corpus, List[Int]([4554, 1794, 3756, 12828, 648, 198]))
    # The trapped states through the canonical state map, on the 40 members
    # of at most six letters; on the ten that fail (F), 58 of them are
    # absorbed by an interior cycle.
    assert_equal(grid.trap_cross_checked, 40)
    assert_equal(grid.trap_absorbed, 58)
    # The finite parts of the written proof.
    assert_equal(grid.kappa_below_one, 150)
    assert_equal(grid.lemma_q_longest, 4)
    assert_equal(grid.regime_longest, 4)
    assert_equal(grid.trapped_states, 2490)
    # (v) the class.
    assert_equal(grid.class_members, 103)
    assert_equal(grid.regime_class_b, 42)
    assert_equal(grid.regime_class_c_only, 9)
    assert_equal(grid.regime_not_members, 54)
    # (vi) witnesses.
    assert_equal(grid.witness_in_range, 195)
    assert_equal(grid.witness_out_of_range, 25)
    assert_equal(grid.left_level_max, 5)
    assert_equal(grid.right_level_max, 7)
    assert_equal(grid.automaton_checked, 154)
    # tau_n.
    assert_equal(tau.members, 16)
    assert_equal(tau.audited, 4)
    assert_equal(tau.screened, 12)
    assert_equal(tau.screened_radius_sum, 76)
    assert_equal(tau.class_members, 8)
    assert_equal(tau.trapped_states, 912)
    assert_equal(tau.small_longest, " 1:8 2:6 3:6 4:6")
    assert_equal(tau.automaton_checked, 12)
    assert_equal(keys, 512)

    print(
        "FC3 families on the grid:", grid.members, "sigma members,", grid.pip3, "PIP3 (all", grid.above_pip_threshold,
        "with n >= r+s+1; Routh screen refuses" + grid.routh_refused + "); (F) holds at", grid.holds,
        "and fails at" + grid.failing + ";", grid.regime, "members with n >= 3r+s, all (F), canonical module accepts"
        + grid.regime_audited + "; decisions: canonical", grid.audited, ", screened", grid.screened, "(radius sum",
        grid.screened_radius_sum, ", largest", grid.screened_radius_max, "); class members", grid.class_members,
        ", in the regime (b)", grid.regime_class_b, ", (c) only", grid.regime_class_c_only, ", not members",
        grid.regime_not_members, "; witnesses on the confirmed ranges", grid.witness_in_range, ", elsewhere",
        grid.witness_out_of_range, "(levels up to", grid.left_level_max, "left,", grid.right_level_max,
        "right); trapped states in the regime", grid.trapped_states, ", longest transient", grid.regime_longest,
        "; tau_n:", tau.members, "members, all PIP3 with (F), canonical", tau.audited, ", screened", tau.screened,
        ", class members", tau.class_members, ", trapped states for n >= 5:", tau.trapped_states,
        "; interior states of the ten failing members", interior_states, "; normal forms", keys,
        "; screened walk against the canonical decision on the corpus:", corpus[0], "specimens,", corpus[2],
        "interior cycles, all reproduced; literal LC5 box graphs on six long-image members:", literal_states,
        "states, no terminal leftmost cycle",
    )
    require_contract("FC3 families (psc.c4_fc3_family): sigma_{r,s,n} = (1^r, 0 1^n 2, 0 1^s) and tau_n = (1, 2 1^n 0, 0 1), pinned on a finite grid; the statement for all parameters is the recorded proof (docs/c4-fc3-family-2026-11-16.md: not machine-checked, independent human review pending), which this test does not replace. Grid: 1 <= r <= 5, 0 <= s <= 2, 1 <= n <= 3r+s+6 (240 members) and tau_n for 1 <= n <= 16; exact integer, rational and Z[beta] arithmetic. (i) The image words; incidence rows (0,1,1), (r,n,s), (0,1,0), tau_n that of sigma_{1,1,n}; det M = r, tr M = n, e_2(M) = -(r+s), chi = t^3 - n t^2 - (r+s) t - r in checked arithmetic; every member primitive; psc.pisot accepts all 180 members with n >= r+s+1, with chi(n) < 0 < chi(n+1), and every tau_n; below that threshold it accepts 40 members and rejects 20: the five (r,2,1) are reducible (chi(-1) = s - 1 - n = 0) and 15 are irreducible and not Pisot, (3,0,1) (3,1,1) (4,0,1) (4,0,2) (4,1,1) (4,1,2) (4,2,2) (5,0,1) (5,0,2) (5,0,3) (5,1,1) (5,1,2) (5,1,3) (5,2,2) (5,2,3); the Routh screen psc.pisot_screen.screen agrees with psc.pisot wherever it answers and refuses exactly the nine PIP3 members with n = 2r - s - 3, two of them above the threshold, (4,0,5) and (5,0,7): a refusal, not a verdict. (ii) g = (1,0,0), two periodic letters; g_R = (1,2,1), two, for s >= 1 and (1,2,0), three, for s = 0; tau_n: g = (1,2,0), three, g_R = (1,0,1), two. (iii) dim H^1 = 4 for s >= 1, 5 for s = 0 and for tau_n (psc.h1_census). (iv) Property (F). decide_geometric_f and fc3_profile are certified for images of at most six letters and refuse every longer one (asserted on each of the 192 long-image PIP3 members): of the 105 grid members with n >= 3r+s they accept sigma_{1,0,3}, sigma_{1,0,4}, sigma_{1,1,4}, and they accept no tau_n with n >= 5. On the 44 members they accept, (F) holds at 34, among them sigma_{1,1,n} and tau_n for n = 1..4 and the nonunit 111/01112/01, 111/011112/01, 111/011112/011, 111/011112/0, and fails at ten, each interior cycle state replaying (M^k - I) v = p(P) at an interior occurrence and each cycle leaving b, c in {0,1}: periods 5 for sigma_{2,1,1} (its 5-cycle through (0;0,0,1) re-derived by hand), 14 for sigma_{3,0,2}, 8 for sigma_{3,1,2}, 5 for sigma_{3,2,3}, 8, 8, 8, 14 for sigma_{5,1,4}, 23 for sigma_{5,0,4} (the six of the note), and 5 for sigma_{3,2,2}, 8, 8, 8, 8 for sigma_{4,1,3}, 5 for sigma_{4,2,3}, 8 for sigma_{5,2,4}; 143 interior states; all ten have n <= r+s-1 and fail both hypotheses of the written proof. Beyond six letters (F) is decided by decide_f_screened: the box of stable_radii (Lemma B) on the coefficient-screened tables, the prototile states among its box start states, psc.leftmost_chain.leftmost_step as the state map, the walk of Lemma W. Calibration: on all 4,554 standing corpus specimens the screened tables are the audited ones and the walk in the canonical box returns the canonical cycle periods (1,794 specimens with none, 3,756 cycles, 12,828 states, 648 specimens with three real roots), decide_f_screened end to end agrees on every 23rd (198), and on the 44 grid members above, the ten failures included. Result: no interior cycle at any of the 192 long-image members, so (F) holds at every grid member with n >= 3r+s (105) and at tau_n for n <= 16; radii pinned (sum 1,552 over the 180 sigma members, largest 13, sum 76 over the 12 tau members, (4,2,2) for 111/0 1^10 2/01, the first nonunit member of the regime), all 180 with a complex conjugate pair; twice the radii hold no cycle on any of them, and on six members the literal box graph of Corollary LC5 (build_box_graph on the independent box_radii, 9,074 states) has no terminal leftmost cycle. A box named by a caller gives a search and no verdict: radii (0,0,0) find nothing on sigma_{3,0,2}, which fails (F). Finite parts of the written proof: eps + 2 r theta < 1 exactly when n >= 3r+s on the 180 members with n >= r+s+1, and 5 theta + 2 theta^2 < 1 exactly when n >= 5 for tau_n (exact signs at the Perron root); every state with b, c in {0,1} reaches a vertex state within four steps on the 150 members with kappa < 1, the longest taking exactly four on each of the 105 regime members (2,490 states), and every state of tau_n, n >= 5, with b in {0,1}, c in {-1,0,1} within six (912 states, the longest exactly six); on the 44 short-image members the same counts come out of the canonical OrbitMemo, where 58 such states of the ten failing members are absorbed by an interior cycle; the trapping lemma is an argument and is not replayed. (v) FC3Profile (fc3_profile on its domain, screened_fc3_profile beyond, equal on the domain): clause (b) exactly for r odd and s >= 1, clause (c) exactly for r odd and n + r + s odd; of the 105 regime members 42 meet the hypotheses of the non-trivial part of the FC3 class by clause (b) (r odd, s >= 1), 9 by clause (c) only (r odd, s = 0, n even), and 54 are not reported (r even, or s = 0 with n odd); tau_n never has (b) and is reported exactly for n odd (8 of 16); 103 of the 220 PIP3 grid members have (F), two periodic letters on both sides and (b) or (c). (vi) Strong coincidence on literal words (coincidence_profile): least levels left (2,2,1), right (3,1,2) for s >= 1 and n >= max(r+1, s); left (2,3,1), right (3,4,4) for s = 0 and n >= r+1 (195 members in all), with the explicit witnesses of the note replayed (prefixes of Parikh vector (1,r,0), suffixes of Parikh vector (s,sn,s)); tau_n, n >= 2: left (3,2,3), right (2,1,2), with its explicit left witnesses; tau_1: (3,4,5), (5,1,4); the other 25 PIP3 members have witnesses for all pairs on both sides too (levels at most 5 left, 7 right); the coincidence automaton agrees on the 154 sigma and 12 tau members with images of at most 14 letters. No grid member is a relabelling of another or of the reversal of one (512 normal forms). Hypotheses and finite facts only: the families are not new C4 cases (the witnesses make C4 elementary on them), no coincidence rank, pure discrete spectrum or conclusion of Theorem FC3 is certified, and no claim status changes")
