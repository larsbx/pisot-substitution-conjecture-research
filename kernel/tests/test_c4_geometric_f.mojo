"""Exact regression for the geometric property (F) class (psc.c4_geometric_f).

docs/c4-geometric-f-class-2026-11-16.md. Named fixtures by hand, refusals,
the literal fixed-ray definition against the overlap-closure one, and the
corpus content of Theorems FC1, P and FC3 on all 4,554 standing specimens,
with (F) cross-checked against `psc.leftmost_chain` (Corollary LC5).

How (F) is tied to Corollary LC5 on every specimen. `psc.c4_geometric_f`
predicts the number of terminal leftmost cycles from its interior f-cycles
(`2 * sum gcd`), and `psc.leftmost_chain.terminal_leftmost_cycles` counts
them. The literal box graph of LC5 costs about 0.2 s per substitution in
`box_radii` alone (the corpus driver `leftmost_chain_census.mojo` runs for
minutes), so here the leftmost function is walked on the box start states of
`stable_radii` closed under the leftmost step only: that sub-automaton of the
overlap graph contains every vertex of every terminal leftmost cycle
(`leftmost_closure`), so its cycles are those of the box graph. Every
`STRIDE`-th specimen and the named fixtures are also replayed on the literal
`build_box_graph`, whose radii come from the independent Sturm--Tarski bound.

Run time: about two minutes on one core, of which the census is twenty
seconds and the leftmost cross-check the rest.

Nothing here certifies a coincidence rank, strong coincidence or pure
discrete spectrum, and no claim status changes: the census counts classes.
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import Mat3
from psc.bpa import apply_substitution, substitution_incidence
from psc.c4_geometric_f import (
    CELL_DET_ODD,
    CELL_F,
    CELL_H1_AT_MOST_4,
    CELL_LEFT_TRIVIAL,
    CELL_PARITY,
    CELL_RIGHT_TRIVIAL,
    GEOMETRIC_F_STATE_CAP,
    GeometricFCensus,
    OrbitMemo,
    PrototileMap,
    PrototileState,
    StableRadiiCache,
    decide_geometric_f,
    decide_geometric_f_from,
    fc3_profile,
    fixed_ray_overlaps,
    fixed_ray_relative_states,
    geometric_f_census,
    interior_address,
    joint_period,
    matrix_digits,
    pair_transient,
    periodic_first_letter_pairs,
    predicted_leftmost_cycles,
    principal_minor_sum,
    stable_radii,
)
from psc.corpus import STATE_CAP, pip_corpus
from psc.endpoint_core import prefix_endpoint_map
from psc.leftmost_chain import leftmost_step, terminal_leftmost_cycles
from psc.overlap_seed_patch import OverlapState, SeedOverlapAutomaton, SeedOverlapTables
from psc.periodic_pair import centre_offset, interior_occurrences
from psc.perron_field3 import CubicElt
from psc.vertex_coincidence import box_radii, box_start_states, build_box_graph

# Every STRIDE-th corpus specimen replays the leftmost cross-check on the
# literal box graph of Corollary LC5, and the (F) decision in a box of twice
# the certified radii.
comptime STRIDE = 97


def tribonacci() -> List[List[Int]]:
    return [[0, 1], [0, 2], [0]]


def interior_control() -> List[List[Int]]:
    return [[0, 1], [1, 2], [0, 2, 1]]


def test_tribonacci_satisfies_f() raises:
    var sigma = tribonacci()
    var v = decide_geometric_f(sigma)
    assert_true(v.holds)
    assert_equal(len(v.cycles), 0)
    assert_equal(v.first_period(), 0)
    assert_true(v.candidates > 0)
    var prediction = predicted_leftmost_cycles(sigma, v)
    assert_equal(prediction.cycles, 0)
    assert_equal(prediction.longest, 0)
    # The first-letter map is constant, so there is no pair of fixed rays.
    assert_equal(len(periodic_first_letter_pairs(sigma)), 0)
    # Vertex states are forward invariant: f(j, 0) = (g(j), 0).
    var m = PrototileMap(sigma)
    for j in range(3):
        var step = m.step(PrototileState(j, 0, 0, 0))
        assert_equal(step.child, PrototileState(0, 0, 0, 0))
        assert_equal(step.index, 0)


def test_interior_periodic_address_of_01_12_021() raises:
    """`0 -> 01, 1 -> 12, 2 -> 021`. By hand: `sigma(2) = 0 . 2 . 1` is an
    interior occurrence of `2` with `P = "0"`, `p(P) = e_0`. The incidence
    matrix has rows `(1,0,1), (1,1,1), (0,1,1)`, so `(M - I) v = e_0` reads
    `v_2 = 1`, `v_0 + v_2 = 0`, `v_1 = 0`: `v = (-1, 0, 1)`, and the position
    `ell_2 - ell_0` lies in `(0, ell_2)`. So `(2, (-1, 0, 1))` is an f-fixed
    state with `v != 0` and (F) fails."""
    var sigma = interior_control()
    var m = PrototileMap(sigma)
    var v = decide_geometric_f(sigma)
    assert_false(v.holds)
    assert_equal(len(v.cycles), 1)
    assert_equal(v.first_period(), 1)
    assert_equal(v.cycles[0].period(), 1)
    var fixed = PrototileState(2, -1, 0, 1)
    assert_equal(v.cycles[0].states[0], fixed)
    assert_equal(v.cycles[0].indices[0], 1)
    assert_true(m.is_state(fixed))
    assert_equal(m.step(fixed).child, fixed)

    var a = interior_address(m, v.cycles[0], 0)
    assert_equal(a.letter, 2)
    assert_equal(a.vector, List[Int]([-1, 0, 1]))
    assert_equal(a.period, 1)
    assert_equal(a.prefix_parikh, List[Int]([1, 0, 0]))
    assert_equal(a.prefix_length, 1)
    assert_equal(a.image_length, 3)

    # (M^k - I) v = p(P), spelled out with the matrix written by hand.
    var by_hand: List[Int] = [1, 0, 1, 1, 1, 1, 0, 1, 1]
    assert_equal(substitution_incidence(sigma), by_hand)
    var image = Mat3(by_hand).apply(a.vector)
    for i in range(3):
        assert_equal(image[i] - a.vector[i], a.prefix_parikh[i])

    # The same address from the word, independently of the state map.
    var occurrences = interior_occurrences(sigma, 2, 1)
    assert_equal(len(occurrences), 1)
    assert_equal(occurrences[0].index, 1)
    assert_equal(occurrences[0].prefix, List[Int]([1, 0, 0]))
    var zero: List[Int] = [0, 0, 0]
    assert_equal(centre_offset(sigma, 1, occurrences[0].prefix, zero), List[Int]([-1, 0, 1]))

    # Two fixed first letters, so 2 * (gcd(1, 1) + gcd(1, 1)) = 4 terminal
    # leftmost cycles, each of length 1; the literal box graph agrees.
    var prediction = predicted_leftmost_cycles(sigma, v)
    assert_equal(prediction.cycles, 4)
    assert_equal(prediction.longest, 1)
    assert_equal(literal_cycle_count(sigma), 4)

    # Its fixed rays through 0 and 1 reach the interior cycle: FC1 is silent.
    assert_equal(len(periodic_first_letter_pairs(sigma)), 1)
    var memo = OrbitMemo(v)
    var t = pair_transient(m, memo, 0, 1)
    assert_equal(t.period, 1)
    assert_equal(t.relative_states, 19)
    assert_equal(t.absorbed, 2)
    assert_false(t.all_reach_vertices())


def literal_cycle_count(sigma: List[List[Int]]) raises -> Int:
    """Terminal leftmost cycles of the literal box graph (Corollary LC5)."""
    var m = PrototileMap(sigma)
    return len(terminal_leftmost_cycles(m.tables, build_box_graph(m.tables), 0))


def test_leftmost_chain_pins_are_recovered() raises:
    """The pins of `test_leftmost_chain.mojo`, from the interior f-cycles:
    `1/12/022` has two terminal cycles of length 1 with `w0 = (0, 1, -1)`,
    i.e. the f-fixed state `(2, -w0)`; `1/012/010` two of length 6;
    `1/22/012` two of length 15."""
    var small: List[List[Int]] = [[1], [1, 2], [0, 2, 2]]
    var vs = decide_geometric_f(small)
    assert_equal(len(vs.cycles), 1)
    assert_equal(vs.cycles[0].period(), 1)
    assert_equal(vs.cycles[0].states[0], PrototileState(2, 0, -1, 1))
    var ps = predicted_leftmost_cycles(small, vs)
    assert_equal(ps.cycles, 2)
    assert_equal(ps.longest, 1)
    assert_equal(literal_cycle_count(small), 2)

    var short: List[List[Int]] = [[1], [0, 1, 2], [0, 1, 0]]
    var vsh = decide_geometric_f(short)
    assert_equal(len(vsh.cycles), 1)
    assert_equal(vsh.cycles[0].period(), 3)
    var psh = predicted_leftmost_cycles(short, vsh)
    assert_equal(psh.cycles, 2)
    assert_equal(psh.longest, 6)
    assert_equal(literal_cycle_count(short), 2)

    var long: List[List[Int]] = [[1], [2, 2], [0, 1, 2]]
    var mlong = PrototileMap(long)
    var vl = decide_geometric_f(long)
    assert_equal(len(vl.cycles), 1)
    assert_equal(vl.cycles[0].period(), 5)
    # r = 15 is past the integer range of the adjugate route of the LC test;
    # the address equation of the period-5 f-cycle is replayed exactly here.
    var a0 = interior_address(mlong, vl.cycles[0], 0)
    assert_equal(a0.letter, 0)
    assert_equal(a0.vector, List[Int]([1, 1, -1]))
    assert_equal(a0.prefix_parikh, List[Int]([4, 5, 10]))
    assert_equal(a0.prefix_length, 19)
    assert_equal(a0.image_length, 28)
    for t in range(5):
        var a = interior_address(mlong, vl.cycles[0], t)
        assert_equal(a.period, 5)
        assert_true(a.prefix_length >= 1 and a.prefix_length <= a.image_length - 2)
    var pl = predicted_leftmost_cycles(long, vl)
    assert_equal(pl.cycles, 2)
    assert_equal(pl.longest, 15)
    assert_equal(literal_cycle_count(long), 2)


def ray_prefix(sigma: List[List[Int]], c: Int, period: Int, length: Int) raises -> List[Int]:
    """The first `length` letters of the `sigma^period`-fixed ray through `c`."""
    var w: List[Int] = [c]
    while len(w) < length:
        var longer = w.copy()
        for _ in range(period):
            longer = apply_substitution(sigma, longer)
        if len(longer) <= len(w) or longer[0] != c:
            raise Error("ray prefix: not a growing fixed ray")
        w = longer^
    var out = List[Int]()
    for i in range(length):
        out.append(w[i])
    return out^


def literal_relative_states(
    mut m: PrototileMap, top: List[Int], bottom: List[Int], mut out: Dict[PrototileState, Bool]
) raises:
    """The definition, word by word: for each vertex `y` of the top ray, the
    tile of the bottom ray that contains the point `y`, and `y` seen from its
    left vertex. Stops where the bottom prefix ends."""
    var y: List[Int] = [0, 0, 0]
    var left: List[Int] = [0, 0, 0]
    var j = 0
    for i in range(len(top)):
        while j + 1 < len(bottom):
            # the next bottom vertex is left + e_{bottom[j]}; advance while it is <= y
            var gap = PrototileState(0, y[0] - left[0], y[1] - left[1], y[2] - left[2])
            if m.sign(m.position(gap) - m.tables.lengths.at(bottom[j])) < 0:
                break
            left[bottom[j]] += 1
            j += 1
        if j + 1 >= len(bottom):
            break
        out[PrototileState(bottom[j], y[0] - left[0], y[1] - left[1], y[2] - left[2])] = True
        y[top[i]] += 1


def literal_pair(
    mut m: PrototileMap, c: Int, d: Int, period: Int, length: Int
) raises -> Dict[PrototileState, Bool]:
    """Relative states read off `length`-letter prefixes, both orientations."""
    var wc = ray_prefix(m.tables.sigma, c, period, length)
    var wd = ray_prefix(m.tables.sigma, d, period, length)
    var out = Dict[PrototileState, Bool]()
    literal_relative_states(m, wc, wd, out)
    literal_relative_states(m, wd, wc, out)
    return out^


def test_fixed_ray_relative_states_match_the_literal_definition() raises:
    """`0 -> 1, 1 -> 2, 2 -> 02`: the first-letter map is a 3-cycle, so the
    three rays are `sigma^3`-fixed. The overlap-closure set of relative states
    equals the set read off 3,000-letter prefixes, 11 states per pair, and the
    transient is 7."""
    var sigma: List[List[Int]] = [[1], [2], [0, 2]]
    var m = PrototileMap(sigma)
    var v = decide_geometric_f(sigma)
    assert_true(v.holds)
    var pairs = periodic_first_letter_pairs(sigma)
    assert_equal(len(pairs), 3)
    var memo = OrbitMemo(v)
    for p in range(3):
        var c = pairs[p].a
        var d = pairs[p].b
        assert_equal(joint_period(prefix_endpoint_map(sigma), c, d), 3)
        var closure = fixed_ray_relative_states(m, c, d)
        var literal = literal_pair(m, c, d, 3, 3000)
        for i in range(len(closure)):
            assert_true(closure[i] in literal)
        assert_equal(len(literal), len(closure))
        assert_equal(len(closure), 11)
        var t = pair_transient(m, memo, c, d)
        assert_equal(t.period, 3)
        assert_equal(t.overlaps, 31)
        assert_equal(t.relative_states, 11)
        assert_true(t.all_reach_vertices())
        assert_equal(t.transient, 7)


def test_a_ray_prefix_is_not_the_set_of_relative_states() raises:
    """`0 -> 1, 1 -> 012, 2 -> 100`, the pair `(0, 1)` of period 2. The two
    rays have 240 relative states and transient 51. A 3,000-letter prefix of
    each ray shows 60 of them, all inside the closure, with transient 36: the
    prefix scan that the scratch census of this increment used is a lower
    bound, not the transient."""
    var sigma: List[List[Int]] = [[1], [0, 1, 2], [1, 0, 0]]
    var m = PrototileMap(sigma)
    var v = decide_geometric_f(sigma)
    assert_true(v.holds)
    var memo = OrbitMemo(v)
    var t = pair_transient(m, memo, 0, 1)
    assert_equal(t.period, 2)
    assert_equal(t.overlaps, 1213)
    assert_equal(t.relative_states, 240)
    assert_true(t.all_reach_vertices())
    assert_equal(t.transient, 51)

    var closure = fixed_ray_relative_states(m, 0, 1)
    var closed = Dict[PrototileState, Bool]()
    for i in range(len(closure)):
        closed[closure[i]] = True
    var literal = literal_pair(m, 0, 1, 2, 3000)
    assert_equal(len(literal), 60)
    var seen_longest = 0
    for s in literal.keys():
        assert_true(s in closed)
        var n = memo.transient(m, s)
        assert_true(n >= 0)
        if n > seen_longest:
            seen_longest = n
    assert_equal(seen_longest, 36)


def raises_on(sigma: List[List[Int]]) -> Bool:
    try:
        _ = decide_geometric_f(sigma)
        return False
    except:
        return True


def test_refusals() raises:
    # Reducible: chi = (x - 1)(x^2 - 2x - 2). Primitive, with a strict system.
    assert_true(raises_on([[1, 0], [1, 0, 2], [2, 1, 1]]))
    # Thue-Morse: two letters.
    assert_true(raises_on([[0, 1], [1, 0]]))
    # Thue-Morse-like on three letters: constant length, chi = x^2 (x - 3).
    assert_true(raises_on([[0, 1, 2], [1, 2, 0], [2, 0, 1]]))
    # Not primitive.
    assert_true(raises_on([[0, 0], [1, 1], [2, 2]]))
    # A letter outside the alphabet and an empty image.
    assert_true(raises_on([[0, 3], [0, 2], [0]]))
    assert_true(raises_on([[0, 1], List[Int](), [0]]))

    # A state cap is an exhausted budget, never a verdict.
    var capped = False
    try:
        _ = decide_geometric_f(interior_control(), 1)
    except:
        capped = True
    assert_true(capped)
    var m = PrototileMap(interior_control())
    var ray_capped = False
    try:
        _ = fixed_ray_overlaps(m, 0, 1, 1)
    except:
        ray_capped = True
    assert_true(ray_capped)
    assert_equal(len(fixed_ray_overlaps(m, 0, 1, STATE_CAP).overlaps), 69)

    # A point outside its tile is not a state and has no image.
    assert_false(m.is_state(PrototileState(2, 1, 0, -1)))
    var stepped = False
    try:
        _ = m.step(PrototileState(2, 1, 0, -1))
    except:
        stepped = True
    assert_true(stepped)
    assert_false(m.is_state(PrototileState(0, 5, 5, 5)))
    var beyond = False
    try:
        _ = m.step(PrototileState(0, 5, 5, 5))
    except:
        beyond = True
    assert_true(beyond)

    # Letter 2 is not periodic under the first-letter map 0 -> 0, 1 -> 1, 2 -> 0.
    var not_periodic = False
    try:
        _ = joint_period([0, 1, 0], 0, 2)
    except:
        not_periodic = True
    assert_true(not_periodic)
    assert_equal(joint_period([0, 1, 0], 0, 1), 1)
    assert_equal(joint_period([1, 2, 0], 0, 2), 3)
    assert_equal(joint_period([1, 0, 2], 0, 1), 2)

    # An orbit that closes on a cycle the verdict did not certify raises: here
    # the interior fixed state of 01/12/021 against an empty certificate.
    var empty = decide_geometric_f(tribonacci())
    assert_true(empty.holds)
    var memo = OrbitMemo(empty)
    var uncertified = False
    try:
        _ = memo.transient(m, PrototileState(2, -1, 0, 1))
    except:
        uncertified = True
    assert_true(uncertified)

    # A box that is too small is a different question, not a verdict on (F):
    # radius 0 holds no state with v != 0, so nothing is found.
    var zero_box: List[Int] = [0, 0, 0]
    assert_equal(len(decide_geometric_f_from(m, zero_box).cycles), 0)


def test_the_certified_radii() raises:
    """`stable_radii` on the fixtures: the box contains the interior states
    found, and neither twice the radii nor the independent Sturm--Tarski radii
    of the box graph (valid for every overlap cycle, hence for every f-cycle)
    find anything else."""
    var t = PrototileMap(tribonacci())
    # D_M for Tribonacci: the proper nonzero sub-vectors of (1, 1, 0) and
    # (1, 0, 1), i.e. e_0, e_1, e_2: three positions.
    assert_equal(len(matrix_digits(t.tables)), 3)
    var fixtures: List[List[List[Int]]] = [
        tribonacci(), interior_control(), [[1], [1, 2], [0, 2, 2]], [[1], [0, 1, 2], [0, 1, 0]], [[1], [2, 2], [0, 1, 2]],
    ]
    for i in range(len(fixtures)):
        var m = PrototileMap(fixtures[i])
        var radii = stable_radii(m.tables)
        var reference = box_radii(m.tables)
        assert_equal(len(radii), 3)
        var v = decide_geometric_f_from(m, radii)
        for c in range(len(v.cycles)):
            for k in range(v.cycles[c].period()):
                var w = v.cycles[c].states[k].vector()
                for a in range(3):
                    assert_true(w[a] >= -radii[a] and w[a] <= radii[a])
        var doubled: List[Int] = [2 * radii[0], 2 * radii[1], 2 * radii[2]]
        var wide = decide_geometric_f_from(m, doubled)
        var independent = decide_geometric_f_from(m, reference)
        assert_equal(len(wide.cycles), len(v.cycles))
        assert_equal(len(independent.cycles), len(v.cycles))
        for c in range(len(v.cycles)):
            assert_equal(wide.cycles[c].states[0], v.cycles[c].states[0])
            assert_equal(wide.cycles[c].period(), v.cycles[c].period())
            assert_equal(independent.cycles[c].states[0], v.cycles[c].states[0])
            assert_equal(independent.cycles[c].period(), v.cycles[c].period())


def vertex_set(w: List[Int]) -> Dict[PrototileState, Bool]:
    """The Parikh vectors of the proper prefixes of `w`: the vertices."""
    var out = Dict[PrototileState, Bool]()
    var y: List[Int] = [0, 0, 0]
    for i in range(len(w)):
        out[PrototileState(0, y[0], y[1], y[2])] = True
        y[w[i]] += 1
    return out^


def test_fc1_inclusion_on_words() raises:
    """Theorem FC1 read off words alone, with no state map. For
    `0 -> 1, 1 -> 2, 2 -> 02` every pair has period 3 and transient 7, so
    `N' = 3`: `M^9 y` is a common vertex of both rays for every vertex `y` of
    either, while `M^6 y` is not for some `y` -- two periods are too few."""
    var sigma: List[List[Int]] = [[1], [2], [0, 2]]
    var incidence = Mat3(substitution_incidence(sigma))
    var m3 = incidence * incidence * incidence
    var m6 = m3 * m3
    var m9 = m6 * m3
    var pairs = periodic_first_letter_pairs(sigma)
    assert_equal(len(pairs), 3)
    for p in range(3):
        var words = List[List[Int]]()
        words.append(ray_prefix(sigma, pairs[p].a, 3, 3000))
        words.append(ray_prefix(sigma, pairs[p].b, 3, 3000))
        var first = vertex_set(words[0])
        var second = vertex_set(words[1])
        var early = 0
        for side in range(2):
            var y: List[Int] = [0, 0, 0]
            for i in range(60):
                var z = m9.apply(y)
                assert_true(z[0] + z[1] + z[2] < 3000)
                var key = PrototileState(0, z[0], z[1], z[2])
                assert_true(key in first)
                assert_true(key in second)
                var u = m6.apply(y)
                var short_key = PrototileState(0, u[0], u[1], u[2])
                if short_key not in first or short_key not in second:
                    early += 1
                y[words[side][i]] += 1
        assert_true(early > 0)


def leftmost_closure(tables: SeedOverlapTables, radii: List[Int]) raises -> SeedOverlapAutomaton:
    """The box start states closed under the leftmost step only.

    Along a leftmost chain one of the two indices is 0 at every step (Lemma S
    of the LC note), so the offset vector of every vertex of a terminal
    leftmost cycle obeys Lemma B of `psc.c4_geometric_f` and lies in the box
    of `stable_radii`: it is one of the box start states. The leftmost child
    is a child, so this sub-automaton of the overlap graph is closed under the
    leftmost step and has the same terminal leftmost cycles as the box graph,
    without the full inflation closure. `terminal_leftmost_cycles` reads only
    the states."""
    var cache = Dict[CubicElt, Int]()
    var starts = box_start_states(tables, radii, cache)
    var states = List[OverlapState]()
    var adj = List[List[Int]]()
    var seen = Dict[OverlapState, Bool]()
    for i in range(len(starts)):
        var s = starts[i]
        while s not in seen:
            seen[s] = True
            states.append(s)
            adj.append(List[Int]())
            if s.shift.is_zero():
                break
            s = leftmost_step(tables, cache, s).child
    return SeedOverlapAutomaton(states, adj, False)


def test_corpus() raises -> GeometricFCensus:
    var corpus = pip_corpus()
    assert_equal(len(corpus), 4554)
    var census = geometric_f_census(corpus)
    assert_equal(census.total, 4554)
    assert_equal(census.cells.total(), 4554)

    # (F) and its interior cycles.
    assert_equal(census.count_where(CELL_F, CELL_F), 1794)
    assert_equal(census.reversal_missing, 0)
    assert_equal(census.reversal_mismatches, 0)
    var periods: List[List[Int]] = [
        [1, 816], [2, 252], [3, 744], [4, 228], [5, 492], [6, 12], [7, 24], [8, 72], [10, 84], [11, 12], [13, 24],
    ]
    var period_total = 0
    for row in periods:
        assert_equal(census.first_period.count(row[0]), row[1])
        period_total += row[1]
    assert_equal(period_total, 2760)
    assert_equal(census.first_period.total(), 2760)
    assert_equal(census.interior_cycles.count(0), 1794)
    assert_equal(census.interior_cycles.count(1), 1860)
    assert_equal(census.interior_cycles.count(2), 804)
    assert_equal(census.interior_cycles.count(3), 96)
    assert_equal(census.interior_cycles.total(), 4554)
    assert_equal(census.interior_cycle_total, 3756)
    assert_equal(census.interior_state_total, 12828)
    assert_equal(census.longest_period, 13)
    assert_true(census.peak_visited < GEOMETRIC_F_STATE_CAP // 10)
    assert_true(census.peak_nodes < STATE_CAP // 2)

    # The bridge to psc.leftmost_chain reproduces the census of the LC note.
    assert_equal(census.leftmost_cycles, 10584)
    assert_equal(census.leftmost_longest, 39)
    assert_equal(census.leftmost_specimens, 2760)

    # Theorem FC1.
    assert_equal(census.f_pairs, 1956)
    assert_equal(census.f_pairs_absorbed, 0)
    assert_equal(census.f_relative_states, 97992)
    assert_equal(census.transients.total(), 1956)
    assert_equal(census.transients.maximum(), 51)
    assert_equal(census.transients.count(51), 24)
    assert_equal(census.transients.count(38), 0)
    assert_equal(census.nonf_pairs, 2790)
    assert_equal(census.nonf_pairs_absorbed, 2790)

    # Theorem P: the odd-determinant classes.
    var odd = CELL_DET_ODD
    assert_equal(census.count_where(odd, odd), 2628)
    assert_equal(census.count_where(odd | CELL_H1_AT_MOST_4, odd | CELL_H1_AT_MOST_4), 2136)
    assert_equal(census.count_where(odd | CELL_PARITY, odd | CELL_PARITY), 1344)
    assert_equal(census.count_where(odd | CELL_H1_AT_MOST_4 | CELL_PARITY, odd), 276)
    assert_equal(2628 - 276, 2352)

    # Theorem FC3 on the (F) class.
    var ends = CELL_LEFT_TRIVIAL | CELL_RIGHT_TRIVIAL
    var open_ends = CELL_F | ends
    assert_equal(census.count_where(open_ends, CELL_F), 510)
    assert_equal(1794 - 510, 1284)
    assert_equal(census.count_where(open_ends | odd | CELL_H1_AT_MOST_4, CELL_F | odd | CELL_H1_AT_MOST_4), 84)
    assert_equal(census.count_where(open_ends | odd | CELL_PARITY, CELL_F | odd | CELL_PARITY), 120)
    assert_equal(census.count_where(open_ends | odd, CELL_F), 174)
    assert_equal(census.count_where(open_ends | odd | CELL_H1_AT_MOST_4 | CELL_PARITY, CELL_F | odd), 180)
    assert_equal(510 - 174 - 180, 156)
    assert_equal(census.residual_determinant.total(), 354)
    assert_equal(census.residual_determinant.count(2 + 8), 174)
    assert_equal(census.residual_determinant.count(1 + 8) + census.residual_determinant.count(-1 + 8), 180)

    # (F) <=> no terminal leftmost cycle, specimen by specimen, with the count.
    var boxes = StableRadiiCache()
    var literal = 0
    var leftmost_total = 0
    var leftmost_longest = 0
    var cycle_free = 0
    var undersized_cycles = 0
    var undersized_f = 0
    for s in range(len(corpus)):
        var m = PrototileMap(corpus[s].sigma)
        var radii = boxes.radii_for(m.tables)
        var cycles = terminal_leftmost_cycles(m.tables, leftmost_closure(m.tables, radii), 0)
        assert_equal(len(cycles), census.leftmost_predicted[s])
        assert_equal(len(cycles) == 0, census.holds[s])
        leftmost_total += len(cycles)
        if len(cycles) == 0:
            cycle_free += 1
        for k in range(len(cycles)):
            if cycles[k].r > leftmost_longest:
                leftmost_longest = cycles[k].r
        # Counter-calibration: half the certified radii is not a certificate.
        var halved: List[Int] = [max(1, radii[0] // 2), max(1, radii[1] // 2), max(1, radii[2] // 2)]
        var undersized = decide_geometric_f_from(m, halved)
        assert_true(len(undersized.cycles) <= census.cycle_counts[s])
        undersized_cycles += len(undersized.cycles)
        if undersized.holds:
            undersized_f += 1
        if s % STRIDE == 0:
            literal += 1
            assert_equal(len(terminal_leftmost_cycles(m.tables, build_box_graph(m.tables), 0)), census.leftmost_predicted[s])
            var doubled: List[Int] = [2 * radii[0], 2 * radii[1], 2 * radii[2]]
            assert_equal(len(decide_geometric_f_from(m, doubled).cycles), census.cycle_counts[s])
    assert_equal(boxes.distinct_matrices(), 348)
    assert_equal(leftmost_total, 10584)
    assert_equal(leftmost_longest, 39)
    assert_equal(cycle_free, 1794)
    assert_equal(literal, 47)
    # The halved box misses interior cycles and so over-reports (F): the pins
    # above would not survive an undersized bound.
    assert_true(undersized_cycles < census.interior_cycle_total)
    assert_true(undersized_f > 1794)
    return census^


def test_arithmetic_profile_fixtures() raises:
    # Tribonacci: chi = x^3 - x^2 - x - 1, so tr = 1, e_2 = -1, det = 1.
    var t = fc3_profile(tribonacci())
    assert_equal(t.determinant, 1)
    assert_equal(t.trace, 1)
    assert_equal(t.e2, -1)
    assert_equal(t.h1_dimension, 3)
    assert_equal(t.left_periodic, 1)
    assert_equal(t.right_periodic, 3)
    assert_true(t.det_odd())
    assert_false(t.parity_clause())
    assert_true(t.cohomology_clause())
    assert_true(t.endpoint_trivial())
    # 01/12/021: chi = x^3 - 3x^2 + 2x - 1; tr = 3, e_2 = 2, det = 1; dim H^1 = 4.
    var c = fc3_profile(interior_control())
    assert_equal(c.determinant, 1)
    assert_equal(c.trace, 3)
    assert_equal(c.e2, 2)
    assert_equal(c.h1_dimension, 4)
    assert_equal(c.left_periodic, 2)
    assert_equal(c.right_periodic, 2)
    assert_true(c.parity_clause())
    assert_false(c.endpoint_trivial())
    assert_true(c.arithmetic_clause())
    # e_2 is the linear coefficient of the characteristic polynomial.
    var m = Mat3(substitution_incidence(interior_control()))
    assert_equal(principal_minor_sum(m), m.charpoly()[1])


def main() raises:
    test_tribonacci_satisfies_f()
    test_interior_periodic_address_of_01_12_021()
    test_leftmost_chain_pins_are_recovered()
    test_fixed_ray_relative_states_match_the_literal_definition()
    test_a_ray_prefix_is_not_the_set_of_relative_states()
    test_refusals()
    test_the_certified_radii()
    test_fc1_inclusion_on_words()
    test_arithmetic_profile_fixtures()
    var census = test_corpus()
    var odd = CELL_DET_ODD
    var open_ends = CELL_F | CELL_LEFT_TRIVIAL | CELL_RIGHT_TRIVIAL
    print(
        "geometric (F):", census.count_where(CELL_F, CELL_F), "of", census.total,
        "specimens, reversal mismatches", census.reversal_mismatches, ";",
        census.interior_cycle_total, "interior f-cycles,", census.first_period.line("first period"), ";",
        "terminal leftmost cycles", census.leftmost_cycles, "on", census.leftmost_specimens,
        "specimens, longest", census.leftmost_longest, "; FC1:", census.f_pairs, "(F) pairs,",
        census.f_pairs_absorbed, "absorbed,", census.transients.line("transients"), ";",
        census.nonf_pairs_absorbed, "of", census.nonf_pairs, "non-(F) pairs absorbed; odd det",
        census.count_where(odd, odd), ", with dim H^1 <= 4:",
        census.count_where(odd | CELL_H1_AT_MOST_4, odd | CELL_H1_AT_MOST_4), ", or tr != e_2:",
        census.count_where(odd, odd) - census.count_where(odd | CELL_H1_AT_MOST_4 | CELL_PARITY, odd),
        "; (F) with two periodic letters on both sides:", census.count_where(open_ends, CELL_F),
        ", not reached by FC3:", census.residual_determinant.total(),
        "; peak candidates / visited states / closure nodes:",
        census.peak_candidates, census.peak_visited, census.peak_nodes,
    )
    require_contract("Geometric property (F) of ternary irreducible Pisot substitutions (psc.c4_geometric_f), exact integer and Z[beta] arithmetic: the prototile state map f(j, v) = (j', M v - p(P)); (F) decided by walking every state with v != 0 inside the box of stable_radii (Lemma B: per incidence matrix, outward-rounded rational intervals), every interior f-cycle replaying (M^k - I) v = p(P) at an interior occurrence. Fixtures: Tribonacci 01/02/0 has (F); 01/12/021 has the f-fixed state (2, (-1, 0, 1)) with (M - I) v = e_0 = p(P) for P = 0 in sigma(2) = 0.2.1, re-derived from the word, and 4 terminal leftmost cycles; 1/12/022, 1/012/010 and 1/22/012 have one interior cycle of period 1, 3, 5 and recover the leftmost-chain pins (2 cycles of length 1, 6, 15); 1/2/02 has 11 relative states per pair, equal to the set read off 3,000-letter ray prefixes, transient 7, and M^9 sends the first 60 vertices of each ray to common vertices while M^6 does not; 1/012/100 pair (0, 1) has 240 relative states and transient 51 where a 3,000-letter prefix shows 60 states and transient 36. Refusals: the reducible 10/102/211, Thue-Morse, 012/120/201, non-primitive and malformed input raise; state and overlap caps raise; a point outside its tile has no image; an orbit closing on an uncertified cycle raises. Corpus, 4,554 specimens on 348 incidence matrices: (F) on 1,794, invariant under image reversal on all 4,554; 3,756 interior cycles with 12,828 states, longest period 13, 0/1/2/3 cycles on 1794/1860/804/96 specimens; least interior period over the other 2,760: 1:816 2:252 3:744 4:228 5:492 6:12 7:24 8:72 10:84 11:12 13:24; terminal leftmost cycles (psc.leftmost_chain on the leftmost closure of the box start states) = 2 sum gcd(|C|, |G|) on every specimen, 10,584 in all, longest 39, none exactly on the 1,794 (F) specimens, replayed on the literal box graph for every 97th specimen (47); half the certified radii miss cycles; Theorem FC1: 1,956 pairs of periodic first letters on (F) specimens, each of their 97,992 relative states reaches a vertex state, maximal transient 51 f-steps (24 pairs; the scratch value 38 was a 3,000-letter prefix scan), and 2,790 pairs on the other specimens, each with a relative state absorbed by an interior cycle; arithmetic classes: 2,628 odd determinants, of them 2,136 with dim H^1 <= 4, 1,344 with tr != e_2 (mod 2), 2,352 with either; of the 1,794 (F) specimens 1,284 have an endpoint map with fewer than two periodic letters, and of the other 510, 84 have odd det and dim H^1 <= 4, 120 odd det and tr != e_2, 156 either, 354 neither (174 with det 2, 180 odd). Class counts only: no coincidence rank, strong coincidence or pure discrete spectrum is certified, and no claim status changes")
