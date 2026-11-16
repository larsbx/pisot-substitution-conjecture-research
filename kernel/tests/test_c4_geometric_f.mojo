"""Exact regression for the geometric property (F) class (psc.c4_geometric_f).

docs/c4-geometric-f-class-2026-11-16.md. Named fixtures by hand, refusals,
the certified radii pinned (five fixtures, and their sums over the corpus),
the literal fixed-ray definition against the overlap-closure one, and the
corpus content of Theorems FC1, P and FC3 on all 4,554 standing specimens,
with (F) cross-checked against `psc.leftmost_chain` (Corollary LC5).

What guards the completeness of the (F) decision. The decision is exhaustive
because every f-periodic state lies in the box of `stable_radii` (Lemma B of
the module, a recorded proof, not machine-checked). The cycle pins below
cannot see a bound that is too small but still holds every interior cycle of
the corpus, and the leftmost cross-check on all specimens uses the same
radii. So the radii themselves are pinned, and the independent bound is
replayed: the box of `box_radii` on the fixtures, and the literal box graph,
which is built on `box_radii`, on the fixtures that fail (F) and on every
`STRIDE`-th specimen.

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

Round 2 (docs/c4-rank-two-wall-2026-11-16.md): the arithmetic profile also
carries `d_2 = 3 - ord_t(chi_M mod 2)`, the clause `dim H^1 = 3` for every
determinant (Theorem H3; with (F), Theorem FC3+) and the dimension bound of
Theorem P+ (`dim H^1 >= 3 + |d_2 - 1|` is necessary for coincidence rank 2).
The tables of (parity of `det M`, `d_2`, `dim H^1`) over the corpus and over
the 510 (F) specimens with two periodic letters on both sides are pinned,
and recomputed specimen by specimen with `d_2` as the rank over `F_2` of
`(M mod 2)^3`, `chi_M mod 2` from `Mat3.charpoly`, and periodic letters as
the fixed letters of the sixth power of an endpoint map, none of which the
module uses; `dim H^1` is `psc.h1_census.h1_profile` on both sides, and (F)
is the module's verdict. These are class counts under recorded conditional
theorems, not certificates of a coincidence rank. The divisor condition of
Theorem P+ and the refinement of Remark (3) after Theorem P of the class
note (Lemma S at the admissible `n < 6`) are not implemented.

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
    CELL_H1_THREE,
    CELL_LEFT_TRIVIAL,
    CELL_PARITY,
    CELL_RANK_BOUND,
    CELL_RIGHT_TRIVIAL,
    GEOMETRIC_F_STATE_CAP,
    GeometricFCensus,
    OrbitMemo,
    PrototileMap,
    PrototileState,
    StableRadiiCache,
    decide_geometric_f,
    decide_geometric_f_with,
    chi_mod2_code,
    fc3_profile,
    fc3_profile_of,
    fixed_ray_overlaps,
    fixed_ray_relative_states,
    geometric_f_census,
    interior_address,
    interior_cycles_in_box,
    joint_period,
    matrix_digits,
    nonzero_roots_mod2,
    pair_transient,
    periodic_first_letter_pairs,
    predicted_leftmost_cycles,
    principal_minor_sum,
    stable_radii,
)
from psc.corpus import STATE_CAP, pip_corpus
from psc.degree2_sieve import mod2
from psc.endpoint_core import prefix_endpoint_map, suffix_endpoint_map
from psc.field3 import discriminant
from psc.h1_census import h1_profile
from psc.histogram import Histogram
from psc.leftmost_chain import leftmost_step, terminal_leftmost_cycles
from psc.overlap_seed_patch import OverlapState, SeedOverlapAutomaton, SeedOverlapTables
from psc.periodic_pair import centre_offset, interior_occurrences
from psc.perron_field3 import CubicElt
from psc.pisot import is_irreducible_cubic, is_pisot_charpoly, is_primitive
from psc.vertex_coincidence import box_radii, box_start_states, build_box_graph

# Every STRIDE-th corpus specimen replays the leftmost cross-check on the
# literal box graph of Corollary LC5, and the search for interior cycles in a
# box of twice the certified radii.
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


def raises_on(sigma: List[List[Int]], expected: String) -> Bool:
    """`decide_geometric_f` refuses `sigma` with a message that contains
    `expected`. Any other failure is not the refusal under test."""
    try:
        _ = decide_geometric_f(sigma)
        return False
    except e:
        return expected in String(e)


def test_refusals() raises:
    var gate = "primitive irreducible Pisot"
    # Reducible: chi = (x - 1)(x^2 - 2x - 2). Primitive, with a strict system.
    assert_true(raises_on([[1, 0], [1, 0, 2], [2, 1, 1]], gate))
    # Thue-Morse: two letters.
    assert_true(raises_on([[0, 1], [1, 0]], "three substitution images"))
    # Thue-Morse-like on three letters: constant length, chi = x^2 (x - 3).
    assert_true(raises_on([[0, 1, 2], [1, 2, 0], [2, 0, 1]], gate))
    # Not primitive.
    assert_true(raises_on([[0, 0], [1, 1], [2, 2]], gate))
    # A letter outside the alphabet and an empty image.
    assert_true(raises_on([[0, 3], [0, 2], [0]], "outside 0..2"))
    assert_true(raises_on([[0, 1], List[Int](), [0]], "non-erasing"))

    # The arms of the PIP3 gate, one at a time.
    # Singular: 1/012/1.
    var singular: List[List[Int]] = [[1], [0, 1, 2], [1]]
    assert_equal(Mat3(substitution_incidence(singular)).det(), 0)
    assert_true(raises_on(singular, gate))
    # Primitive and irreducible, not Pisot: 1/2/001, chi = x^3 - x - 2.
    var not_pisot: List[List[Int]] = [[1], [2], [0, 0, 1]]
    var np = Mat3(substitution_incidence(not_pisot))
    assert_equal(np.charpoly(), List[Int]([-2, -1, 0, 1]))
    assert_true(is_primitive(np))
    assert_true(is_irreducible_cubic(np.charpoly()))
    assert_false(is_pisot_charpoly(np.charpoly()))
    assert_true(raises_on(not_pisot, gate))
    # Primitive and reducible, with an irrational Pisot inflation and a strict
    # system (test_c4_reducible_pisot_controls): 011/120/2012.
    var reducible: List[List[Int]] = [[0, 1, 1], [1, 2, 0], [2, 0, 1, 2]]
    var rm = Mat3(substitution_incidence(reducible))
    assert_true(is_primitive(rm))
    assert_false(is_irreducible_cubic(rm.charpoly()))
    assert_true(raises_on(reducible, gate))
    # An image of length 7 is outside the audited image-length domain:
    # (0^5 1, 1 2 0^5, 0^6) is refused, not decided.
    var long_image: List[List[Int]] = [[0, 0, 0, 0, 0, 1], [1, 2, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]
    assert_true(raises_on(long_image, "certified only for"))

    # A state cap is an exhausted budget, never a verdict.
    var capped = False
    try:
        _ = decide_geometric_f(interior_control(), 1)
    except e:
        capped = "state cap reached" in String(e)
    assert_true(capped)
    var m = PrototileMap(interior_control())
    var ray_capped = False
    try:
        _ = fixed_ray_overlaps(m, 0, 1, 1)
    except e:
        ray_capped = "overlap cap reached" in String(e)
    assert_true(ray_capped)
    assert_equal(len(fixed_ray_overlaps(m, 0, 1, STATE_CAP).overlaps), 69)

    # A point outside its tile is not a state and has no image.
    assert_false(m.is_state(PrototileState(2, 1, 0, -1)))
    var stepped = False
    try:
        _ = m.step(PrototileState(2, 1, 0, -1))
    except e:
        stepped = "not a state" in String(e)
    assert_true(stepped)
    assert_false(m.is_state(PrototileState(0, 5, 5, 5)))
    var beyond = False
    try:
        _ = m.step(PrototileState(0, 5, 5, 5))
    except e:
        beyond = "not a state" in String(e)
    assert_true(beyond)

    # Letter 2 is not periodic under the first-letter map 0 -> 0, 1 -> 1, 2 -> 0.
    var not_periodic = False
    try:
        _ = joint_period([0, 1, 0], 0, 2)
    except e:
        not_periodic = "not periodic under the first-letter map" in String(e)
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
    except e:
        uncertified = "outside the certified box" in String(e)
    assert_true(uncertified)

    # A search in a box that is not certified is a different question and
    # returns no verdict on (F). Radius 0 holds no state with v != 0, so the
    # search of 01/12/021 finds nothing, although 01/12/021 fails (F): a
    # `BoxSearch` has no `holds`, and only `decide_geometric_f` and
    # `decide_geometric_f_with`, which take the box from `stable_radii`,
    # return a verdict.
    var zero_box: List[Int] = [0, 0, 0]
    var nothing = interior_cycles_in_box(m, zero_box)
    assert_equal(nothing.candidates, 0)
    assert_equal(len(nothing.cycles), 0)
    assert_false(decide_geometric_f(interior_control()).holds)


def test_the_certified_radii() raises:
    """`stable_radii` on the fixtures, pinned: the box contains the interior
    states found, and neither twice the radii nor the independent
    Sturm--Tarski radii of the box graph (valid for every overlap cycle, hence
    for every f-cycle) find anything else.

    The pins are what guards `stable_radii`. A bound that is too small but
    still holds every interior cycle of the corpus would pass every cycle pin
    of this file. The pinned values are what the module returns; they were
    compared with a high-precision evaluation of the right-hand side of Lemma
    B, step 3 (its floor, coordinate by coordinate) in the audit of
    2026-11-16, which is scratch and is not replayed here."""
    var t = PrototileMap(tribonacci())
    # D_M for Tribonacci: the proper nonzero sub-vectors of (1, 1, 0) and
    # (1, 0, 1), i.e. e_0, e_1, e_2: three positions.
    assert_equal(len(matrix_digits(t.tables)), 3)
    # The two functions use different increment sets and different rounding
    # (`stable_radii` takes the floor of its bound, `box_radii` rounds up), so
    # the returned radii are not comparable coordinate by coordinate: smaller
    # in one coordinate, larger in another.
    assert_equal(stable_radii(t.tables), List[Int]([2, 3, 4]))
    assert_equal(box_radii(t.tables), List[Int]([3, 3, 3]))
    var fixtures: List[List[List[Int]]] = [
        tribonacci(), interior_control(), [[1], [1, 2], [0, 2, 2]], [[1], [0, 1, 2], [0, 1, 0]], [[1], [2, 2], [0, 1, 2]],
    ]
    var pinned: List[List[Int]] = [[2, 3, 4], [4, 3, 3], [4, 5, 3], [26, 15, 16], [18, 15, 17]]
    var boxes = StableRadiiCache()
    for i in range(len(fixtures)):
        var m = PrototileMap(fixtures[i])
        var radii = stable_radii(m.tables)
        assert_equal(radii, pinned[i])
        var reference = box_radii(m.tables)
        # Both verdict entry points decide in that box and agree.
        var v = decide_geometric_f(fixtures[i])
        assert_equal(v.radii, pinned[i])
        var cached = decide_geometric_f_with(m, boxes)
        assert_equal(cached.radii, pinned[i])
        assert_equal(cached.holds, v.holds)
        assert_equal(cached.candidates, v.candidates)
        assert_equal(len(cached.cycles), len(v.cycles))
        for c in range(len(v.cycles)):
            for k in range(v.cycles[c].period()):
                var w = v.cycles[c].states[k].vector()
                for a in range(3):
                    assert_true(w[a] >= -radii[a] and w[a] <= radii[a])
        var doubled: List[Int] = [2 * radii[0], 2 * radii[1], 2 * radii[2]]
        var wide = interior_cycles_in_box(m, doubled)
        var independent = interior_cycles_in_box(m, reference)
        assert_equal(len(wide.cycles), len(v.cycles))
        assert_equal(len(independent.cycles), len(v.cycles))
        for c in range(len(v.cycles)):
            assert_equal(wide.cycles[c].states[0], v.cycles[c].states[0])
            assert_equal(wide.cycles[c].period(), v.cycles[c].period())
            assert_equal(independent.cycles[c].states[0], v.cycles[c].states[0])
            assert_equal(independent.cycles[c].period(), v.cycles[c].period())
    assert_equal(boxes.distinct_matrices(), 5)
    # The five fixtures all have a complex conjugate pair (negative
    # discriminant). 1/02/202 has discriminant 49: both conjugates are real,
    # the other branch of `stable_radii`.
    for i in range(len(fixtures)):
        assert_true(discriminant(PrototileMap(fixtures[i]).tables.field) < 0)
    var totally_real: List[List[Int]] = [[1], [0, 2], [2, 0, 2]]
    var real_map = PrototileMap(totally_real)
    assert_equal(discriminant(real_map.tables.field), 49)
    assert_equal(stable_radii(real_map.tables), List[Int]([4, 5, 3]))
    assert_equal(decide_geometric_f(totally_real).radii, List[Int]([4, 5, 3]))


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


def rank_mod2(m: Mat3) -> Int:
    """Rank over `F_2` of a 3x3 integer matrix, by elimination on its rows
    packed as three bits."""
    var rows = List[Int]()
    for i in range(3):
        var bits = 0
        for j in range(3):
            bits = 2 * bits + mod2(m.at(i, j))
        rows.append(bits)
    var rank = 0
    for bit in range(2, -1, -1):
        var pivot = -1
        for i in range(rank, 3):
            if (rows[i] >> bit) & 1 == 1:
                pivot = i
                break
        if pivot < 0:
            continue
        var swap = rows[rank]
        rows[rank] = rows[pivot]
        rows[pivot] = swap
        for i in range(3):
            if i != rank and (rows[i] >> bit) & 1 == 1:
                rows[i] = rows[i] ^ rows[rank]
        rank += 1
    return rank


def periodic_letters(h: List[Int]) -> Int:
    """Letters on a cycle of a self-map of three letters: the fixed letters
    of `h^6` (cycle lengths 1, 2, 3 divide 6, and a letter off every cycle is
    not fixed by any power)."""
    var n = 0
    for a in range(3):
        var x = a
        for _ in range(6):
            x = h[x]
        if x == a:
            n += 1
    return n


def test_d2_is_the_number_of_nonzero_roots_mod_2() raises:
    """All eight classes of `chi_M mod 2 = t^3 + a t^2 + b t + c`, code
    `4a + 2b + c`, factored by hand over `F_2`.

    0: t^3                    d_2 = 0      4: t^2 (t + 1)          d_2 = 1
    2: t (t + 1)^2            d_2 = 2      6: t (t^2 + t + 1)      d_2 = 2
    1: (t + 1)(t^2 + t + 1)   d_2 = 3      3: t^3 + t + 1          d_2 = 3
    5: t^3 + t^2 + 1          d_2 = 3      7: (t + 1)^3            d_2 = 3

    `d_2` is the degree of the part prime to `t`, and the same number is the
    rank over `F_2` of the cube of the companion matrix of the class."""
    var expected: List[Int] = [0, 3, 2, 3, 1, 3, 2, 3]
    for code in range(8):
        assert_equal(nonzero_roots_mod2(code), expected[code])
        var a = (code >> 2) & 1
        var b = (code >> 1) & 1
        var c = code & 1
        # companion matrix of t^3 + a t^2 + b t + c over F_2 (signs vanish)
        var companion = Mat3([0, 0, c, 1, 0, b, 0, 1, a])
        assert_equal(rank_mod2(companion * companion * companion), expected[code])
        # det, tr, e_2 of the companion matrix have the parities c, a, b
        assert_equal(chi_mod2_code(companion.det(), companion.trace(), principal_minor_sum(companion)), code)
        assert_equal(chi_mod2_code(-c, a + 2, b - 4), code)
    var outside = False
    try:
        _ = nonzero_roots_mod2(8)
    except e:
        outside = "outside 0..7" in String(e)
    assert_true(outside)


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
    # Cannot be nonzero: on an (F) specimen an absorbed orbit raises in
    # `OrbitMemo.transient` before it is counted. The raise is the guard.
    assert_equal(census.f_pairs_absorbed, 0)
    assert_equal(census.f_relative_states, 97992)
    assert_equal(census.transients.total(), 1956)
    assert_equal(census.transients.maximum(), 51)
    assert_equal(census.transients.count(51), 24)
    assert_equal(census.transients.count(38), 0)
    var transient_rows: List[List[Int]] = [
        [2, 36], [3, 252], [4, 300], [5, 342], [6, 54], [7, 174], [8, 126], [9, 12], [10, 48], [11, 96], [12, 6],
        [13, 24], [15, 66], [16, 102], [18, 30], [19, 24], [20, 24], [21, 54], [22, 18], [31, 72], [35, 72], [51, 24],
    ]
    var transient_total = 0
    for row in transient_rows:
        assert_equal(census.transients.count(row[0]), row[1])
        transient_total += row[1]
    assert_equal(transient_total, 1956)
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

    # The certified radii the census decided in: 348 incidence matrices, and
    # the sum of the three radii over the matrices and over the specimens.
    # These pins and those of `test_the_certified_radii` guard `stable_radii`.
    assert_equal(census.matrices, 348)
    assert_equal(census.matrix_radius_sum, 8562)
    assert_equal(len(census.radii), 4554)

    # (F) <=> no terminal leftmost cycle, specimen by specimen, with the count.
    var literal = 0
    var leftmost_total = 0
    var leftmost_longest = 0
    var cycle_free = 0
    var radius_sum = 0
    var halved_cycles = 0
    var halved_empty = 0
    # Round 2: the class tables recomputed specimen by specimen, key
    # 10 d_2 + dim H^1, from quantities the module does not use.
    var all_classes = Histogram(40)
    var open_classes = Histogram(40)
    var excluded_odd = 0
    var excluded_even = 0
    var open_excluded = 0
    for s in range(len(corpus)):
        var m = PrototileMap(corpus[s].sigma)
        var profile = fc3_profile_of(m)
        var incidence = corpus[s].incidence.copy()
        var d2 = rank_mod2(incidence * incidence * incidence)
        assert_equal(profile.d2(), d2)
        var chi = incidence.charpoly()
        assert_equal(profile.chi_mod2(), 4 * mod2(chi[2]) + 2 * mod2(chi[1]) + mod2(chi[0]))
        assert_equal(nonzero_roots_mod2(profile.chi_mod2()), d2)
        var dimension = h1_profile(corpus[s].sigma).dimension
        assert_equal(profile.h1_dimension, dimension)
        assert_equal(profile.rank_two_dimension_bound(), 3 + abs(d2 - 1))
        assert_equal(profile.dimension_clause(), dimension < 3 + abs(d2 - 1))
        assert_equal(profile.h1_three(), dimension == 3)
        var det_is_odd = mod2(incidence.det()) == 1
        assert_equal(d2 == 3, det_is_odd)
        var excluded = dimension == 3
        if det_is_odd:
            excluded = dimension <= 4 or mod2(incidence.trace()) != mod2(chi[1])
        assert_equal(profile.rank_two_excluded(), excluded)
        all_classes.record(10 * d2 + dimension)
        if excluded:
            if det_is_odd:
                excluded_odd += 1
            else:
                excluded_even += 1
        var two_sided = (
            periodic_letters(prefix_endpoint_map(corpus[s].sigma)) >= 2
            and periodic_letters(suffix_endpoint_map(corpus[s].sigma)) >= 2
        )
        if census.holds[s] and two_sided:
            open_classes.record(10 * d2 + dimension)
            if excluded:
                open_excluded += 1
        var radii = census.radii[s].copy()
        assert_equal(len(radii), 3)
        radius_sum += radii[0] + radii[1] + radii[2]
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
        # The search is a `BoxSearch`; it has no verdict to misreport.
        var halved: List[Int] = [max(1, radii[0] // 2), max(1, radii[1] // 2), max(1, radii[2] // 2)]
        var undersized = interior_cycles_in_box(m, halved)
        assert_true(len(undersized.cycles) <= census.cycle_counts[s])
        halved_cycles += len(undersized.cycles)
        if len(undersized.cycles) == 0:
            halved_empty += 1
        if s % STRIDE == 0:
            literal += 1
            assert_equal(len(terminal_leftmost_cycles(m.tables, build_box_graph(m.tables), 0)), census.leftmost_predicted[s])
            var doubled: List[Int] = [2 * radii[0], 2 * radii[1], 2 * radii[2]]
            assert_equal(len(interior_cycles_in_box(m, doubled).cycles), census.cycle_counts[s])
    assert_equal(radius_sum, 99078)
    assert_equal(leftmost_total, 10584)
    assert_equal(leftmost_longest, 39)
    assert_equal(cycle_free, 1794)
    assert_equal(literal, 47)
    # The halved box misses interior cycles: fewer cycles are found, and more
    # than 1,794 halved boxes hold none, so reading an empty halved box as (F)
    # would over-report. This calibrates that one box only. A bound that is
    # too small but still holds every interior cycle of the corpus passes
    # every cycle pin of this test; what guards `stable_radii` is the pinned
    # radii (the five fixtures, 8,562 and 99,078).
    assert_true(halved_cycles < census.interior_cycle_total)
    assert_true(halved_empty > 1794)

    # Round 2. The census tables equal the independent recomputation above.
    for key in range(40):
        assert_equal(census.classes.d2_dimension.count(key), all_classes.count(key))
        assert_equal(census.open_classes.d2_dimension.count(key), open_classes.count(key))
    assert_equal(census.classes.total(), 4554)
    assert_equal(census.open_classes.total(), 510)
    assert_equal(census.rank_two_excluded, excluded_odd + excluded_even)
    assert_equal(census.open_rank_two_excluded, open_excluded)
    check_round_two_classes(census, excluded_odd, excluded_even, open_excluded)
    return census^


def check_round_two_classes(
    census: GeometricFCensus, excluded_odd: Int, excluded_even: Int, open_excluded: Int
) raises:
    """The pins of round 2: class counts under Theorems H3, FC3+ and P+ of
    docs/c4-rank-two-wall-2026-11-16.md, not certificates of a coincidence
    rank."""
    var odd = CELL_DET_ODD
    var open_ends = CELL_F | CELL_LEFT_TRIVIAL | CELL_RIGHT_TRIVIAL
    var dimensions: List[Int] = [3, 4, 5, 7]

    # (d_2, dim H^1) over the corpus; d_2 = 3 exactly for odd determinant.
    var table: List[List[Int]] = [
        [0, 336, 36, 48, 12], [1, 456, 48, 144, 36], [2, 570, 72, 120, 48], [3, 1740, 396, 408, 84],
    ]
    var total = 0
    for row in table:
        for k in range(4):
            assert_equal(census.classes.d2_count(row[0], dimensions[k]), row[k + 1])
            total += row[k + 1]
        assert_equal(census.classes.d2_count(row[0], 6), 0)
    assert_equal(total, 4554)
    assert_equal(census.classes.d2_dimension.total(), 4554)
    for k in range(4):
        assert_equal(census.classes.parity_count(True, dimensions[k]), table[3][k + 1])
        assert_equal(
            census.classes.parity_count(False, dimensions[k]), table[0][k + 1] + table[1][k + 1] + table[2][k + 1]
        )
    # The same table by the class of chi_M mod 2 (code 4 tr + 2 e_2 + det).
    var fine: List[List[Int]] = [
        [0, 336, 36, 48, 12], [2, 342, 48, 96, 36], [6, 228, 24, 24, 12], [4, 456, 48, 144, 36],
        [1, 396, 96, 108, 12], [3, 372, 132, 96, 12], [5, 528, 96, 96, 12], [7, 444, 72, 108, 48],
    ]
    var fine_total = 0
    for row in fine:
        for k in range(4):
            assert_equal(census.classes.count(row[0], dimensions[k]), row[k + 1])
            fine_total += row[k + 1]
    assert_equal(fine_total, 4554)
    assert_equal(census.classes.chi_dimension.total(), 4554)
    # Round-1 pin, from the table: chi_M mod 2 irreducible (codes 3 and 5).
    assert_equal(372 + 132 + 96 + 12 + 528 + 96 + 96 + 12, 1344)

    # dim H^1 = 3, every determinant (Theorem H3).
    assert_equal(census.count_where(CELL_H1_THREE, CELL_H1_THREE), 3102)
    assert_equal(census.count_where(odd | CELL_H1_THREE, odd | CELL_H1_THREE), 1740)
    assert_equal(census.count_where(odd | CELL_H1_THREE, CELL_H1_THREE), 1362)
    assert_equal(336 + 456 + 570, 1362)
    # The 1,362 by (F): 1,128 fail (F); of the 234 with (F), 192 have an
    # endpoint map with fewer than two periodic letters (clause (a')) and 42
    # have two periodic letters on both sides (pinned below).
    assert_equal(census.count_where(odd | CELL_H1_THREE | CELL_F, CELL_H1_THREE), 1128)
    assert_equal(census.count_where(odd | CELL_H1_THREE | CELL_F, CELL_H1_THREE | CELL_F), 234)
    assert_equal(1128 + 192 + 42, 1362)
    # (F) and dim H^1 = 3, every determinant: the hypotheses of Theorem FC3+.
    assert_equal(census.count_where(CELL_H1_THREE | CELL_F, CELL_H1_THREE | CELL_F), 1350)
    assert_equal(census.count_where(odd | CELL_H1_THREE | CELL_F, odd | CELL_H1_THREE | CELL_F), 1116)
    assert_equal(1116 + 234, 1350)
    # The dimension bound of Theorem P+: dim H^1 < 3 + |d_2 - 1|.
    assert_equal(census.count_where(CELL_RANK_BOUND, CELL_RANK_BOUND), 3042)
    assert_equal(census.count_where(odd | CELL_RANK_BOUND, odd | CELL_RANK_BOUND), 2136)
    assert_equal(census.count_where(odd | CELL_RANK_BOUND, CELL_RANK_BOUND), 906)
    assert_equal(336 + 570, 906)
    # For odd determinant it is clause (b); for even determinant it is
    # contained in dim H^1 = 3, and silent on d_2 = 1.
    assert_equal(census.count_where(odd | CELL_RANK_BOUND | CELL_H1_AT_MOST_4, odd | CELL_RANK_BOUND), 0)
    assert_equal(census.count_where(odd | CELL_RANK_BOUND | CELL_H1_AT_MOST_4, odd | CELL_H1_AT_MOST_4), 0)
    assert_equal(census.count_where(odd | CELL_RANK_BOUND | CELL_H1_THREE, CELL_RANK_BOUND), 0)
    assert_equal(census.count_where(odd | CELL_RANK_BOUND | CELL_H1_THREE, CELL_H1_THREE), 456)
    # The hypotheses of "coincidence rank != 2" without the divisor
    # condition: odd, dim H^1 <= 4 or tr != e_2; even, dim H^1 = 3.
    assert_equal(excluded_odd, 2352)
    assert_equal(excluded_even, 1362)
    assert_equal(census.rank_two_excluded, 3714)
    assert_equal(4554 - 3714, 276 + 564)

    # The 510 (F) specimens with two periodic letters on both sides.
    var open_table: List[List[Int]] = [
        [0, 30, 0, 0, 0], [1, 0, 0, 48, 24], [2, 12, 0, 60, 0], [3, 24, 60, 204, 48],
    ]
    var open_total = 0
    for row in open_table:
        for k in range(4):
            assert_equal(census.open_classes.d2_count(row[0], dimensions[k]), row[k + 1])
            open_total += row[k + 1]
    assert_equal(open_total, 510)
    var open_fine: List[List[Int]] = [
        [0, 30, 0, 0, 0], [2, 0, 0, 48, 0], [6, 12, 0, 12, 0], [4, 0, 0, 48, 24],
        [1, 0, 24, 96, 0], [3, 0, 0, 48, 0], [5, 24, 24, 12, 12], [7, 0, 12, 48, 36],
    ]
    var open_fine_total = 0
    for row in open_fine:
        for k in range(4):
            assert_equal(census.open_classes.count(row[0], dimensions[k]), row[k + 1])
            open_fine_total += row[k + 1]
    assert_equal(open_fine_total, 510)
    # Even determinant (174, all with det 2): 42 with dim H^1 = 3, of which
    # 30 with chi_M = t^3 and 12 with chi_M = t (t^2 + t + 1) mod 2; 132
    # remain, 72 with d_2 = 1 and 60 with d_2 = 2 and dim H^1 = 5.
    assert_equal(census.count_where(open_ends | odd, CELL_F), 174)
    assert_equal(census.residual_determinant.count(2 + 8), 174)
    assert_equal(census.count_where(open_ends | odd | CELL_H1_THREE, CELL_F | CELL_H1_THREE), 42)
    assert_equal(234 - 42, 192)
    assert_equal(census.open_classes.count(0, 3), 30)
    assert_equal(census.open_classes.count(6, 3), 12)
    assert_equal(census.open_classes.count(2, 3) + census.open_classes.count(4, 3), 0)
    assert_equal(census.count_where(open_ends | odd | CELL_H1_THREE, CELL_F), 132)
    assert_equal(census.open_classes.d2_count(1, 5) + census.open_classes.d2_count(1, 7), 72)
    assert_equal(census.open_classes.d2_count(2, 5), 60)
    assert_equal(census.open_classes.d2_count(0, 4) + census.open_classes.d2_count(0, 5) + census.open_classes.d2_count(0, 7), 0)
    # On this class the dimension bound of P+ and dim H^1 = 3 select the
    # same even specimens (none has d_2 = 1 and dim H^1 = 3).
    assert_equal(census.count_where(open_ends | odd | CELL_RANK_BOUND, CELL_F | CELL_RANK_BOUND), 42)
    # With the 156 odd ones of round 1: 198 of the 510 meet the hypotheses,
    # 312 = 180 + 132 do not.
    assert_equal(open_excluded, 198)
    assert_equal(census.open_rank_two_excluded, 198)
    assert_equal(156 + 42, 198)
    assert_equal(510 - 198, 180 + 132)


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
    # Outside PIP3 the clauses mean nothing, and the profile is refused. The
    # reducible strict control 011/120/2012 has det -1 and dim H^1 = 3, so it
    # would satisfy clause (b); it has a strict system
    # (test_c4_reducible_pisot_controls).
    var reducible: List[List[Int]] = [[0, 1, 1], [1, 2, 0], [2, 0, 1, 2]]
    assert_equal(Mat3(substitution_incidence(reducible)).det(), -1)
    assert_equal(h1_profile(reducible).dimension, 3)
    var refused = False
    try:
        _ = fc3_profile(reducible)
    except e:
        refused = "primitive irreducible Pisot" in String(e)
    assert_true(refused)
    # Round 2. Tribonacci: chi_M = (t + 1)^3 mod 2, d_2 = 3, and dim H^1 = 3
    # is below the bound 5.
    assert_equal(t.chi_mod2(), 7)
    assert_equal(t.d2(), 3)
    assert_equal(t.rank_two_dimension_bound(), 5)
    assert_true(t.dimension_clause())
    assert_true(t.h1_three())
    assert_true(t.rank_two_excluded())
    # 01/12/021: chi_M = t^3 + t^2 + 1 mod 2, irreducible; dim H^1 = 4 < 5.
    assert_equal(c.chi_mod2(), 5)
    assert_equal(c.d2(), 3)
    assert_equal(c.rank_two_dimension_bound(), 5)
    assert_true(c.dimension_clause())
    assert_false(c.h1_three())
    assert_true(c.rank_two_excluded())


def check_profile(
    sigma: List[List[Int]],
    matrix: List[Int],
    determinant: Int,
    trace: Int,
    e2: Int,
    code: Int,
    d2: Int,
    dimension: Int,
    bound: Int,
    excluded: Bool,
) raises:
    assert_equal(substitution_incidence(sigma), matrix)
    var p = fc3_profile(sigma)
    assert_equal(p.determinant, determinant)
    assert_equal(p.trace, trace)
    assert_equal(p.e2, e2)
    assert_equal(p.chi_mod2(), code)
    assert_equal(p.d2(), d2)
    assert_equal(p.h1_dimension, dimension)
    assert_equal(p.rank_two_dimension_bound(), bound)
    assert_equal(p.dimension_clause(), dimension < bound)
    assert_equal(p.h1_three(), dimension == 3)
    assert_equal(p.rank_two_excluded(), excluded)


def test_round_two_profile_fixtures() raises:
    """One specimen per value of `d_2` of the even-determinant table, and one
    odd-determinant specimen reached by no clause, by hand. The incidence
    matrix is written out (rows; column `a` is the Parikh vector of
    `sigma(a)`), and `chi_M = t^3 - tr t^2 + e_2 t - det`."""
    # 01/121/012: rows (1,0,1), (1,2,1), (0,1,1); tr 4, e_2 = 2 + 1 + 1 = 4,
    # det = 1 + 1 = 2; chi = t^3 mod 2, d_2 = 0, bound 4; dim H^1 = 3.
    var zero: List[List[Int]] = [[0, 1], [1, 2, 1], [0, 1, 2]]
    check_profile(zero, [1, 0, 1, 1, 2, 1, 0, 1, 1], 2, 4, 4, 0, 0, 3, 4, True)
    var pz = fc3_profile(zero)
    assert_equal(pz.left_periodic, 2)
    assert_equal(pz.right_periodic, 2)
    assert_true(decide_geometric_f(zero).holds)
    # 01/220/100: rows (1,1,2), (1,0,1), (0,2,0); tr 1, e_2 = -1 + 0 - 2 = -3,
    # det = -2 + 4 = 2; chi = t (t^2 + t + 1) mod 2, d_2 = 2, bound 4;
    # dim H^1 = 3.
    var two_low: List[List[Int]] = [[0, 1], [2, 2, 0], [1, 0, 0]]
    check_profile(two_low, [1, 1, 2, 1, 0, 1, 0, 2, 0], 2, 1, -3, 6, 2, 3, 4, True)
    assert_false(fc3_profile(two_low).endpoint_trivial())
    assert_true(decide_geometric_f(two_low).holds)
    # 1/212/021: rows (0,0,1), (1,1,1), (0,2,1); tr 2, e_2 = 0 + 0 - 1 = -1,
    # det 2; chi = t (t + 1)^2 mod 2, d_2 = 2, bound 4; dim H^1 = 5 passes it.
    var two_high: List[List[Int]] = [[1], [2, 1, 2], [0, 2, 1]]
    check_profile(two_high, [0, 0, 1, 1, 1, 1, 0, 2, 1], 2, 2, -1, 2, 2, 5, 4, False)
    assert_false(fc3_profile(two_high).endpoint_trivial())
    assert_true(decide_geometric_f(two_high).holds)
    # 1/22/021 and 1/22/012 share the matrix with rows (0,0,1), (1,0,1),
    # (0,2,1); tr 1, e_2 = -2, det 2; chi = t^2 (t + 1) mod 2, d_2 = 1, bound 3:
    # Theorem P+ gives no dimension bound. 1/22/021 has dim H^1 = 5 and is
    # reached by no clause; 1/22/012 has dim H^1 = 3 and is reached by the
    # clause dim H^1 = 3 only (it fails (F): the period-5 interior cycle
    # pinned above).
    var one_high: List[List[Int]] = [[1], [2, 2], [0, 2, 1]]
    check_profile(one_high, [0, 0, 1, 1, 0, 1, 0, 2, 1], 2, 1, -2, 4, 1, 5, 3, False)
    assert_false(fc3_profile(one_high).endpoint_trivial())
    assert_true(decide_geometric_f(one_high).holds)
    var one_low: List[List[Int]] = [[1], [2, 2], [0, 1, 2]]
    check_profile(one_low, [0, 0, 1, 1, 0, 1, 0, 2, 1], 2, 1, -2, 4, 1, 3, 3, True)
    assert_false(fc3_profile(one_low).dimension_clause())
    assert_false(decide_geometric_f(one_low).holds)
    # Odd determinant, reached by no clause: 1/2/021 has the Tribonacci
    # polynomial (tr 1, e_2 -1, det 1; chi = (t + 1)^3 mod 2, tr = e_2) and
    # dim H^1 = 5, the bound.
    var odd_open: List[List[Int]] = [[1], [2], [0, 2, 1]]
    check_profile(odd_open, [0, 0, 1, 1, 0, 1, 0, 1, 1], 1, 1, -1, 7, 3, 5, 5, False)
    assert_false(fc3_profile(odd_open).arithmetic_clause())


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
    test_d2_is_the_number_of_nonzero_roots_mod_2()
    test_round_two_profile_fixtures()
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
        ", reached by none of (a'), (b), (c):", census.residual_determinant.total(),
        "; round 2 class counts, key 10 d_2 + dim H^1:", census.classes.d2_dimension.line("corpus"), ";",
        census.open_classes.d2_dimension.line("(F) with two periodic letters on both sides"),
        "; dim H^1 = 3:", census.count_where(CELL_H1_THREE, CELL_H1_THREE), ", of them even det:",
        census.count_where(odd | CELL_H1_THREE, CELL_H1_THREE),
        "; hypotheses of cr != 2 without the divisor condition:", census.rank_two_excluded, "of", census.total,
        "and", census.open_rank_two_excluded, "of", census.open_classes.total(),
        "; peak candidates / visited states / closure nodes:",
        census.peak_candidates, census.peak_visited, census.peak_nodes,
    )
    require_contract("Geometric property (F) of ternary irreducible Pisot substitutions (psc.c4_geometric_f), exact integer and Z[beta] arithmetic: the prototile state map f(j, v) = (j', M v - p(P)); (F) decided by walking every state with v != 0 inside the box of stable_radii (Lemma B: per incidence matrix, outward-rounded rational intervals; the radii are pinned on the five fixtures, [2,3,4], [4,3,3], [4,5,3], [26,15,16], [18,15,17], and by their sum, 8,562 over the 348 matrices and 99,078 over the specimens; a search in any other box returns no verdict), every interior f-cycle replaying (M^k - I) v = p(P) at an interior occurrence. Fixtures: Tribonacci 01/02/0 has (F); 01/12/021 has the f-fixed state (2, (-1, 0, 1)) with (M - I) v = e_0 = p(P) for P = 0 in sigma(2) = 0.2.1, re-derived from the word, and 4 terminal leftmost cycles; 1/12/022, 1/012/010 and 1/22/012 have one interior cycle of period 1, 3, 5 and recover the leftmost-chain pins (2 cycles of length 1, 6, 15); 1/2/02 has 11 relative states per pair, equal to the set read off 3,000-letter ray prefixes, transient 7, and M^9 sends the first 60 vertices of each ray to common vertices while M^6 does not; 1/012/100 pair (0, 1) has 240 relative states and transient 51 where a 3,000-letter prefix shows 60 states and transient 36. Refusals: the reducible 10/102/211 and 011/120/2012, the singular 1/012/1, the non-Pisot 1/2/001, an image of length 7, Thue-Morse, 012/120/201, non-primitive and malformed input raise, each matched on its refusal message; fc3_profile refuses 011/120/2012; state and overlap caps raise; a point outside its tile has no image; an orbit closing on an uncertified cycle raises. Corpus, 4,554 specimens on 348 incidence matrices: (F) on 1,794, invariant under image reversal on all 4,554; 3,756 interior cycles with 12,828 states, longest period 13, 0/1/2/3 cycles on 1794/1860/804/96 specimens; least interior period over the other 2,760: 1:816 2:252 3:744 4:228 5:492 6:12 7:24 8:72 10:84 11:12 13:24; terminal leftmost cycles (psc.leftmost_chain on the leftmost closure of the box start states) = 2 sum gcd(|C|, |G|) on every specimen, 10,584 in all, longest 39, none exactly on the 1,794 (F) specimens, replayed on the literal box graph for every 97th specimen (47); half the certified radii miss cycles (a calibration of that box only; the pinned radii guard the bound); Theorem FC1: 1,956 pairs of periodic first letters on (F) specimens, each of their 97,992 relative states reaches a vertex state, maximal transient 51 f-steps (24 pairs; the scratch value 38 was a 3,000-letter prefix scan), and 2,790 pairs on the other specimens, each with a relative state absorbed by an interior cycle; arithmetic classes: 2,628 odd determinants, of them 2,136 with dim H^1 <= 4, 1,344 with tr != e_2 (mod 2), 2,352 with either; of the 1,794 (F) specimens 1,284 have an endpoint map with fewer than two periodic letters, and of the other 510, 84 have odd det and dim H^1 <= 4, 120 odd det and tr != e_2, 156 either, 354 neither (174 with det 2, 180 odd). Round 2 (docs/c4-rank-two-wall-2026-11-16.md, Theorems H3, FC3+ and P+: class counts under recorded conditional theorems, not certificates of a coincidence rank): d_2 = 3 - ord_t(chi_M mod 2), the number of nonzero roots of chi_M over an algebraic closure of F_2, read from the parities of det M, e_2(M), tr M (the eight classes factored by hand) and equal to the rank over F_2 of (M mod 2)^3 on all 4,554 specimens; fixtures by hand: 01/121/012 (chi_M = t^3 mod 2, d_2 = 0, dim H^1 = 3), 01/220/100 (t(t^2 + t + 1), d_2 = 2, dim 3), 1/212/021 (t(t + 1)^2, d_2 = 2, dim 5), 1/22/021 and 1/22/012 (t^2 (t + 1), d_2 = 1, dim 5 and 3), 1/2/021 (odd, tr = e_2, dim 5); corpus counts by (d_2, dim H^1 = 3/4/5/7), d_2 = 3 exactly for odd determinant: d_2 = 0: 336/36/48/12; d_2 = 1: 456/48/144/36; d_2 = 2: 570/72/120/48; d_2 = 3: 1740/396/408/84, also pinned by the class of chi_M mod 2; dim H^1 = 3 (Theorem H3, every determinant) on 3,102 specimens, 1,362 of them with even determinant, of which 1,128 fail (F), 192 have (F) and an endpoint map with fewer than two periodic letters, and 42 have (F) and two periodic letters on both sides; (F) and dim H^1 = 3 (the hypotheses of Theorem FC3+) on 1,350 = 1,116 odd + 234 even; dim H^1 < 3 + |d_2 - 1| (the dimension bound of Theorem P+ fails) on 3,042 = 2,136 odd + 906 even, contained in dim H^1 = 3 for even determinant and silent on the 456 specimens with d_2 = 1 and dim H^1 = 3; the hypotheses of 'coincidence rank != 2' without the divisor condition (odd determinant: dim H^1 <= 4 or tr != e_2; even determinant: dim H^1 = 3) hold on 3,714 = 2,352 + 1,362 specimens; over the 510 (F) specimens with two periodic letters on both sides: d_2 = 0: 30 at dim H^1 = 3; d_2 = 1: 48 at dim 5 and 24 at dim 7; d_2 = 2: 12 at dim 3 and 60 at dim 5; d_2 = 3: 24/60/204/48; of the 174 with det 2, 42 have dim H^1 = 3 (30 with chi_M = t^3 and 12 with chi_M = t(t^2 + t + 1) mod 2) and 132 remain (72 with d_2 = 1, 60 with d_2 = 2 and dim H^1 = 5); with the 156 odd ones, 198 of the 510 meet the hypotheses and 312 = 180 + 132 do not; the (d_2, dim H^1) tables and the hypothesis counts are recomputed specimen by specimen in the test with d_2 from that rank; the divisor condition of Theorem P+ and the refinement of Remark (3) after Theorem P (Lemma S at the admissible n < 6) are not implemented. Class counts only: no coincidence rank, strong coincidence or pure discrete spectrum is certified, and no claim status changes")
