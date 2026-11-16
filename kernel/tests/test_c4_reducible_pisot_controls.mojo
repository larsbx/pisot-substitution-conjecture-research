"""Reducible strict controls with irrational Pisot inflation, and two nonunit
seam families read through the on-main local birth sieve.

Contract: `docs/c4-closure-attempt-2026-11-16.md` (negative controls, §7;
nonunit route, §5). Sieve and eliminator:
`docs/c4-bilateral-birth-rigidity-2026-11-02.md` §9. Legal-predecessor rule:
`docs/c4-legal-seams-2026-11-04.md`, `docs/c4-seam-birth-orbits-2026-11-04.md`.

**(A) Controls.** `C-D1 = 011/120/2012`, `C-D2 = 010/1222/2012` and
`1/012/101` are primitive with a rational eigenvalue `+1` or `-1`, so the
irreducibility arm of the PIP screen rejects them; the quadratic cofactor of
`chi_M` is irreducible and Pisot, so the inflation factor is an irrational
Pisot number. For each stated pair of fixed rays the seed is the first
irreducible balanced block of the two rays, and the search is the bounded
ordered child closure `psc.c4_cut_attractor.strict_closure`:

* it returns a finite closure, validated against every literal factor
  occurrence (`validate_strict_closure`): a strict system exists, and since
  every block of the ray pair is a block of an inflation of the seed, the
  two rays never carry the same letter at an index with equal prefix Parikh
  vectors;
* or it meets a coincident factor: the two rays coincide, and the bounded
  left-witness search gives the level, the letter index and the letter;
* or it exhausts its state cap, which is reported as capped and is neither.

**(B) Families.** For `3 <= c <= 63`, `F1_c = (0^(c-1) 1, 1 2 0^(c-1), 0^c)`
and `F3_c = (0^(c-1) 1 0, 0 2 1, 2 0)` are primitive with `det M = c`,
`chi_M = x^3 - c x^2 - c` resp. `x^3 - (c+2) x^2 + 2c x - c`, irreducible and
Pisot by the corpus screen and by the Routh screen. `F1_c` has an empty
on-main `L_sigma`. `F3_c` has exactly the two on-main types `(1, 2, 2, 0)` and
`(2, 0, 1, 2)` (top source letter, top digit, bottom source letter, bottom
digit), and both lose their only non-collapsing left pair once the left
letter at digit zero is taken from a legal predecessor: the bigram `12` is
illegal. `c = 63` is the last parameter inside the 64-letter image budget of
the on-main sieve; `c = 64` is refused, not decided.

**What the on-main functions express, and what is composed here.** On main:
the count `|L_sigma|` (`unresolved_local_birth_types`), the legal bigrams,
and the hub-based phase-zero seam lists (`phase_zero_birth_seams`), which
are empty for `F3_c` at every hub choice and track. The hub-free reading (the
types themselves, filtered by the legal-predecessor rule without choosing a
hub or a track) is `psc.c4_seam_families.legal_local_birth_types`, a
composition of those on-main predicates; that its emptiness excludes a
strict system rests on written proofs, not on this test.

**Controls against a vacuous pass.** At `c = 2` both families keep legal
types, and `F3_2` keeps hub-based birth seams. On every strict control here
and on `10/102/211` the legal filter keeps every literal birth type of the
actual strict system.

**The primitivity hypothesis.** The eliminator of §9 is stated for a
primitive expanding substitution with `det M != 0`. `1/0/22` is not
primitive, has `det M = -2` and an empty on-main `L_sigma`, and has the
strict system `{(01,10), (10,01)}`: without primitivity an empty sieve
excludes nothing. `legal_local_birth_types` refuses that input.

**Not pinned here.** No statement about C4, #138, #139, #84, G1 or PSC; no
census of reducible substitutions; the 8-state overlap closure of
`1/012/101` (a geometric overlap graph, not a balanced-pair system) is not
replayed. For `3 <= c <= 8` each family member is also excluded by Theorem
A(4) through left strong-coincidence witnesses, pinned below, so on that
range the sieve excludes nothing Theorem A(4) does not; what it adds is one
argument for every `c`, without a witness.

Replay:
`cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_reducible_pisot_controls.mojo`
"""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from finite_linear_algebra.mat3 import Mat3
from psc import pisot_screen
from psc.bpa import apply_substitution, coincidence_boundaries, prefix_endpoint_map, substitution_incidence, suffix_endpoint_map
from psc.c4_cut_alignment import classify_irreducible_birth, unresolved_local_birth_types
from psc.c4_cut_attractor import (
    StrictClosure,
    inflated_first_pair_mask,
    intertwines,
    left_witness,
    strict_closure,
    validate_strict_closure,
)
from psc.c4_legal_seams import legal_bigrams, phase_zero_birth_seams, phase_zero_legal_seams
from psc.c4_quotient_spectrum import parikh_span_basis, quotient_charpoly
from psc.c4_seam_families import (
    f1_family,
    f3_family,
    legal_left_pair_exists,
    legal_local_birth_types,
    local_birth_types,
)
from psc.closed_component_search import CLASS_PIP, CLASS_REDUCIBLE, coincidence_profile, specimen_class
from psc.pisot import CubicScreen, is_irreducible_cubic, is_pip, is_pisot_charpoly, is_primitive
from psc.words import Pair

# Outcome of one bounded strict-system search. A capped search is neither of
# the two verdicts.
comptime VERDICT_STRICT = 1
comptime VERDICT_COINCIDENT = 0
comptime VERDICT_CAPPED = -1

# Family range: 63 is the largest parameter whose images fit the 64-letter
# budget of `unresolved_local_birth_types`.
comptime C_MIN = 3
comptime C_MAX = 63
# Range on which the strong-coincidence witnesses of the members are pinned.
comptime SC_MAX = 8
comptime SC_WORD_BUDGET = 2000000


def _w(s: String) -> List[Int]:
    var out = List[Int]()
    for b in s.as_bytes():
        out.append(Int(b) - 48)
    return out^


def _pair(u: String, v: String) -> Pair:
    return Pair(_w(u), _w(v))


def _sorted(l: List[Int]) -> List[Int]:
    var out = l.copy()
    for i in range(1, len(out)):
        var x = out[i]
        var j = i
        while j > 0 and out[j - 1] > x:
            out[j] = out[j - 1]
            j -= 1
        out[j] = x
    return out^


def _eval(coeffs: List[Int], x: Int) -> Int:
    """Integer Horner; coefficients low degree first."""
    var acc = 0
    for i in range(len(coeffs) - 1, -1, -1):
        acc = acc * x + coeffs[i]
    return acc


def _times_linear(quadratic: List[Int], root: Int) -> List[Int]:
    """`(x - root)(x^2 + q1 x + q0)`, low degree first."""
    var q0 = quadratic[0]
    var q1 = quadratic[1]
    return [-root * q0, q0 - root * q1, q1 - root, 1]


def _ray_root(tau: List[List[Int]], a: Int, b: Int, word_budget: Int = 4096) raises -> Pair:
    """The first irreducible balanced block of the `tau`-fixed rays
    `(X_a, X_b)`: the shortest nonempty common prefix length with equal Parikh
    vectors. `tau^n(a)` and `tau^n(b)` are prefixes of the rays because
    `tau(a)` starts with `a` and `tau(b)` with `b`. An exhausted word budget
    raises: it is not a statement about the rays."""
    if tau[a][0] != a or tau[b][0] != b:
        raise Error("ray root: the two letters are not fixed by the first-letter map")
    var top: List[Int] = [a]
    var bottom: List[Int] = [b]
    while len(top) <= word_budget and len(bottom) <= word_budget:
        var before = min(len(top), len(bottom))
        top = apply_substitution(tau, top)
        bottom = apply_substitution(tau, bottom)
        var n = min(len(top), len(bottom))
        if n == before:
            raise Error("ray root: the prefixes do not grow")
        var d: List[Int] = [0, 0, 0]
        for k in range(n):
            d[top[k]] += 1
            d[bottom[k]] -= 1
            if d[0] == 0 and d[1] == 0 and d[2] == 0:
                var u = List[Int]()
                var v = List[Int]()
                for t in range(k + 1):
                    u.append(top[t])
                    v.append(bottom[t])
                return Pair(u^, v^)
    raise Error("ray root: word budget exhausted before a common cut")


def _search(tau: List[List[Int]], seed: Pair, cap: Int) raises -> Int:
    """The bounded ordered child closure of `seed`, reported three ways. Any
    refusal other than a coincident factor or the state cap is re-raised."""
    try:
        var c = strict_closure(tau, seed, cap)
        validate_strict_closure(tau, c)
        return VERDICT_STRICT
    except e:
        var message = String(e)
        if "coincident factor reached" in message:
            return VERDICT_COINCIDENT
        if "exceeded the state cap" in message:
            return VERDICT_CAPPED
        raise Error("unexpected refusal of the strict-system search: " + message)


def _ordered_first_pairs(c: StrictClosure) -> List[Int]:
    """Sorted distinct codes `3 u_0 + v_0` over the ordered states."""
    var out = List[Int]()
    for i in range(c.size()):
        var code = 3 * c.states[i].u[0] + c.states[i].v[0]
        if code not in out:
            out.append(code)
    return _sorted(out)


def _ordered_last_pairs(c: StrictClosure) -> List[Int]:
    """Sorted distinct codes `3 u_last + v_last` over the ordered states."""
    var out = List[Int]()
    for i in range(c.size()):
        var n = c.states[i].length()
        var code = 3 * c.states[i].u[n - 1] + c.states[i].v[n - 1]
        if code not in out:
            out.append(code)
    return _sorted(out)


def _longest(c: StrictClosure) -> Int:
    var out = 0
    for i in range(c.size()):
        out = max(out, c.states[i].length())
    return out


def _contained(a: StrictClosure, b: StrictClosure, swapped: Bool) -> Int:
    """How many states of `a` (or their swaps) are states of `b`."""
    var n = 0
    for i in range(a.size()):
        var p = Pair(a.states[i].v, a.states[i].u) if swapped else a.states[i].copy()
        if b.index_of(p) >= 0:
            n += 1
    return n


def _has_type(types: List[Int], a: Int, r: Int, b: Int, s: Int) -> Bool:
    for t in range(len(types) // 4):
        if types[4 * t] == a and types[4 * t + 1] == r and types[4 * t + 2] == b and types[4 * t + 3] == s:
            return True
    return False


def _actual_birth_types(tau: List[List[Int]], c: StrictClosure) raises -> List[Int]:
    """`[interior cuts, distinct types, types missing from the legal list]`
    over every interior cut of every state of a strict closure, each cut
    classified by the on-main occurrence-level `classify_irreducible_birth`."""
    var legal = legal_local_birth_types(tau)
    var seen = List[Int]()
    var cuts = 0
    var missing = 0
    for f in range(c.size()):
        for j in range(len(c.cuts[f])):
            var pos = c.cuts[f][j]
            if pos == 0:
                continue
            cuts += 1
            var birth = classify_irreducible_birth(tau, c.states[f], pos)
            var a = c.states[f].u[birth.top_source]
            var b = c.states[f].v[birth.bottom_source]
            if not _has_type(seen, a, birth.top_digit, b, birth.bottom_digit):
                seen += [a, birth.top_digit, b, birth.bottom_digit]
                if not _has_type(legal, a, birth.top_digit, b, birth.bottom_digit):
                    missing += 1
    return [cuts, len(seen) // 4, missing]


def _assert_outside_pip3(
    sigma: List[List[Int]], incidence: List[Int], det: Int, chi: List[Int], root: Int, cofactor: List[Int]
) raises:
    """Primitive, with the stated incidence, determinant and cubic; `root` is
    a rational root on the unit circle, `chi = (x - root) * cofactor`; the
    irreducibility arm of every PIP screen rejects it; the cofactor is an
    irreducible Pisot quadratic.

    Which arm rejects is pinned too. `psc.pisot.is_pisot_charpoly` asks for
    exactly one root outside the *closed* unit disc, and it counts the other
    real roots on `(-1, 1]`: a cubic with the root `+1` passes it, one with
    the root `-1` does not. So `is_pip` rejects a control with the root `+1`
    through irreducibility alone."""
    var m = Mat3(substitution_incidence(sigma))
    assert_equal(m.e, incidence)
    assert_equal(m.det(), det)
    assert_equal(m.charpoly(), chi)
    assert_true(is_primitive(m))
    assert_true(root == 1 or root == -1)
    assert_equal(_eval(chi, root), 0)
    assert_equal(_times_linear(cofactor, root), chi)
    assert_false(is_irreducible_cubic(chi))
    assert_equal(is_pisot_charpoly(chi), root == 1)
    assert_false(is_pip(m))
    var screen = CubicScreen()
    assert_false(screen.is_pip(m))
    assert_equal(specimen_class(screen, m), CLASS_REDUCIBLE)
    assert_equal(pisot_screen.irreducibility(chi), pisot_screen.REDUCIBLE)
    assert_equal(pisot_screen.screen(chi), pisot_screen.SCREEN_NOT_PISOT)  # a root on the unit circle
    assert_equal(pisot_screen.irreducibility(cofactor), pisot_screen.IRREDUCIBLE)
    assert_equal(pisot_screen.screen(cofactor), pisot_screen.SCREEN_PISOT)


def cd1() -> List[List[Int]]:
    return [[0, 1, 1], [1, 2, 0], [2, 0, 1, 2]]


def cd2() -> List[List[Int]]:
    return [[0, 1, 0], [1, 2, 2, 2], [2, 0, 1, 2]]


def phase_one() -> List[List[Int]]:
    return [[1], [0, 1, 2], [1, 0, 1]]


def test_controls_lie_outside_pip3() raises:
    # C-D1: chi = x^3 - 4x^2 + 2x + 1 = (x - 1)(x^2 - 3x - 1)
    _assert_outside_pip3(cd1(), [1, 1, 1, 2, 1, 1, 0, 1, 2], -1, [1, 2, -4, 1], 1, [-1, -3, 1])
    # C-D2: chi = x^3 - 5x^2 + 5x - 1 = (x - 1)(x^2 - 4x + 1)
    _assert_outside_pip3(cd2(), [2, 0, 1, 1, 1, 1, 0, 3, 2], 1, [-1, 5, -5, 1], 1, [1, -4, 1])
    # 1/012/101: chi = x^3 - x^2 - 3x - 1 = (x + 1)(x^2 - 2x - 1)
    _assert_outside_pip3(phase_one(), [0, 1, 1, 1, 1, 2, 0, 1, 0], 1, [-1, -3, -1, 1], -1, [-1, -2, 1])
    # First-letter maps: the identity (class D) twice, then the map 0 <-> 1, 2 -> 1.
    assert_equal(prefix_endpoint_map(cd1()), [0, 1, 2])
    assert_equal(prefix_endpoint_map(cd2()), [0, 1, 2])
    assert_equal(prefix_endpoint_map(phase_one()), [1, 0, 1])


def test_cd1_one_closed_system_and_a_coincident_pair() raises:
    var sigma = cd1()
    var root01 = _ray_root(sigma, 0, 1)
    var root02 = _ray_root(sigma, 0, 2)
    assert_equal(root01, _pair("0111201201202", "1202012011201"))
    assert_equal(root02, _pair("01112012", "20120111"))
    assert_equal(_search(sigma, root01, 64), VERDICT_STRICT)
    assert_equal(_search(sigma, root02, 64), VERDICT_STRICT)
    var c = strict_closure(sigma, root01, 64)
    var d = strict_closure(sigma, root02, 64)
    assert_equal(c.size(), 18)
    assert_equal(d.size(), 18)
    # one closed system: the two roots generate the same 18 ordered states
    assert_equal(_contained(c, d, False), 18)
    assert_equal(_contained(d, c, False), 18)
    assert_equal(_contained(c, c, True), 0)  # no state is the swap of a state
    assert_true(intertwines(sigma, c))
    assert_equal(_longest(c), 13)
    assert_equal(_ordered_first_pairs(c), [1, 2])  # (0,1), (0,2): the hub 0 always on top
    assert_equal(_ordered_last_pairs(c), [6, 7])   # (2,0), (2,1)
    assert_equal(inflated_first_pair_mask(sigma, c, 2), 0b011)  # cut pairs {0,1}, {0,2} only
    # Parikh span of rank two; M acts on Q^3 / V by the rational root +1
    assert_equal(len(parikh_span_basis(c)), 2)
    assert_equal(quotient_charpoly(sigma, c), [1, -1])
    # The bounded left-witness search finds nothing on the strict pairs. That
    # is an exhausted budget; the verdict is the closed system above.
    assert_equal(left_witness(sigma, 0, 1, 8), [-1, -1, -1])
    assert_equal(left_witness(sigma, 0, 2, 8), [-1, -1, -1])
    # The complementary pair (X_1, X_2) coincides: level 2, letter index 3
    # (three letters precede the common letter), letter 2.
    var root12 = _ray_root(sigma, 1, 2)
    assert_equal(root12, _pair("120", "201"))
    assert_equal(_search(sigma, root12, 64), VERDICT_COINCIDENT)
    assert_equal(left_witness(sigma, 1, 2, 8), [2, 3, 2])
    assert_equal(left_witness(sigma, 1, 2, 1), [-1, -1, -1])  # level 1 is too short to see it
    # A state cap below the system is reported as capped, never as a verdict.
    assert_equal(_search(sigma, root01, 17), VERDICT_CAPPED)
    assert_equal(_search(sigma, root01, 18), VERDICT_STRICT)


def test_cd2_two_systems_and_a_coincident_pair() raises:
    var sigma = cd2()
    var root01 = _ray_root(sigma, 0, 1)
    var root12 = _ray_root(sigma, 1, 2)
    assert_equal(root01, _pair("01012220101222201220122", "12222012201220122012010"))
    assert_equal(root12, _pair("12222012201220122012010122220122012010", "20120101222201201012220101222201220122"))
    assert_equal(_search(sigma, root01, 64), VERDICT_STRICT)
    assert_equal(_search(sigma, root12, 64), VERDICT_STRICT)
    var c = strict_closure(sigma, root01, 64)
    var d = strict_closure(sigma, root12, 64)
    assert_equal(c.size(), 21)
    assert_equal(d.size(), 23)
    assert_true(intertwines(sigma, c))
    assert_true(intertwines(sigma, d))
    assert_equal(_longest(c), 56)
    assert_equal(_longest(d), 56)
    assert_equal(_ordered_first_pairs(c), [1])     # (0,1)
    assert_equal(_ordered_last_pairs(c), [6])      # (2,0)
    assert_equal(_ordered_first_pairs(d), [3, 5])  # (1,0), (1,2)
    assert_equal(_ordered_last_pairs(d), [2])      # (0,2)
    # The (X_1, X_2) system holds the swap of every (X_0, X_1) state, its own
    # root, which is its only state headed (1,2), and one further state.
    assert_equal(_contained(c, d, True), 21)
    assert_equal(_contained(c, d, False), 0)
    var headed12 = 0
    for i in range(d.size()):
        if d.states[i].u[0] == 1 and d.states[i].v[0] == 2:
            headed12 += 1
            assert_equal(d.states[i], root12)
    assert_equal(headed12, 1)
    assert_equal(inflated_first_pair_mask(sigma, c, 2), 0b001)  # cut pair {0,1} only
    assert_equal(inflated_first_pair_mask(sigma, d, 2), 0b101)  # cut pairs {0,1}, {1,2}
    assert_equal(len(parikh_span_basis(c)), 2)
    assert_equal(quotient_charpoly(sigma, c), [1, -1])
    assert_equal(len(parikh_span_basis(d)), 2)
    assert_equal(quotient_charpoly(sigma, d), [1, -1])
    assert_equal(left_witness(sigma, 0, 1, 8), [-1, -1, -1])
    assert_equal(left_witness(sigma, 1, 2, 8), [-1, -1, -1])
    # The complementary pair (X_0, X_2) coincides: level 3, letter index 14,
    # letter 2, after the three noncoincident blocks cut at 6, 9 and 14.
    var root02 = _ray_root(sigma, 0, 2)
    assert_equal(root02, _pair("010122", "201201"))
    assert_equal(_search(sigma, root02, 64), VERDICT_COINCIDENT)
    assert_equal(left_witness(sigma, 0, 2, 8), [3, 14, 2])
    assert_equal(left_witness(sigma, 0, 2, 2), [-1, -1, -1])
    var top: List[Int] = [0]
    var bottom: List[Int] = [2]
    for _ in range(3):
        top = apply_substitution(sigma, top)
        bottom = apply_substitution(sigma, bottom)
    var u = List[Int]()
    var v = List[Int]()
    for k in range(14):
        u.append(top[k])
        v.append(bottom[k])
    assert_equal(coincidence_boundaries(u, v), [0, 6, 9, 14])
    assert_equal(top[14], 2)
    assert_equal(bottom[14], 2)
    assert_equal(_search(sigma, root01, 20), VERDICT_CAPPED)
    assert_equal(_search(sigma, root12, 22), VERDICT_CAPPED)
    # A word budget that runs out before the level budget raises: no verdict.
    var refused = False
    try:
        _ = left_witness(sigma, 0, 1, 32, 2000)
    except e:
        refused = "word budget exhausted before the level budget" in String(e)
    assert_true(refused)


def test_phase_one_control() raises:
    var sigma = phase_one()
    # The first-letter map exchanges 0 and 1, so the fixed rays belong to sigma^2.
    var tau = List[List[Int]]()
    for a in range(3):
        tau.append(apply_substitution(sigma, sigma[a]))
    assert_equal(tau[0], [0, 1, 2])
    assert_equal(tau[1], [1, 0, 1, 2, 1, 0, 1])
    assert_equal(tau[2], [0, 1, 2, 1, 0, 1, 2])
    assert_equal(prefix_endpoint_map(tau), [0, 1, 0])  # 0 and 1 are the only fixed letters
    var root = _ray_root(tau, 0, 1)
    assert_equal(root, _pair("01", "10"))
    assert_equal(_search(tau, root, 16), VERDICT_STRICT)
    var c = strict_closure(tau, root, 16)
    assert_equal(c.size(), 3)
    assert_equal(c.states[0], _pair("01", "10"))
    assert_equal(c.states[1], _pair("21", "12"))
    assert_equal(c.states[2], _pair("2101", "1012"))
    assert_true(intertwines(tau, c))
    assert_equal(_longest(c), 4)
    assert_equal(_ordered_first_pairs(c), [1, 7])  # (0,1), (2,1)
    assert_equal(_ordered_last_pairs(c), [3, 5])   # (1,0), (1,2)
    assert_equal(_contained(c, c, True), 0)
    assert_equal(len(parikh_span_basis(c)), 2)
    assert_equal(quotient_charpoly(tau, c), [1, -1])   # (-1)^2 on Q^3 / V
    assert_equal(left_witness(tau, 0, 1, 6), [-1, -1, -1])
    # Under sigma itself the same seed generates the three states and their
    # swaps: sigma exchanges the two rays, so it exchanges the two tracks.
    assert_equal(_search(sigma, root, 16), VERDICT_STRICT)
    var lift = strict_closure(sigma, root, 16)
    assert_equal(lift.size(), 6)
    assert_equal(_contained(c, lift, False), 3)
    assert_equal(_contained(c, lift, True), 3)
    assert_equal(_ordered_first_pairs(lift), [1, 3, 5, 7])
    assert_equal(len(parikh_span_basis(lift)), 2)
    assert_equal(quotient_charpoly(sigma, lift), [1, 1])  # the rational root -1
    # The remaining letter pair {0,2} has a level-one left witness.
    assert_equal(left_witness(sigma, 0, 2, 6), [1, 0, 1])
    assert_equal(_search(tau, root, 2), VERDICT_CAPPED)
    assert_equal(_search(sigma, root, 5), VERDICT_CAPPED)


def _assert_pip3(sigma: List[List[Int]], incidence: List[Int], det: Int, chi: List[Int]) raises:
    var m = Mat3(substitution_incidence(sigma))
    assert_equal(m.e, incidence)
    assert_equal(m.det(), det)
    assert_equal(m.charpoly(), chi)
    assert_true(is_primitive(m))
    assert_true(is_irreducible_cubic(chi))
    assert_true(is_pisot_charpoly(chi))
    assert_true(is_pip(m))
    var screen = CubicScreen()
    assert_true(screen.is_pip(m))
    assert_equal(specimen_class(screen, m), CLASS_PIP)
    # the degree-n Routh screen agrees and never refuses on this range
    assert_equal(pisot_screen.irreducibility(chi), pisot_screen.IRREDUCIBLE)
    assert_equal(pisot_screen.screen(chi), pisot_screen.SCREEN_PISOT)


def test_family_shapes() raises:
    assert_equal(f1_family(3), [[0, 0, 1], [1, 2, 0, 0], [0, 0, 0]])
    assert_equal(f3_family(3), [[0, 0, 1, 0], [0, 2, 1], [2, 0]])
    assert_equal(f1_family(2), [[0, 1], [1, 2, 0], [0, 0]])
    assert_equal(f3_family(2), [[0, 1, 0], [0, 2, 1], [2, 0]])
    for c in range(2, C_MAX + 2):
        var f1 = f1_family(c)
        var f3 = f3_family(c)
        assert_equal(len(f1[0]), c)
        assert_equal(len(f1[1]), c + 1)
        assert_equal(len(f1[2]), c)
        assert_equal(len(f3[0]), c + 1)
        assert_equal(len(f3[1]), 3)
        assert_equal(len(f3[2]), 2)
    for bad in [1, 0, -3]:
        var refused = 0
        try:
            _ = f1_family(bad)
        except:
            refused += 1
        try:
            _ = f3_family(bad)
        except:
            refused += 1
        assert_equal(refused, 2)


def test_families_have_no_legal_birth_type() raises:
    var members = 0
    for c in range(C_MIN, C_MAX + 1):
        var f1 = f1_family(c)
        var f3 = f3_family(c)
        _assert_pip3(f1, [c - 1, c - 1, c, 1, 1, 0, 0, 1, 0], c, [-c, 0, -c, 1])
        _assert_pip3(f3, [c, 1, 1, 1, 1, 0, 0, 1, 1], c, [-c, 2 * c, -(c + 2), 1])
        # F1_c: the on-main sieve is empty as it stands.
        assert_equal(unresolved_local_birth_types(f1), 0)
        assert_equal(len(local_birth_types(f1)), 0)
        assert_equal(len(legal_local_birth_types(f1)), 0)
        # F3_c: exactly two on-main types, mirror images of one another.
        assert_equal(unresolved_local_birth_types(f3), 2)
        assert_equal(local_birth_types(f3), [1, 2, 2, 0, 2, 0, 1, 2])
        # Top: sigma(1) = 0 2 | 1, left letter 2. Bottom: | 2 0 at digit zero,
        # so its left letter is the last letter of the image of a predecessor
        # of 2. The on-main sieve allows all three predecessors; the last
        # letters are (0, 1, 0), and (2, 1) never collapses. Only 02 is a
        # legal bigram ending in 2, so the legal left pair is (2, 0), which
        # collapses under the last-letter map.
        assert_equal(prefix_endpoint_map(f3), [0, 0, 2])
        assert_equal(suffix_endpoint_map(f3), [0, 1, 0])
        var legal = legal_bigrams(f3)
        assert_equal(legal, [True, True, True, True, False, False, True, True, False])  # 00 01 02 10 20 21
        assert_false(legal[3 * 1 + 2])
        var last = suffix_endpoint_map(f3)
        assert_false(legal_left_pair_exists(f3, legal, last, 1, 2, 2, 0))
        assert_false(legal_left_pair_exists(f3, legal, last, 2, 0, 1, 2))
        assert_equal(len(legal_local_birth_types(f3)), 0)
        # What the on-main hub-based lists say: with the forced hubs (left 2,
        # right 1) one legal seam survives on the bottom track and none on
        # the top; no hub choice on either track has a birth seam.
        assert_equal(len(phase_zero_legal_seams(f3, 2, 1, True)), 0)
        assert_equal(phase_zero_legal_seams(f3, 2, 1, False), [15])
        for left_hub in range(3):
            for right_hub in range(3):
                assert_equal(len(phase_zero_birth_seams(f3, left_hub, right_hub, True)), 0)
                assert_equal(len(phase_zero_birth_seams(f3, left_hub, right_hub, False)), 0)
        members += 1
    assert_equal(members, 61)


def test_the_filter_is_not_vacuous() raises:
    # c = 2 is below the family range: both members are PIP with det 2 and
    # keep legal birth types, so the criterion does not exclude them.
    var f1 = f1_family(2)
    var f3 = f3_family(2)
    _assert_pip3(f1, [1, 1, 2, 1, 1, 0, 0, 1, 0], 2, [-2, 0, -2, 1])
    _assert_pip3(f3, [2, 1, 1, 1, 1, 0, 0, 1, 1], 2, [-2, 4, -4, 1])
    assert_equal(unresolved_local_birth_types(f1), 4)
    assert_equal(local_birth_types(f1), [0, 1, 1, 1, 0, 1, 1, 2, 1, 1, 0, 1, 1, 2, 0, 1])
    assert_equal(legal_local_birth_types(f1), [0, 1, 1, 1, 0, 1, 1, 2, 1, 1, 0, 1, 1, 2, 0, 1])
    assert_equal(unresolved_local_birth_types(f3), 4)
    assert_equal(local_birth_types(f3), [0, 2, 1, 1, 1, 1, 0, 2, 1, 2, 2, 0, 2, 0, 1, 2])
    assert_equal(legal_local_birth_types(f3), [0, 2, 1, 1, 1, 1, 0, 2])
    # the hub-based lists keep birth seams at c = 2, at four hub/track choices
    assert_equal(phase_zero_birth_seams(f3, 2, 1, False), [15])
    var nonempty = 0
    for left_hub in range(3):
        for right_hub in range(3):
            for track in range(2):
                if len(phase_zero_birth_seams(f3, left_hub, right_hub, track == 1)) > 0:
                    nonempty += 1
    assert_equal(nonempty, 4)
    # c = 64 exceeds the image budget of the on-main sieve: refused, not decided.
    var refused = 0
    try:
        _ = unresolved_local_birth_types(f1_family(C_MAX + 1))
    except e:
        if "image outside checked local-filter arithmetic budget" in String(e):
            refused += 1
    try:
        _ = legal_local_birth_types(f3_family(C_MAX + 1))
    except e:
        if "image outside checked local-filter arithmetic budget" in String(e):
            refused += 1
    assert_equal(refused, 2)
    # singular incidence is refused by the list as by the count (1/012/1)
    var singular: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var caught = False
    try:
        _ = legal_local_birth_types(singular)
    except:
        caught = True
    assert_true(caught)


def test_the_eliminator_needs_primitivity() raises:
    """`0 -> 1, 1 -> 0, 2 -> 22`: not primitive, `det M = -2`, the on-main
    sieve is empty, and `(01, 10) -> (10, 01) -> (01, 10)` is a strict system.
    So an empty `L_sigma` with `det M != 0` is not an exclusion without
    primitivity, and the legal list refuses instead of returning empty."""
    var swap: List[List[Int]] = [[1], [0], [2, 2]]
    var m = Mat3(substitution_incidence(swap))
    assert_equal(m.e, [0, 1, 0, 1, 0, 0, 0, 0, 2])
    assert_equal(m.det(), -2)
    assert_false(is_primitive(m))
    assert_equal(unresolved_local_birth_types(swap), 0)
    assert_equal(len(local_birth_types(swap)), 0)
    var system = strict_closure(swap, _pair("01", "10"), 16)
    validate_strict_closure(swap, system)
    assert_equal(system.size(), 2)
    assert_equal(system.states[0], _pair("01", "10"))
    assert_equal(system.states[1], _pair("10", "01"))
    var refused = False
    try:
        _ = legal_local_birth_types(swap)
    except e:
        refused = "not primitive" in String(e)
    assert_true(refused)


def test_legal_filter_keeps_every_birth_of_the_strict_controls() raises:
    # [interior cuts, distinct literal types, types missing from the legal list]
    # 10/102/211, the on-main reducible strict control: |L| = 8 on main.
    var old: List[List[Int]] = [[1, 0], [1, 0, 2], [2, 1, 1]]
    var c_old = strict_closure(old, _ray_root(old, 1, 2), 16)
    assert_equal(c_old.size(), 4)
    assert_equal(unresolved_local_birth_types(old), 8)
    assert_equal(len(legal_local_birth_types(old)), 4 * 8)
    assert_equal(_actual_birth_types(old, c_old), [12, 3, 0])
    # C-D1
    var c1 = strict_closure(cd1(), _ray_root(cd1(), 0, 1), 64)
    assert_equal(unresolved_local_birth_types(cd1()), 56)
    assert_equal(len(legal_local_birth_types(cd1())), 4 * 56)
    assert_equal(_actual_birth_types(cd1(), c1), [69, 6, 0])
    # C-D2: the legal rule removes 12 of the 56 types and none that occurs
    var c2 = strict_closure(cd2(), _ray_root(cd2(), 0, 1), 64)
    var d2 = strict_closure(cd2(), _ray_root(cd2(), 1, 2), 64)
    assert_equal(unresolved_local_birth_types(cd2()), 56)
    assert_equal(len(legal_local_birth_types(cd2())), 4 * 44)
    assert_equal(_actual_birth_types(cd2(), c2), [83, 1, 0])
    assert_equal(_actual_birth_types(cd2(), d2), [94, 1, 0])
    assert_true(_has_type(legal_local_birth_types(cd2()), 2, 1, 1, 0))  # the one type of (X_0, X_1)
    assert_true(_has_type(legal_local_birth_types(cd2()), 1, 0, 2, 1))  # its mirror, in (X_1, X_2)
    # 1/012/101 under sigma, the six-state ordered lift
    var c3 = strict_closure(phase_one(), _pair("01", "10"), 16)
    assert_equal(unresolved_local_birth_types(phase_one()), 20)
    assert_equal(len(legal_local_birth_types(phase_one())), 4 * 20)
    assert_equal(_actual_birth_types(phase_one(), c3), [8, 6, 0])


def test_family_members_are_also_strongly_coincident() raises:
    # Scope: on this range Theorem A(4) already excludes each member, with all
    # three letter pairs left-witnessed, in pair order {0,1}, {0,2}, {1,2}.
    for c in range(C_MIN, SC_MAX + 1):
        var p1 = coincidence_profile(f1_family(c), SC_WORD_BUDGET)
        var p3 = coincidence_profile(f3_family(c), SC_WORD_BUDGET)
        assert_equal(p1.left, [4, 1, 5])
        assert_equal(p3.left, [1, 4, 2])
        assert_true(p1.excludes_strict_systems())
        assert_true(p3.excludes_strict_systems())


def main() raises:
    test_controls_lie_outside_pip3()
    test_cd1_one_closed_system_and_a_coincident_pair()
    test_cd2_two_systems_and_a_coincident_pair()
    test_phase_one_control()
    test_family_shapes()
    test_families_have_no_legal_birth_type()
    test_the_filter_is_not_vacuous()
    test_the_eliminator_needs_primitivity()
    test_legal_filter_keeps_every_birth_of_the_strict_controls()
    test_family_members_are_also_strongly_coincident()
    print("C4 reducible Pisot controls: C-D1 one 18-state system (longest 13), (X_1,X_2) coincident at [2,3,2]; C-D2 21 and 23 states (longest 56), (X_0,X_2) coincident at [3,14,2]; 1/012/101 3 states under sigma^2, 6 under sigma; all three reducible with a root +1 or -1; F1_c and F3_c for 3 <= c <= 63: PIP with det c, |L| = 0 resp. 2, no legal birth type; c = 2 and the strict controls keep legal types.")
    require_contract("reducible strict controls with irrational Pisot inflation, by the bounded ordered child closure seeded at the first balanced block of each fixed-ray pair and validated against every literal factor occurrence: C-D1 011/120/2012 (det -1, chi (x-1)(x^2-3x-1)) has one closed 18-state system for (X_0,X_1) and (X_0,X_2), ordered first pairs (0,1),(0,2), longest state 13, and (X_1,X_2) coincides at level 2, letter index 3; C-D2 010/1222/2012 (det 1, chi (x-1)(x^2-4x+1)) has 21 states for (X_0,X_1) with first pair (0,1) and 23 for (X_1,X_2) with first pairs (1,0),(1,2), longest state 56, and (X_0,X_2) coincides at level 3, letter index 14; 1/012/101 (det 1, chi (x+1)(x^2-2x-1)) has 3 states under sigma^2 from (X_0,X_1), first pairs (0,1),(2,1), longest state 4, and 6 under sigma; each is primitive and rejected by the PIP screen through its rational root, with an irreducible Pisot quadratic cofactor; an exhausted state cap is reported as capped, an exhausted level budget as no witness within the budget ([-1,-1,-1]), and an exhausted word budget raises; none is a verdict; F1_c = (0^(c-1)1, 120^(c-1), 0^c) and F3_c = (0^(c-1)10, 021, 20) for 3 <= c <= 63 are primitive with det c and chi x^3-cx^2-c resp. x^3-(c+2)x^2+2cx-c, irreducible Pisot by the corpus screen and the Routh screen; F1_c has empty on-main L_sigma; F3_c has exactly the on-main types (1,2,2,0) and (2,0,1,2), both removed by the on-main legal-predecessor rule because the bigram 12 is illegal, and no hub-based phase-zero birth seam; c = 2 keeps legal types and c = 64 is refused; the non-primitive 1/0/22 (det -2, empty on-main L_sigma, strict system (01,10),(10,01)) is refused by the legal list, whose emptiness is read as an exclusion only for primitive input; the legal filter keeps every literal birth type of the strict controls and of 10/102/211; left strong-coincidence levels (4,1,5) and (1,4,2) for 3 <= c <= 8; no C4 inference")
