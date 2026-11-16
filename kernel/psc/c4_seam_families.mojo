"""Two nonunit seam families, and the on-main local birth sieve `L_sigma` read
as a list of types with the on-main legal-predecessor rule applied to it.

Sources on main. The sieve `L_sigma` and its *uniform zero-candidate
eliminator* (for a primitive substitution with `det M != 0`, an empty
`L_sigma` excludes every finite strict child-closed system of that one
substitution; the on-main statement says "primitive expanding". Without
primitivity this is false: `1/0/22` has an empty `L_sigma`, `det M = -2`
and the strict system `{(01,10), (10,01)}`, pinned in
`kernel/tests/test_c4_reducible_pisot_controls.mojo`):
`docs/c4-bilateral-birth-rigidity-2026-11-02.md` §9, implemented as
`psc.c4_cut_alignment.unresolved_local_birth_types`, which returns the
*number* of types. Legal bigrams and the rule that a cut at an image boundary
takes its left letter from the image of a *legal* predecessor of the source
letter: `docs/c4-legal-seams-2026-11-04.md` and
`docs/c4-seam-birth-orbits-2026-11-04.md`, implemented as
`psc.c4_legal_seams.legal_bigrams` and `_preceding_matches`. The families and
the statement they are used for: `docs/c4-closure-attempt-2026-11-16.md`
(nonunit route).

**Type convention.** A type is `(a, r, b, s)`: the cut lies in the top image
`sigma(a)` after `r` letters and in the bottom image `sigma(b)` after `s`
letters, `0 <= r < |sigma(a)|`, `0 <= s < |sigma(b)|`. So `sigma(a)[r]` and
`sigma(b)[s]` are the letters to the right of the cut, and the letter to its
left is `sigma(a)[r - 1]` for `r > 0` and the last letter of the image of the
preceding source letter for `r = 0`. Lists are flat, four entries a type, in
the loop order `a, r, b, s` of the on-main function.

**What this module adds, and nothing else.**

* `f1_family(c)`, `f3_family(c)`: the images of
  `F1_c = (0^(c-1) 1, 1 2 0^(c-1), 0^c)` and `F3_c = (0^(c-1) 1 0, 0 2 1, 2 0)`.
* `local_birth_types`: the members of `L_sigma`, enumerated with the on-main
  predicates of `psc.c4_cut_alignment` under the four conditions of §9. It
  raises unless their number is the on-main count, so it cannot drift from
  `unresolved_local_birth_types`. Like that count it checks the determinant
  and not primitivity.
* `legal_local_birth_types`: the members of `L_sigma` that keep a
  non-collapsing left pair when condition 4 of §9 is read with
  `_preceding_matches` (at digit zero only last letters of images of *legal*
  predecessors) instead of all three preceding source letters. It is a subset
  of `L_sigma` by construction. No hub, track or phase is chosen. It raises on
  a substitution that is not primitive: its empty list is the one the notes
  read as an exclusion, and without primitivity it would not be one.

**What the on-main functions express without this module.** The count
`|L_sigma|`, and the hub-based seam lists `phase_zero_legal_seams` /
`phase_zero_birth_seams`, which fix a left hub on the top track and a right
hub on a stated track (a phase-zero hypothesis). Neither returns the types,
and neither applies the legal-predecessor rule without choosing hubs; that
composition is the only thing added here.

**Not proved here.** Everything here is exact integer arithmetic on finite
words; no theorem is proved by enumeration. That an empty
`legal_local_birth_types` excludes a strict system rests on written proofs:
the eliminator of §9, and legality of the words of a strict system rooted at
periodic rays (Lemma RL, section 5.2 of
`docs/c4-closure-attempt-2026-11-16.md`, used through Proposition C2,
section 5.4, for primitive substitutions with `det M != 0`; recorded proofs,
not machine-checked; on main the legality lemma is stated for a phase-zero
strongly connected carrier and for the carrier modulo track swap). A nonempty
list is an over-approximation and never evidence of a strict system. Singular
incidence, malformed images and images longer than 64 letters are refused by
the on-main functions this module calls, and a substitution that is not
primitive by `legal_local_birth_types` itself (refuse to conclude). No C4,
BH, G1 or PSC inference is made.
"""

from finite_linear_algebra.mat3 import Mat3
from psc.bpa import prefix_endpoint_map, substitution_incidence, suffix_endpoint_map
from psc.c4_cut_alignment import (
    _det3,
    _eventually_equal,
    _integral_column_lift,
    _prefix_counts,
    unresolved_local_birth_types,
)
from psc.c4_legal_seams import _preceding_matches, legal_bigrams
from psc.pisot import is_primitive
from psc.words import ALPHABET

# Smallest parameter the constructors accept. The families are stated for
# `c >= 3`; `c = 2` is kept as the calibration below that range.
comptime FAMILY_MIN = 2


def _zeros(n: Int) -> List[Int]:
    return List[Int](length=n, fill=0)


def f1_family(c: Int) raises -> List[List[Int]]:
    """`F1_c = (0^(c-1) 1, 1 2 0^(c-1), 0^c)`."""
    if c < FAMILY_MIN:
        raise Error("the seam families need c >= 2")
    var image0 = _zeros(c - 1)
    image0.append(1)
    var image1: List[Int] = [1, 2]
    image1 += _zeros(c - 1)
    var out = List[List[Int]]()
    out.append(image0^)
    out.append(image1^)
    out.append(_zeros(c))
    return out^


def f3_family(c: Int) raises -> List[List[Int]]:
    """`F3_c = (0^(c-1) 1 0, 0 2 1, 2 0)`."""
    if c < FAMILY_MIN:
        raise Error("the seam families need c >= 2")
    var image0 = _zeros(c - 1)
    image0.append(1)
    image0.append(0)
    var out = List[List[Int]]()
    out.append(image0^)
    out.append([0, 2, 1])
    out.append([2, 0])
    return out^


def local_birth_types(sigma: List[List[Int]]) raises -> List[Int]:
    """The members `(a, r, b, s)` of `L_sigma`, flat, in the on-main loop
    order. Conditions (§9): `(r, s) != (0, 0)`; the right letters are not
    eventually equal under the first-letter map; the difference of the two
    proper-prefix Parikh vectors lies in `M Z^3`; some pair of possible left
    letters is not eventually equal under the last-letter map, where a digit
    zero ranges over the last letters of all three images.

    The on-main count is taken first, so its refusals (singular incidence,
    malformed images, an image longer than 64 letters) are this function's
    refusals; a disagreement between the list and that count raises.

    No primitivity check is made here, as none is made by the on-main count.
    An empty list is an exclusion only under the hypotheses of the eliminator
    (primitive, `det M != 0`); `legal_local_birth_types` checks both."""
    var expected = unresolved_local_birth_types(sigma)
    var m = substitution_incidence(sigma)
    var det = _det3(m)
    var first = prefix_endpoint_map(sigma)
    var last = suffix_endpoint_map(sigma)
    var out = List[Int]()
    for a in range(ALPHABET):
        for r in range(len(sigma[a])):
            for b in range(ALPHABET):
                for s in range(len(sigma[b])):
                    if r == 0 and s == 0:
                        continue
                    if _eventually_equal(first, sigma[a][r], sigma[b][s]):
                        continue
                    var qa = _prefix_counts(sigma[a], r)
                    var qb = _prefix_counts(sigma[b], s)
                    var correction: List[Int] = [qa[0] - qb[0], qa[1] - qb[1], qa[2] - qb[2]]
                    if not _integral_column_lift(m, det, correction):
                        continue
                    var possible_left = False
                    for prev_a in range(ALPHABET):
                        for prev_b in range(ALPHABET):
                            var left_a = sigma[a][r - 1] if r > 0 else last[prev_a]
                            var left_b = sigma[b][s - 1] if s > 0 else last[prev_b]
                            if not _eventually_equal(last, left_a, left_b):
                                possible_left = True
                    if possible_left:
                        out += [a, r, b, s]
    if len(out) != 4 * expected:
        raise Error("the enumerated local birth types disagree with the on-main count")
    return out^


def legal_left_pair_exists(
    sigma: List[List[Int]], legal: List[Bool], last: List[Int], a: Int, r: Int, b: Int, s: Int
) raises -> Bool:
    """Whether the cut of type `(a, r, b, s)` has left letters `(x, y)` that
    are not eventually equal under the last-letter map, `x` and `y` ranging
    over the letters `_preceding_matches` allows: the image letter before the
    digit, or at digit zero the last letter of the image of a legal
    predecessor of the source letter. `legal` is `legal_bigrams(sigma)` and
    `last` the last-letter map."""
    if len(legal) != ALPHABET * ALPHABET or len(last) != ALPHABET:
        raise Error("legal-predecessor test needs nine bigram flags and a last-letter map")
    if a < 0 or a >= ALPHABET or b < 0 or b >= ALPHABET:
        raise Error("birth type source letter outside the alphabet")
    if r < 0 or r >= len(sigma[a]) or s < 0 or s >= len(sigma[b]):
        raise Error("birth type digit outside its image")
    for x in range(ALPHABET):
        if not _preceding_matches(sigma, legal, a, r, x):
            continue
        for y in range(ALPHABET):
            if not _preceding_matches(sigma, legal, b, s, y):
                continue
            if not _eventually_equal(last, x, y):
                return True
    return False


def legal_local_birth_types(sigma: List[List[Int]]) raises -> List[Int]:
    """The members of `local_birth_types(sigma)` for which
    `legal_left_pair_exists`, flat, in the same order. Empty means: no local
    birth type of `sigma` survives the lattice, endpoint and legal-predecessor
    conditions together.

    Raises when `sigma` is not primitive. Proposition C2 of the
    closure-attempt note (primitive, `det M != 0`) is what turns an empty
    list into "no strict system"; for the non-primitive `1/0/22` the list
    would be empty although `{(01,10), (10,01)}` is a strict system. The
    determinant is checked by the on-main count."""
    var types = local_birth_types(sigma)  # refuses first, as the on-main count does
    if not is_primitive(Mat3(substitution_incidence(sigma))):
        raise Error(
            "legal local birth types: the substitution is not primitive; Proposition C2 does not apply"
            + " and an empty list would not be an exclusion"
        )
    var legal = legal_bigrams(sigma)
    var last = suffix_endpoint_map(sigma)
    var out = List[Int]()
    for t in range(len(types) // 4):
        var a = types[4 * t]
        var r = types[4 * t + 1]
        var b = types[4 * t + 2]
        var s = types[4 * t + 3]
        if legal_left_pair_exists(sigma, legal, last, a, r, b, s):
            out += [a, r, b, s]
    return out^
