"""Conjugacy classes of a substitution by letter rotations, decided exactly.

`tau` is a *left conjugate* of `sigma` by the word `p` when
`sigma(a) p = p tau(a)` for every letter `a`. Then `sigma` and `tau` generate
the same subshift and the same tiling space up to translation, with the same
incidence matrix, so pure discrete spectrum transfers between them
(docs/sadic-transfer-literature-gate-2026-10-11.md §2).

A one-letter step needs every image to begin with the same letter `a`:
`tau(b) = a^{-1} sigma(b) a`. A conjugacy by `p = a p'` factors through that
step, so the closure of `sigma` under one-letter left and right steps is its
whole conjugacy class. Steps keep image lengths, so the class is finite;
`conjugacy_class` still refuses past an explicit cap rather than truncating.

Spectral conclusions are the imported invariance under its hypotheses. This
module decides the combinatorics only. A class of size one proves nothing
about the spectrum.

docs/lateral-generalization-strategy-2026-10-23.md, move 1.
"""

from psc.bpa import substitution_incidence
from substitution_dynamics.barge_class import (
    common_prefix_length,
    common_suffix_length,
    rotate_left,
    rotate_right,
)
from substitution_dynamics.substitution import Substitution


def _as_substitution(sigma: List[List[Int]]) -> Substitution:
    return Substitution(sigma.copy(), len(sigma))


def common_first_letter(sigma: List[List[Int]]) -> Int:
    """The letter every image begins with, or -1."""
    return sigma[0][0] if common_prefix_length(_as_substitution(sigma)) > 0 else -1


def common_last_letter(sigma: List[List[Int]]) -> Int:
    """The letter every image ends with, or -1."""
    return sigma[0][len(sigma[0]) - 1] if common_suffix_length(_as_substitution(sigma)) > 0 else -1


def step_left(sigma: List[List[Int]]) raises -> List[List[Int]]:
    """`tau(b) = a^{-1} sigma(b) a`, the vendored rotation by one letter;
    raises unless every image begins with `a`."""
    if common_first_letter(sigma) < 0:
        raise Error("no common first letter: a left step is not a conjugacy")
    return rotate_left(_as_substitution(sigma), 1).images.copy()


def step_right(sigma: List[List[Int]]) raises -> List[List[Int]]:
    """`tau(b) = z sigma(b) z^{-1}`, the vendored rotation by one letter;
    raises unless every image ends with `z`."""
    if common_last_letter(sigma) < 0:
        raise Error("no common last letter: a right step is not a conjugacy")
    return rotate_right(_as_substitution(sigma), 1).images.copy()


def same_substitution(s: List[List[Int]], t: List[List[Int]]) -> Bool:
    if len(s) != len(t):
        return False
    for a in range(len(s)):
        if s[a] != t[a]:
            return False
    return True


def _index_of(found: List[List[List[Int]]], t: List[List[Int]]) -> Int:
    for i in range(len(found)):
        if same_substitution(found[i], t):
            return i
    return -1


def conjugacy_class(sigma: List[List[Int]], cap: Int) raises -> List[List[List[Int]]]:
    """Every substitution reachable from `sigma` by one-letter steps, `sigma`
    first. Raises when more than `cap` are found: a truncated class would
    understate it."""
    if cap < 1:
        raise Error("conjugacy class cap must be positive")
    var found = List[List[List[Int]]]()
    found.append(sigma.copy())
    var head = 0
    while head < len(found):
        var s = found[head].copy()
        head += 1
        for side in range(2):
            var ok = common_first_letter(s) >= 0 if side == 0 else common_last_letter(s) >= 0
            if not ok:
                continue
            var t = step_left(s) if side == 0 else step_right(s)
            if _index_of(found, t) < 0:
                if len(found) == cap:
                    raise Error("conjugacy class exceeds its cap; no verdict")
                found.append(t^)
    return found^


def is_left_conjugate_by(sigma: List[List[Int]], tau: List[List[Int]], p: List[Int]) -> Bool:
    """`sigma(a) p == p tau(a)` for every letter: the defining equation, checked
    directly on words, independently of how `tau` was produced."""
    if len(sigma) != len(tau):
        return False
    for a in range(len(sigma)):
        var lhs = sigma[a].copy()
        for x in p:
            lhs.append(x)
        var rhs = p.copy()
        for x in tau[a]:
            rhs.append(x)
        if lhs != rhs:
            return False
    return True


def same_incidence(s: List[List[Int]], t: List[List[Int]]) -> Bool:
    return substitution_incidence(s) == substitution_incidence(t)
