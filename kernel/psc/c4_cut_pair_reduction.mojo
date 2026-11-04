"""Exact cut-pair audit of a supplied strict C4 balanced-pair system.

Contract (docs/c4-cut-pair-productivity-2026-11-04.md, Theorem A). For a
finite strictly child-closed system C of irreducible noncoincident balanced
pairs, the set A(C) of unordered first-letter pairs ("cut pairs") satisfies

* every balanced cut of every inflation of every state carries a pair of A(C);
* A(C) is closed under the initial-letter map g x g, and g never collapses it;
* no pair of A(C) is left strongly coincident.

This module checks the first two items literally on supplied words, at a
stated inflation depth, and reports the third as a bounded search: a missing
strong-coincidence witness within `max_level` is an exhausted budget, never a
verdict. A coincident factor, an unbalanced or reducible state, a cut pair
outside A(C), or a collapsing initial-letter map aborts the audit (fail closed:
refuse to conclude). No C4, BH, G1 or PSC inference is made here.
"""

from psc.bpa import apply_substitution, coincidence_boundaries, prefix_endpoint_map, sigma3
from psc.words import ALPHABET, Pair, is_balanced


def pair_bit(a: Int, b: Int) raises -> Int:
    """Bit of the unordered letter pair {a,b}: {0,1}->1, {0,2}->2, {1,2}->4."""
    if a == b or a < 0 or b < 0 or a >= ALPHABET or b >= ALPHABET:
        raise Error("cut pair must consist of two distinct letters")
    return 1 << (a + b - 1)


def require_balanced_letters(s: Pair) raises:
    """Range-check every letter before any Parikh indexing, then balance."""
    if s.length() <= 0:
        raise Error("cut-pair input is empty")
    for symbol in s.u:
        if symbol < 0 or symbol >= ALPHABET:
            raise Error("invalid top word letter")
    for symbol in s.v:
        if symbol < 0 or symbol >= ALPHABET:
            raise Error("invalid bottom word letter")
    if not is_balanced(s):
        raise Error("cut-pair input is not balanced")


def first_pair_mask(states: List[Pair]) raises -> Int:
    if len(states) == 0:
        raise Error("empty supplied system")
    var mask = 0
    for s in states:
        require_balanced_letters(s)
        if len(coincidence_boundaries(s.u, s.v)) != 2:
            raise Error("supplied state is reducible")
        mask |= pair_bit(s.u[0], s.v[0])
    return mask


def inflated_cut_pair_mask(sigma: List[List[Int]], states: List[Pair], depth: Int) raises -> Int:
    """Cut pairs of the complete balanced factorisation of sigma^depth(S), all S.

    Raises on a coincident factor: the supplied system is then not strict."""
    _ = sigma3(sigma)
    if depth < 0 or depth > 10:
        raise Error("cut-pair inflation depth must lie in 0..10")
    var image_bound = 0
    for a in range(ALPHABET):
        if len(sigma[a]) == 0:
            raise Error("cut-pair substitution has an empty image")
        image_bound = max(image_bound, len(sigma[a]))
    var mask = 0
    for s in states:
        require_balanced_letters(s)
        var top = s.u.copy()
        var bottom = s.v.copy()
        for _ in range(depth):
            if len(top) > 100000 // image_bound or len(bottom) > 100000 // image_bound:
                raise Error("cut-pair inflation budget exhausted")
            top = apply_substitution(sigma, top)
            bottom = apply_substitution(sigma, bottom)
        var cuts = coincidence_boundaries(top, bottom)
        for k in range(len(cuts) - 1):
            var c = cuts[k]
            if top[c] == bottom[c]:
                raise Error("coincident factor: supplied system is not strict")
            mask |= pair_bit(top[c], bottom[c])
    return mask


def initial_image_mask(sigma: List[List[Int]], mask: Int) raises -> Int:
    """(g x g)(A) for the initial-letter map g; a collapsed pair aborts."""
    var g = prefix_endpoint_map(sigma)
    var image = 0
    for a in range(ALPHABET):
        for b in range(a + 1, ALPHABET):
            if mask & pair_bit(a, b):
                if g[a] == g[b]:
                    raise Error("initial-letter map collapses a cut pair: first child is coincident")
                image |= pair_bit(g[a], g[b])
    return image


def strong_coincidence_level(sigma: List[List[Int]], a: Int, b: Int, max_level: Int) raises -> Int:
    """Least n <= max_level with sigma^n(a)=P c Q, sigma^n(b)=P' c Q', p(P)=p(P').

    Returns -1 when the budget is exhausted (not a non-coincidence verdict)."""
    _ = pair_bit(a, b)
    _ = sigma3(sigma)
    if max_level <= 0 or max_level > 12:
        raise Error("bounded strong coincidence requires 1 <= level <= 12")
    var image_bound = 0
    for letter in range(ALPHABET):
        if len(sigma[letter]) == 0:
            raise Error("strong coincidence substitution has an empty image")
        image_bound = max(image_bound, len(sigma[letter]))
    var top: List[Int] = [a]
    var bottom: List[Int] = [b]
    for n in range(1, max_level + 1):
        if len(top) > 100000 // image_bound or len(bottom) > 100000 // image_bound:
            raise Error("strong coincidence word budget exhausted")
        top = apply_substitution(sigma, top)
        bottom = apply_substitution(sigma, bottom)
        var delta: List[Int] = [0, 0, 0]
        for i in range(min(len(top), len(bottom))):
            if delta[0] == 0 and delta[1] == 0 and delta[2] == 0 and top[i] == bottom[i]:
                return n
            delta[top[i]] += 1
            delta[bottom[i]] -= 1
    return -1


struct CutPairAudit(Copyable, Movable):
    var first_mask: Int
    var cut_mask: Int
    var initial_image: Int
    var witnessed_mask: Int

    def __init__(out self, first_mask: Int, cut_mask: Int, initial_image: Int, witnessed_mask: Int):
        self.first_mask = first_mask
        self.cut_mask = cut_mask
        self.initial_image = initial_image
        self.witnessed_mask = witnessed_mask


def audit_cut_pairs(
    sigma: List[List[Int]], states: List[Pair], depth: Int, max_level: Int
) raises -> CutPairAudit:
    _ = sigma3(sigma)
    var first = first_pair_mask(states)
    var cut = inflated_cut_pair_mask(sigma, states, depth)
    if cut & ~first:
        raise Error("an inflated cut pair is outside A(C): supplied system is not child-closed")
    var image = initial_image_mask(sigma, first)
    if image & ~first:
        raise Error("(g x g)(A) leaves A(C): supplied system is not child-closed")
    var witnessed = 0
    for a in range(ALPHABET):
        for b in range(a + 1, ALPHABET):
            if first & pair_bit(a, b) and strong_coincidence_level(sigma, a, b, max_level) >= 0:
                witnessed |= pair_bit(a, b)
    if witnessed != 0:
        # A real common-letter/equal-prefix witness makes the allegedly
        # strictly closed input impossible, even when the separately
        # chosen finite inflation depth has not yet reached it.
        raise Error("cut-pair strong-coincidence witness refutes supplied strict system")
    return CutPairAudit(first, cut, image, witnessed)
