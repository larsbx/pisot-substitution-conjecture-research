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


def first_pair_mask(states: List[Pair]) raises -> Int:
    if len(states) == 0:
        raise Error("empty supplied system")
    var mask = 0
    for s in states:
        if s.length() == 0 or not is_balanced(s):
            raise Error("supplied state is empty or unbalanced")
        if len(coincidence_boundaries(s.u, s.v)) != 2:
            raise Error("supplied state is reducible")
        mask |= pair_bit(s.u[0], s.v[0])
    return mask


def inflated_cut_pair_mask(sigma: List[List[Int]], states: List[Pair], depth: Int) raises -> Int:
    """Cut pairs of the complete balanced factorisation of sigma^depth(S), all S.

    Raises on a coincident factor: the supplied system is then not strict."""
    if depth < 0:
        raise Error("negative inflation depth")
    var mask = 0
    for s in states:
        var top = s.u.copy()
        var bottom = s.v.copy()
        for _ in range(depth):
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
    var top: List[Int] = [a]
    var bottom: List[Int] = [b]
    for n in range(1, max_level + 1):
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
    return CutPairAudit(first, cut, image, witnessed)
