"""Conjugates of powers of `sigma` in Barge's PDS class.

Barge (2016) proves pure discrete spectrum for a primitive, non-periodic
substitution with Pisot inflation that is *injective on initial letters and
constant on final letters* (hypotheses as audited in
docs/p1b-strict-zipper-literature-gate-2026-09-21.md). Reversing every image
preserves the spectrum, so the *mirror* class (constant on initial letters,
injective on final letters) is covered too. Powers `sigma^n` and conjugates
`tau(a) = u^{-1} sigma^n(a) u` (all images of `sigma^n` beginning with `u`),
or `tau(a) = v sigma^n(a) v^{-1}` (all ending with `v`), have the same tiling
space up to translation, hence the same spectrum, and the same incidence
matrix up to the power.

For a left rotation every image of `tau` ends with `u`, so `tau` is constant
on final letters; it is injective on initial letters exactly when the letters
following the common prefix are pairwise distinct, which needs the *maximal*
common prefix (a shorter one leaves them all equal). Symmetrically for right
rotations. So, per power, three candidates decide membership: `sigma^n`, its
maximal left rotation and its maximal right rotation.

A witness gives PDS for `sigma` by Barge's theorem, hence PPVC by Theorem S
(docs/p1b-vertex-coincidence-box-2026-10-02.md §5.1). This module decides
membership exactly; it proves nothing about specimens without a witness.
"""

from psc.dumont_thomas import power_substitution


comptime KIND_NONE = 0
comptime KIND_DIRECT = 1
comptime KIND_LEFT_ROTATION = 2
comptime KIND_RIGHT_ROTATION = 3


def _pairwise_distinct(a: Int, b: Int, c: Int) -> Bool:
    return a != b and a != c and b != c


def injective_on_initial(t: List[List[Int]]) -> Bool:
    return _pairwise_distinct(t[0][0], t[1][0], t[2][0])


def injective_on_final(t: List[List[Int]]) -> Bool:
    return _pairwise_distinct(t[0][len(t[0]) - 1], t[1][len(t[1]) - 1], t[2][len(t[2]) - 1])


def constant_on_initial(t: List[List[Int]]) -> Bool:
    return t[0][0] == t[1][0] and t[1][0] == t[2][0]


def constant_on_final(t: List[List[Int]]) -> Bool:
    var a = t[0][len(t[0]) - 1]
    return a == t[1][len(t[1]) - 1] and a == t[2][len(t[2]) - 1]


def in_barge_class(t: List[List[Int]]) -> Bool:
    """Injective on initial letters and constant on final letters."""
    return injective_on_initial(t) and constant_on_final(t)


def in_mirror_class(t: List[List[Int]]) -> Bool:
    """Constant on initial letters and injective on final letters."""
    return constant_on_initial(t) and injective_on_final(t)


def common_prefix_length(t: List[List[Int]]) -> Int:
    var k = 0
    while k < len(t[0]) and k < len(t[1]) and k < len(t[2]):
        if t[0][k] != t[1][k] or t[0][k] != t[2][k]:
            break
        k += 1
    return k


def common_suffix_length(t: List[List[Int]]) -> Int:
    var k = 0
    while k < len(t[0]) and k < len(t[1]) and k < len(t[2]):
        var x = t[0][len(t[0]) - 1 - k]
        if x != t[1][len(t[1]) - 1 - k] or x != t[2][len(t[2]) - 1 - k]:
            break
        k += 1
    return k


def rotate_left(t: List[List[Int]], k: Int) -> List[List[Int]]:
    """`tau(a) = u^{-1} t(a) u` for the common prefix `u` of length `k`."""
    var out = List[List[Int]]()
    for a in range(len(t)):
        var w = List[Int]()
        for i in range(k, len(t[a])):
            w.append(t[a][i])
        for i in range(k):
            w.append(t[0][i])
        out.append(w^)
    return out^


def rotate_right(t: List[List[Int]], k: Int) -> List[List[Int]]:
    """`tau(a) = v t(a) v^{-1}` for the common suffix `v` of length `k`."""
    var out = List[List[Int]]()
    for a in range(len(t)):
        var w = List[Int]()
        for i in range(len(t[0]) - k, len(t[0])):
            w.append(t[0][i])
        for i in range(len(t[a]) - k):
            w.append(t[a][i])
        out.append(w^)
    return out^


struct BargeWitness(Copyable, Movable, Writable):
    var power: Int  # 0 when none was found
    var kind: Int
    var mirror: Bool

    def __init__(out self, power: Int, kind: Int, mirror: Bool):
        self.power = power
        self.kind = kind
        self.mirror = mirror

    def found(self) -> Bool:
        return self.kind != KIND_NONE

    def write_to[W: Writer](self, mut w: W):
        w.write("power=", self.power, " kind=", self.kind, " mirror=", self.mirror)


def _classify(t: List[List[Int]], power: Int, kind: Int) -> BargeWitness:
    if in_barge_class(t):
        return BargeWitness(power, kind, False)
    if in_mirror_class(t):
        return BargeWitness(power, kind, True)
    return BargeWitness(0, KIND_NONE, False)


def barge_witness(sigma: List[List[Int]], max_power: Int) raises -> BargeWitness:
    """The least power `n <= max_power` at which `sigma^n` or its maximal left
    or right rotation lies in Barge's class or its mirror."""
    for n in range(1, max_power + 1):
        var t = power_substitution(sigma, n)
        var w = _classify(t, n, KIND_DIRECT)
        if w.found():
            return w^
        var p = common_prefix_length(t)
        if p > 0:
            w = _classify(rotate_left(t, p), n, KIND_LEFT_ROTATION)
            if w.found():
                return w^
        var s = common_suffix_length(t)
        if s > 0:
            w = _classify(rotate_right(t, s), n, KIND_RIGHT_ROTATION)
            if w.found():
                return w^
    return BargeWitness(0, KIND_NONE, False)
