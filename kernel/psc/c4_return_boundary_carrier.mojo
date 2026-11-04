"""Occurrence-complete return-cut refinement for the exact #487 specimen.

28 local states, 80 child occurrences. Word-register residuals are NOT a
finite configuration space. No general C4/G1/PSC inference is implemented.
Paper proof: docs/c4-return-boundary-carrier-2026-11-04.md.
"""

from substitution_dynamics.substitution import Substitution, validate_word
from psc.bpa import apply_substitution
from psc.c4_return_induction_prefix_satellite import (
    source_sigma, source_return_words, expected_return_substitution,
    induce_marker_zero_return,
)


struct CutEdge(Copyable, Movable):
    var child: Int
    var occurrence: Int
    var target_return: Int
    var target_offset: Int
    var emitted: List[Int]

    def __init__(
        out self, child: Int, occurrence: Int, target_return: Int,
        target_offset: Int, emitted: List[Int],
    ):
        self.child = child
        self.occurrence = occurrence
        self.target_return = target_return
        self.target_offset = target_offset
        self.emitted = emitted.copy()


struct ResidualCode(Copyable, Movable):
    var phase: Int
    var common: List[Int]
    var tail: List[Int]
    var longer: List[Int]
    var shorter: List[Int]

    def __init__(
        out self, phase: Int, common: List[Int], tail: List[Int],
        longer: List[Int], shorter: List[Int],
    ):
        self.phase = phase
        self.common = common.copy()
        self.tail = tail.copy()
        self.longer = longer.copy()
        self.shorter = shorter.copy()


struct ReturnBoundaryCarrier(Copyable, Movable):
    var sigma: List[List[Int]]
    var words: List[List[Int]]
    var tau: List[List[Int]]

    def __init__(out self) raises:
        self.sigma = source_sigma()
        self.words = source_return_words()
        self.tau = induce_marker_zero_return(self.sigma, self.words)
        if self.tau != expected_return_substitution():
            raise Error("exact source return substitution changed")

    def _check_point(self, j: Int, d: Int) raises:
        if j < 0 or j >= 4:
            raise Error("return symbol outside 0..3")
        if d < 0 or d >= len(self.words[j]):
            raise Error("cut must precede a letter; terminal cut is not a state")

    def point_id(self, j: Int, d: Int) raises -> Int:
        self._check_point(j, d)
        var result = d
        for k in range(j):
            result += len(self.words[k])
        return result

    def decode(self, code: List[Int]) raises -> List[Int]:
        if len(code) > 4096:
            raise Error("return decoding budget exceeded before allocation")
        validate_word(code, 4)
        var result = List[Int]()
        for c in code:
            for x in self.words[c]:
                result.append(x)
        return result^

    def tau_apply(self, code: List[Int]) raises -> List[Int]:
        if len(code) > 4096:
            raise Error("return-code input budget exceeded")
        validate_word(code, 4)
        var size = 0
        for c in code:
            size += len(self.tau[c])
        if size > 4096:
            raise Error("return-code output budget exceeded before allocation")
        # tau was constructed and checked above; reuse the vendored primitive.
        return Substitution(self.tau.copy(), 4).apply(code)

    def code_image(self, letter: Int, level: Int) raises -> List[Int]:
        if letter < 0 or letter >= 4 or level < 0 or level > 6:
            raise Error("invalid return letter or bounded replay depth")
        var word: List[Int] = [letter]
        for _ in range(level):
            word = self.tau_apply(word)
        return word^

    def edge(self, j: Int, d: Int, t: Int) raises -> CutEdge:
        self._check_point(j, d)
        var letter = self.words[j][d]
        if t < 0 or t >= len(self.sigma[letter]):
            raise Error("child occurrence outside source letter image")
        # Precompute the physical prefix length; no inflated deep word needed.
        var pos = t
        for i in range(d):
            pos += len(self.sigma[self.words[j][i]])
        var emitted = List[Int]()
        for k in range(len(self.tau[j])):
            var c = self.tau[j][k]
            if pos < len(self.words[c]):
                if self.words[c][pos] != self.sigma[letter][t]:
                    raise Error("return recoding changed the actual next letter")
                return CutEdge(t, k, c, pos, emitted)
            pos -= len(self.words[c])
            emitted.append(c)
        raise Error("complete return factorization failed to contain a child")

    def lifted_images(self) raises -> List[List[Int]]:
        var result = List[List[Int]]()
        for j in range(4):
            for d in range(len(self.words[j])):
                var image = List[Int]()
                var x = self.words[j][d]
                for t in range(len(self.sigma[x])):
                    var e = self.edge(j, d, t)
                    image.append(self.point_id(e.target_return, e.target_offset))
                result.append(image)
        return result^

    def residual(self, level: Int, kind: Int) raises -> ResidualCode:
        """kind 0: pair (0,3); kind 1: pair (1,2). Level cap is not a theorem."""
        if level < 0 or level > 6 or kind < 0 or kind > 1:
            raise Error("invalid residual pair or bounded materialization depth")
        var phase = kind
        var q = List[Int]()
        var v = List[Int]()
        for _ in range(level):
            var next_q = self.tau_apply(q)
            if phase == 0:
                next_q.append(0)
            else:
                next_q.append(3)
                next_q.append(2)
            var next_v: List[Int] = [2]
            var image_v = self.tau_apply(v)
            for c in image_v:
                next_v.append(c)
            q = next_q
            v = next_v
            phase = 1
        var longer = q.copy()
        var shorter = q.copy()
        if phase == 0:
            longer.append(0)
            shorter.append(3)
        else:
            longer.append(1)
            shorter.append(2)
        for c in v:
            longer.append(c)
        return ResidualCode(phase, q, v, longer, shorter)
