"""A substitution-local upper bound on the least strong-coincidence level.

This module extracts the quantitative statement that follows from the affine
coincidence automaton without promoting it to a uniform family theorem.  If the
language for a letter pair is nonempty, a shortest accepting run is simple, so
its length is at most the number of reachable automaton states minus one.

The bound is exact and unconditional for a fixed substitution.  Uniform use
over the alphabet-three PIP family still requires a substitution-independent
bound on the reachable state count, and it does not prove that the accepted
language is nonempty.  Those two obligations are deliberately returned rather
than hidden.
"""

from psc.automata import witness
from psc.coincidence_formula import coincidence_automaton
from psc.words import ALPHABET


struct PairDepthBound(Copyable, Movable):
    """The fixed-substitution graph bound and its nonemptiness outcome."""

    var states: Int
    var upper: Int
    var level: Int
    var empty: Bool

    def __init__(out self, states: Int, upper: Int, level: Int, empty: Bool):
        self.states = states
        self.upper = upper
        self.level = level
        self.empty = empty

    def certifies_level(self) -> Bool:
        return self.empty or (self.level >= 0 and self.level <= self.upper)


def pair_depth_bound(
    sigma: List[List[Int]], top: Int, bottom: Int
) raises -> PairDepthBound:
    """Build the complete reachable affine automaton for one pair.

    When its language is nonempty, the returned shortest level is at most
    `states - 1`: deleting a repeated-state segment from a shortest run would
    give a shorter accepting run.  The rejecting sink is retained, so this is a
    safe bound rather than a sharpened count of coaccessible live states.
    """
    var automaton = coincidence_automaton(sigma, top, bottom)
    var found = witness(automaton)
    var upper = automaton.states() - 1
    var level = -1 if found.empty else len(found.word)
    var out = PairDepthBound(automaton.states(), upper, level, found.empty)
    if not out.certifies_level():
        raise Error("shortest coincidence path exceeds its finite-state bound")
    return out


def substitution_depth_bound(sigma: List[List[Int]]) raises -> PairDepthBound:
    """The maximum fixed-substitution bound over the three unordered pairs.

    `empty` records whether some pair language is empty.  In that case
    `level = -1`; the state bound remains diagnostic and is not a coincidence
    theorem.
    """
    var largest_states = 0
    var largest_upper = 0
    var largest_level = 0
    var any_empty = False
    for top in range(ALPHABET):
        for bottom in range(top + 1, ALPHABET):
            var pair = pair_depth_bound(sigma, top, bottom)
            if pair.states > largest_states:
                largest_states = pair.states
            if pair.upper > largest_upper:
                largest_upper = pair.upper
            if pair.empty:
                any_empty = True
            elif pair.level > largest_level:
                largest_level = pair.level
    return PairDepthBound(
        largest_states,
        largest_upper,
        -1 if any_empty else largest_level,
        any_empty,
    )
