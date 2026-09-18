"""A substitution-local upper bound on the least strong-coincidence level.

This module extracts the quantitative statement that follows from the affine
coincidence automaton without promoting it to a uniform family theorem.  If the
language for a letter pair is nonempty, a shortest accepting run is simple, so
its length is at most the number of coaccessible automaton states minus one.

The graph inequality is unconditional, but the executable construction is
exact only when the shared powered-field kernel accepts the input; that kernel
currently has a documented incidence-entry bound of 64 and raises outside it.
Such a refusal is inconclusive. Uniform use over the alphabet-three PIP family
therefore also requires removal of that implementation boundary, as well as a
substitution-independent coaccessible-state bound and a proof of nonemptiness.
"""

from psc.automata import Dfa, witness
from psc.coincidence_formula import coincidence_automaton
from psc.words import ALPHABET


struct PairDepthBound(Copyable, Movable):
    """The fixed-substitution graph bound and its nonemptiness outcome."""

    var states: Int
    var coaccessible: Int
    var upper: Int
    var level: Int
    var empty: Bool

    def __init__(out self, states: Int, coaccessible: Int, upper: Int, level: Int, empty: Bool):
        self.states = states
        self.coaccessible = coaccessible
        self.upper = upper
        self.level = level
        self.empty = empty

    def certifies_level(self) -> Bool:
        return self.empty or (self.level >= 0 and self.level <= self.upper)



def coaccessible_state_count(automaton: Dfa) raises -> Int:
    """Count reachable states from which some accepting state is reachable.

    The automata built here contain only forward-reachable states.  Reverse
    reachability from every accepting state therefore gives exactly the states
    that can lie on an accepting run.  This is a graph computation: no spectral
    approximation and no additional substitution hypothesis enters.
    """
    var live = List[Bool](length=automaton.states(), fill=False)
    var queue = List[Int]()
    for state in range(automaton.states()):
        if automaton.accepting[state]:
            live[state] = True
            queue.append(state)
    var head = 0
    while head < len(queue):
        var target = queue[head]
        head += 1
        for source in range(automaton.states()):
            if live[source]:
                continue
            for letter in range(automaton.letters):
                if automaton.step(source, letter) == target:
                    live[source] = True
                    queue.append(source)
                    break
    return len(queue)

def pair_depth_bound(
    sigma: List[List[Int]], top: Int, bottom: Int
) raises -> PairDepthBound:
    """Build the complete reachable affine automaton for one pair.

    When its language is nonempty, the returned shortest level is at most
    `coaccessible - 1`: every state on a shortest accepting run can reach its
    accepting endpoint, and deleting a repeated-state segment would give a
    shorter run. States that cannot reach acceptance—including the rejecting
    sink—are excluded exactly by reverse reachability.

    The shared exact field constructor currently raises when an incidence entry
    exceeds 64. That is an explicit executable-domain refusal, not a negative
    coincidence result and not a restriction in the mathematical proposition.
    """
    var automaton = coincidence_automaton(sigma, top, bottom)
    var found = witness(automaton)
    var coaccessible = coaccessible_state_count(automaton)
    var upper = -1 if found.empty else coaccessible - 1
    var level = -1 if found.empty else len(found.word)
    var out = PairDepthBound(
        automaton.states(), coaccessible, upper, level, found.empty
    )
    if not out.certifies_level():
        raise Error("shortest coincidence path exceeds its finite-state bound")
    return out^


def substitution_depth_bound(sigma: List[List[Int]]) raises -> PairDepthBound:
    """The maximum fixed-substitution bound over the three unordered pairs.

    `empty` records whether some pair language is empty.  In that case
    `level = -1`; the state bound remains diagnostic and is not a coincidence
    theorem.
    """
    var largest_states = 0
    var largest_coaccessible = 0
    var largest_upper = 0
    var largest_level = 0
    var any_empty = False
    for top in range(ALPHABET):
        for bottom in range(top + 1, ALPHABET):
            var pair = pair_depth_bound(sigma, top, bottom)
            if pair.states > largest_states:
                largest_states = pair.states
            if pair.coaccessible > largest_coaccessible:
                largest_coaccessible = pair.coaccessible
            if pair.upper > largest_upper:
                largest_upper = pair.upper
            if pair.empty:
                any_empty = True
            elif pair.level > largest_level:
                largest_level = pair.level
    return PairDepthBound(
        largest_states,
        largest_coaccessible,
        largest_upper,
        -1 if any_empty else largest_level,
        any_empty,
    )
