"""The coincidence formula, decided the way the route planned to decide it.

`psc.coincidence_formula` answers `SC(i, j)` with one purpose-built automaton:
its accepting condition is the conjunction, wired in by hand. That settles the
question but it is not the procedure the gate proposed, which was to *write the
formula* and let the automata kernel eliminate its quantifiers. This module is
that procedure, run.

## The formula, and which automaton discharges which conjunct

Over two tracks of Dumont-Thomas digits packed as `p + radix q`, with `P` on
track zero in `sigma^k(i)` and `Q` on track one in `sigma^k(j)`:

    SC(i, j)  ==  exists P, Q of one length :
                      adm_i(P)                      -- numeration_automaton(sigma, i)
                  and adm_j(Q)                      -- numeration_automaton(sigma, j)
                  and (or over letters a :          -- letter_automaton, both tracks
                          end_i(P) = a and end_j(Q) = a)
                  and parikh_i(P) = parikh_j(Q)     -- parikh_equality_automaton

Every conjunct but the last is an automaton `psc.dumont_thomas` already had.
`cylinder` puts a one-track condition on its track, `intersection` and `union`
are the connectives, `is_empty` with `witness` discharges the existential and
returns the instance. Nothing here decides anything itself; it assembles.

The last conjunct is the one the numeration's own signature does not give, and
saying exactly that is the point of assembling the rest from the kernel. A
counting function `n -> |u[0..n)|_a` is not in general first-order definable
from `+` and the letter predicates -- Walnut counts with linear
representations, not formulas -- so the theory has to be extended by the
*equality* of two such counts, which stays recognisable where neither count
does. `parikh_equality_automaton` is that predicate, and adding a recognisable
relation to the structure leaves the first-order theory decidable.

## Why run it when the answer is already known

Because agreeing is evidence and assembling is not the same as asserting. The
direct automaton reads its letters off its own state; the assembly reads them
off the Dumont-Thomas letter map, through the product, the union and the
subset construction. `same_language` between the two says that the kernel's
Boolean algebra, the letter map and the hand-wired condition are one thing --
three pieces of the repository that are supposed to agree and had never been
made to say so.

It also does what the bespoke automaton cannot: `coincident_positions`
projects the pair away and leaves the recognisable *set* of paths in
`sigma^k(i)` at which the pair coincides, which is a formula's answer rather
than a search's.

## What it still does not do

Decide the family. `SC` is decidable per substitution -- three procedures now
agree on that -- and "every substitution in this family" is a different
quantifier: over an infinite, stratified parameter set that fixes the alphabet,
the numeration and the automaton before any of this starts. The family
statement is `Pi_1` over a recursively enumerable family, so a counterexample
would be found by search and no finite computation certifies the positive case
without a uniform argument. The gate says which uniform arguments exist (two
letters, Barge-Diamond) and that three letters is open.
"""

from psc.automata import (
    Dfa,
    cylinder,
    intersection,
    is_empty,
    minimised,
    project,
    union,
    widened,
    witness,
    Witness,
)
from psc.coincidence_formula import parikh_equality_automaton
from psc.dumont_thomas import letter_automaton, max_image_length, numeration_automaton
from psc.words import ALPHABET


comptime TRACKS = 2
comptime PATH_TRACK = 0
comptime OTHER_TRACK = 1


def _on_track(single: Dfa, track: Int, radix: Int) raises -> Dfa:
    """A one-track condition, placed on its track of the pair alphabet."""
    return cylinder(widened(single, radix), TRACKS, track, radix)


def reaching_one_letter(sigma: List[List[Int]], top: Int, bottom: Int) raises -> Dfa:
    """`or over letters a : end_top(P) = a and end_bottom(Q) = a`, built out of
    the Dumont-Thomas letter map and nothing else."""
    if top < 0 or top >= ALPHABET or bottom < 0 or bottom >= ALPHABET:
        raise Error("a coincidence pair is two letters of the substitution")
    var radix = max_image_length(sigma)
    var assembled = Dfa(radix * radix, List[Int](length=radix * radix, fill=0), [False])
    for letter in range(ALPHABET):
        var both = intersection(
            _on_track(letter_automaton(sigma, top, letter), PATH_TRACK, radix),
            _on_track(letter_automaton(sigma, bottom, letter), OTHER_TRACK, radix),
        )
        assembled = both.copy() if letter == 0 else union(assembled, both)
    return minimised(assembled)


def coincidence_by_elimination(
    sigma: List[List[Int]], top: Int, bottom: Int
) raises -> Dfa:
    """The formula above, assembled conjunct by conjunct and minimised.

    The admissibility conjuncts are applied before the Parikh relation, which is
    the largest automaton by far: the product is built before it is minimised,
    so intersecting the small conditions first is the difference between a
    product that closes and one that does not."""
    if top < 0 or top >= ALPHABET or bottom < 0 or bottom >= ALPHABET:
        raise Error("a coincidence pair is two letters of the substitution")
    var radix = max_image_length(sigma)
    var conditions = intersection(
        _on_track(numeration_automaton(sigma, top), PATH_TRACK, radix),
        _on_track(numeration_automaton(sigma, bottom), OTHER_TRACK, radix),
    )
    conditions = minimised(intersection(conditions, reaching_one_letter(sigma, top, bottom)))
    return minimised(
        intersection(conditions, parikh_equality_automaton(sigma, top, bottom))
    )


def eliminated_witness(
    sigma: List[List[Int]], top: Int, bottom: Int
) raises -> Witness:
    """The existential discharged: a shortest pair of paths satisfying the
    formula, or the fact that there is none."""
    return witness(coincidence_by_elimination(sigma, top, bottom))


def holds_by_elimination(
    sigma: List[List[Int]], top: Int, bottom: Int
) raises -> Bool:
    """`SC(top, bottom)`, decided by emptiness of the assembled language."""
    return not is_empty(coincidence_by_elimination(sigma, top, bottom))


def coincident_positions(
    sigma: List[List[Int]], top: Int, bottom: Int
) raises -> Dfa:
    """The paths in `sigma^k(top)` at which the pair coincides, with the other
    path quantified away by the subset construction.

    A formula's answer rather than a search's: a recognisable *set* of
    positions, not one witness. `project` is what makes it one, and this is the
    quantifier the bespoke automaton has no way to discharge."""
    return minimised(
        project(coincidence_by_elimination(sigma, top, bottom), TRACKS, OTHER_TRACK)
    )
