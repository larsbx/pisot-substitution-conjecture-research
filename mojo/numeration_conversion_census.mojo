"""Conversion automata over the corpus, each verified on a bounded domain.

For every sampled specimen: build the automaton relating Dumont-Thomas path
words to digit words of the linear numeration, and check it against the
positions it claims to relate. Every position below the bound must pair with
its own digit word and with no nearby other; where the conversion is small
enough to carry the letter map across, the transferred map must answer exactly
as reading the fixed point does.

The same three outcomes are kept apart as in the addition census. A built and
verified conversion is finite evidence about that specimen. A construction past
the state cap is a refusal, not a negative: the imported theorem says a finite
state set exists, and this exploration did not find one inside the cap. A
specimen skipped -- for a digit alphabet larger than the cap, or for a
conversion too large to project through -- was never attempted, and the two
reasons are counted apart because they say different things.

This driver catches nothing. A refusal arrives as a flag on the result;
anything that raises aborts the census rather than being counted as an
inconclusive specimen.

Nothing here decides a coincidence condition or moves a ledger entry
(`docs/automatic-sequence-route-literature-gate-2026-09-17.md`).
"""

from psc.automata import minimised
from psc.corpus import pip_corpus, report_progress
from psc.dumont_thomas import digits, letter_at, max_image_length, prolongable_form
from psc.histogram import Histogram, max_int
from psc.linear_numeration import (
    basis_obeys_recurrence,
    greedy_digits,
    longest_basis,
    max_greedy_digit,
)
from psc.numeration_conversion import (
    conversion_automaton,
    letter_in_conversion,
    pair_word,
)
from psc.oa_overlap_types import prolongable_point

comptime STRIDE = 25
comptime RADIX_CAP = 4
comptime STATE_CAP = 20000
comptime POSITION_BOUND = 40
comptime NEAR_MISSES = 3
comptime PROJECTABLE = 200


def main() raises:
    var corpus = pip_corpus()
    var sampled = 0
    var built = 0
    var refused = 0
    var skipped_alphabet = 0
    var recurrence_failures = 0
    var pairs_checked = 0
    var false_rejects = 0
    var false_accepts = 0
    var largest = 0
    var projected = 0
    var too_large_to_project = 0
    var letters_checked = 0
    var letter_mismatches = 0
    var largest_letter_map = 0
    var radices = Histogram(32)

    for s in range(0, len(corpus), STRIDE):
        ref spec = corpus[s]
        sampled += 1
        var point = prolongable_point(spec.sigma)
        var tau = prolongable_form(spec.sigma)
        var u = longest_basis(tau, point.letter, 20)
        if not basis_obeys_recurrence(tau, point.letter, 20):
            recurrence_failures += 1
            print("RECURRENCE MISMATCH", spec.label())
            continue

        var radix = max_int(max_greedy_digit(u, 200) + 1, max_image_length(tau))
        radices.record(radix)
        if radix > RADIX_CAP:
            skipped_alphabet += 1
            continue
        var result = conversion_automaton(tau, point.letter, radix, STATE_CAP)
        if not result.accepted():
            refused += 1
            report_progress(s, len(corpus))
            continue
        built += 1
        var conversion = result.automaton.copy()
        var small = minimised(conversion)
        largest = max_int(largest, small.states())

        for n in range(POSITION_BOUND):
            pairs_checked += 1
            var path = digits(tau, point.letter, n)
            if not conversion.accepts(pair_word(radix, path, greedy_digits(u, n))):
                false_rejects += 1
                print("FALSE REJECT", spec.label(), n)
            for offset in range(1, NEAR_MISSES + 1):
                var other = pair_word(radix, path, greedy_digits(u, n + offset))
                if conversion.accepts(other):
                    false_accepts += 1
                    print("FALSE ACCEPT", spec.label(), n, "against", n + offset)

        # Carrying the letter map across is a subset construction over the
        # product, so its cost is the conversion's size squared: a large
        # conversion is not attempted, and saying so is not the same as saying
        # it failed.
        if small.states() > PROJECTABLE:
            too_large_to_project += 1
            report_progress(s, len(corpus))
            continue
        projected += 1
        for target in range(3):
            var map = letter_in_conversion(conversion, tau, point.letter, target, radix)
            largest_letter_map = max_int(largest_letter_map, map.states())
            for n in range(POSITION_BOUND):
                letters_checked += 1
                if map.accepts(greedy_digits(u, n)) != (
                    letter_at(tau, point.letter, n) == target
                ):
                    letter_mismatches += 1
                    print("LETTER MISMATCH", spec.label(), target, n)
        report_progress(s, len(corpus))

    print("corpus:", len(corpus), " stride:", STRIDE, " sampled:", sampled)
    print("basis recurrence mismatches:", recurrence_failures)
    print("conversions built:", built, " refused at the cap:", refused,
          " skipped for alphabet:", skipped_alphabet)
    print("pairs checked:", pairs_checked, " false rejects:", false_rejects,
          " false accepts:", false_accepts)
    print("letter maps carried across:", projected,
          " conversions too large to project:", too_large_to_project)
    print("letter verdicts checked:", letters_checked,
          " mismatches:", letter_mismatches)
    print("largest minimised conversion:", largest,
          " largest letter map:", largest_letter_map)
    print(radices.line("specimens by pair-alphabet radix"))
