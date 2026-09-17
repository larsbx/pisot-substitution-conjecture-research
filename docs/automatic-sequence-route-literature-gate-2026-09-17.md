# Literature gate — deciding coincidence by automata over a numeration system

## Proposed step

Replace a census over an enumerated corpus with a decision procedure. The census
answers "no counterexample among these 4,554 specimens"; a decision procedure
would answer "true of every substitution in this family", by expressing the
condition as a first-order formula over a numeration system attached to the
substitution and deciding it with automata.

The route has three parts, and this gate separates what the repository now has
from what it would have to import.

## What is built here, and checked

`mojo/psc/automata.mojo` — deterministic automata over an integer alphabet with
total transitions, and the operations a decision procedure needs: intersection,
union, complement, the subset construction that discharges one existential
quantifier over a track of a product alphabet, emptiness with a shortest
witness, and Moore minimisation with language equality on top of it.

`mojo/psc/dumont_thomas.mojo` — the Dumont–Thomas numeration of the fixed point
of a substitution, as an automaton: states are letters, the digit `j` moves from
`a` to the `j`-th letter of `tau(a)`, a digit past the end of an image is
inadmissible, and the letter reached after the last digit is `u_n`. The fixed
point is therefore a letter-valued output of a finite automaton reading these
digits, and the positions carrying a given letter form a recognisable set.

`mojo/automatic_route_census.mojo` — three identities per specimen, between
computations that share no step:

| Identity | One side | The other side |
| --- | --- | --- |
| letters | the automaton's output at position `n` | the fixed-point prefix, by substituting |
| positions | admissible digit words of length `k` | `|tau^k(c)|`, by substituting |
| occurrences | digit words ending at a letter | an entry of `M^k`, the incidence matrix power |

Over every twentieth specimen — 228 specimens, prolongable powers 1 to 3, digit
radices 2 to 26 — 68,400 letter positions and every count agree, with zero
mismatches. That is finite evidence over an enumerated domain, and it is the
whole of what is established here.

## What must be imported

**Recognisability of addition.** A first-order formula over the numeration is
decidable by automata only when addition is recognisable in it: the set of
triples of representations with `x + y = z` must be accepted by a finite
automaton. For a Pisot base this is a theorem of Frougny, with Bruyère and
Hansel supplying the logical framework that turns it into decidability of the
first-order theory. Nothing in this repository proves it, and the automata layer
above does not need it — but the step from "recognisable set" to "decision
procedure" does, and any claim of the form "decided for every substitution in
the family" rests on it.

**Walnut as an engine.** Shallit's Walnut decides such statements for automatic
sequences given the numeration's automata. Using it would mean generating the
addition automaton for each cubic Pisot base, which is the same import in
executable form.

**The formula itself.** Strong coincidence is stated here as a property of
balanced pairs and of the overlap graph. Writing it as a first-order formula
over positions of the fixed point — with the quantifiers a decision procedure
can eliminate — is mathematics this gate does not do, and the encoding would
have to be checked against the verdicts the existing census reports before
anything is concluded from it.

## Decision

**Proceed, with the claim narrowed to a presentation.** What is claimed now is
that the Dumont–Thomas numeration presents the fixed point exactly, and that the
automata operations implementing a decision procedure are correct on their own
terms. No claim is made that any coincidence condition has been decided, for one
substitution or for a family.

The next step is the encoding, and its acceptance test is agreement with the
verdicts the degree-3 census already reports on a family it already covers.
Disagreement there is a bug in the encoding, never a new result.

## Sources

No PDF snapshots were imported for this review, so there is nothing under
`docs/source-imports/` to cite. These are bibliographic references, not verified
snapshots, and each must be pinned before any ledger uses it:

- J.-M. Dumont and A. Thomas, on numeration systems attached to substitutions,
  for the representation this module implements.
- C. Frougny, on recognisability of addition in a Pisot numeration system.
- V. Bruyère and G. Hansel, with C. Michaux and R. Villemaire, on the logical
  framework making such numerations decidable.
- J. Shallit, *The Logical Approach to Automatic Sequences*, for Walnut and the
  decision procedure in practice.
- P. Arnoux and S. Ito, for strong coincidence as it is used in this repository.

## Non-claims

This gate decides nothing about the Pisot substitution conjecture, about
`OverlapProductivity`, or about any specimen's coincidence. The census it
describes is a bounded experiment on its own stated scope. A decision procedure
does not exist here until the formula is written, the addition automaton is
supplied or imported, and the encoding agrees with the census on a family the
census already covers.
