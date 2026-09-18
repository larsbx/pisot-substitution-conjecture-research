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
union, complement, the subset construction of Rabin and Scott[^1] discharging
one existential quantifier over a track of a product alphabet, emptiness with a
shortest witness, and Moore's partition refinement[^2] with language equality on
top of it. Both constructions are textbook and nothing about them is new here;
what they are for is the next paragraph.

`mojo/psc/dumont_thomas.mojo` — the Dumont–Thomas numeration[^3] of the fixed
point of a substitution, as an automaton: states are letters, the digit `j` moves from
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
mismatches. The tests pin the same three identities on the tribonacci
substitution[^11] and on a substitution prolongable only at a power. That is
finite evidence over an enumerated domain, and it is the whole of what is
established here.

### The addition automaton, built and checked

`mojo/psc/linear_numeration.mojo` — the numeration the substitution itself
carries: `U_k = |tau^k(c)|`, which obeys the characteristic recurrence of the
incidence matrix by Cayley–Hamilton, with greedy digits written against it. The
census below verifies that recurrence on every sampled specimen rather than
citing it.

`mojo/psc/numeration_addition.mojo` — the third automaton a decision procedure
needs, after admissibility and the letter map:

    { (x, y, z) : val(x) + val(y) = val(z) }

over digit triples. Reading most significant first, the running difference is
kept as a window vector over `(U_(j+2), U_(j+1), U_j)`, and the step is
`v <- (v1 - c2 v0, v2 - c1 v0, -c0 v0 + s)` with `s = x + y - z`. Unpruned that
exploration diverges, because the step is multiplication by the expanding root.
What makes it finite is the Pisot property applied as a reachability test: the
digits still to come can contribute only a bounded reserve, so a state past it
can never be completed to zero and is sent to a rejecting sink. The comparison
is exact — the state's value is a cubic element and `sign_at_perron` decides
its sign at the Perron root by Sturm–Tarski counting, with no float anywhere.

For the tribonacci substitution the construction gives 137 states, 44
minimised, over the eight triples of a binary alphabet; every one of the 3,600
sums below 60 is accepted and no near miss is.

`mojo/numeration_addition_census.mojo` carries that over the corpus, and keeps
three outcomes apart. Over 183 sampled specimens: 109 automata built and
verified, with 68,125 sums checked, zero false rejects and zero false accepts;
8 constructions refused at the state cap; 66 specimens skipped because their
digit alphabet would make the triple alphabet too large to be worth building.
The largest minimised automaton has 494 states.

A substitution made prolongable by a power can have images longer than three,
which is the domain `build_perron_field3` states it is certified on — that
entry point serves the overlap kernel's legacy unchecked predicates, and it
refuses outside it, correctly. Such a specimen is still eligible for this
numeration, so the field is built here from the powered matrix's own
characteristic polynomial, screened by the same exact coefficient tests the
corpus screen uses: rational roots for irreducibility, Sturm counting for the
Pisot property. 67 of the sampled specimens are past that domain, and the
census reports how many of them built, so a run says whether it exercised the
case at all rather than leaving it to inference.

A refusal at the cap is a statement about this exploration's bound, not about
the specimen: the imported theorem says a finite state set exists for a Pisot
basis, and not finding one inside the cap is a refusal, never a negative.

### The two numerations are not one presentation

The greedy digits against `U` and the Dumont–Thomas path digits coincide for
some substitutions and not for others: a path digit weighs a child block, whose
length depends on the letters along the path, and a greedy digit weighs `U_j`
alone. Over the sampled corpus they agree for 1 specimen and differ for 22.
`agrees_with_path_digits` decides it per substitution, and the tests carry one
example of each. This matters for the route: the letter map of
`psc.dumont_thomas` is indexed by path digits, and addition is recognised over
greedy digits, so a formula quantifying over both needs the conversion. That is
a fourth automaton, and it is the next section.

### The conversion, and the letter map moved across it

`mojo/psc/numeration_conversion.mojo` builds

    C = { (P, G) : P an admissible path word from `c`, |G| = |P|,
                   val_path(P) = val_greedy(G) }

as a synchronous two-track automaton, and then uses it to carry the letter map
into the numeration where addition is recognised.

The state is three integers and one letter. The length vector satisfies
`L_(m+1) = M^T L_m` — one substitution step is one level of it — so the running
difference, kept as a coefficient vector against the *current* level, steps by
the integer matrix `x <- M x + s`, and `L_0 = (1, 1, 1)` makes acceptance the
statement that the coordinates of `x` sum to zero. That identity is what keeps
the state small: a window of three levels across three letters would be nine
coefficients for a value with three degrees of freedom, the same difference
would be reached in representations the exploration cannot identify, and it
diverges rather than closing. Measured, not argued: at nine coefficients the
tribonacci conversion closes at 3,182 states and `0 -> 011, 1 -> 02, 2 -> 0`
was still opening new ones past 400,000.

Pruning is the same Pisot reachability test as for addition, with one
difference that matters. The three letters' weights are not commensurable:
`L_m(b)` grows like `v_b beta^m` with `v` the left Perron eigenvector, whose
entries lie in `Z[beta]` and differ between letters. So the value is the cubic
element `sum_b x[b] v_b` over the eigenvector `perron_tile_lengths_in`
constructs and verifies in the same field, and `sign_at_perron` decides the
comparison. The reserve's `1/(beta - 1)` is cleared by multiplying through by
`beta - 1`, which is positive, so no division and no float enters.

The bound is drawn wider than the computation asks, because the ratios it is
computed from are limiting ones applied at finite levels. How much wider is
measured on both sides rather than asserted: at the narrowest factor the
computation suggests, the language of the `0 -> 011` specimen changes; from one
step wider it stops changing, and widening further only adds states that
minimisation merges back. `conversion_automaton_with` exposes the factor so the
regression can check exactly that.

`greedy_letter_automaton` is then the object the route wanted: place the
Dumont–Thomas letter map on the path track, discharge the path by the subset
construction, and what is left is a condition on the digit word alone. The
letter map and addition now speak one numeration.

`mojo/numeration_conversion_census.mojo` carries this over the corpus with the
same three outcomes kept apart. Over 183 sampled specimens: 115 conversions
built, 4,600 position pairs checked with zero false rejects and zero false
accepts; 1 construction refused at the state cap; 67 skipped for their digit
alphabet. The letter map was carried across for 88 of them — the projection
costs the conversion's size squared, so 27 conversions were too large to
attempt, which is not the same as failing — and all 10,560 transferred letter
verdicts agree with reading the fixed point. The largest minimised conversion
has 1,421 states and the largest transferred letter map 198.

What it does *not* do: `C` relates a path word to any digit word of the same
length with the same value, not only to the greedy one. Greedy-normality is a
separate language — a lexicographic condition against the expansion of one —
and it is not built, so the transferred letter map accepts every
representation of such a position. For a decision procedure that is the useful
side of the choice, since normalisation is its own automaton there too; it is
still a thing that has to be said rather than left to inference.

## What must be imported

**Recognisability of addition, in general.** The automaton above is built and
checked per specimen on a bounded domain. That a finite one exists for every
Pisot basis, and that the construction terminates for all of them rather than
for the fourteen it happened to terminate for, is Frougny's theorem,[^4] with the finiteness
side studied by Frougny and Solomyak,[^5] and the logical framework that turns
recognisability into decidability of a first-order theory is Bruyère, Hansel,
Michaux and Villemaire,[^6] extended to linear numeration systems of this kind
by Bruyère and Hansel.[^7] Nothing in this repository proves any of it, and the
automata layer above does not need it — but the step from "recognisable set" to
"decision procedure" does, and any claim of the form "decided for every
substitution in the family" rests on it.

**Walnut as an engine.** Walnut[^8] decides such statements for automatic
sequences once the numeration's automata are supplied; Shallit's monograph[^9]
is both the reference and the practical account of what the decision procedure
can and cannot reach. Using it would mean generating the addition automaton for
each cubic Pisot base, which is the same import in executable form.

**The formula itself.** Strong coincidence, in the sense this repository uses
it,[^10] is stated here as a property of balanced pairs and of the overlap
graph. Writing it as a first-order formula
over positions of the fixed point — with the quantifiers a decision procedure
can eliminate — is mathematics this gate does not do, and the encoding would
have to be checked against the verdicts the existing census reports before
anything is concluded from it.

## Decision

**Proceed, with the claim narrowed to constructions checked on bounded
domains.** What is claimed now: the Dumont–Thomas numeration presents the fixed
point exactly; the automata operations implementing a decision procedure are
correct on their own terms; the linear numeration round-trips its greedy
digits; the addition automaton, where it was built, is the addition relation on
the range tested; and the conversion, where it was built, pairs each position's
path word with that position's digit word and with no other on the range
tested, carrying the letter map across unchanged. No claim is made that any coincidence condition
has been decided, for one substitution or for a family, and none that the
construction terminates for every specimen — eight refusals say otherwise on
this corpus sample and this cap.

Four automata now exist for a specimen that builds: admissibility, the letter
map, addition, and the conversion that puts the first two into the numeration
the third is recognised over. What remains is the formula — the coincidence
condition written with quantifiers a decision procedure can eliminate — and,
for a claim about digits rather than about values, the greedy-normal language
that would make the conversion functional. Its acceptance test is unchanged:
agreement with the verdicts the degree-3 census already reports on a family it
already covers. Disagreement there is a bug in the encoding, never a new
result.

## Sources

No PDF snapshots were imported for this review, so there is nothing under
`docs/source-imports/` to cite. The entries below are bibliographic references
to standard literature, not verified snapshots: they were written without access
to the published record, so volume, year and page details must be checked
against it when each is pinned, and no ledger may cite one until that is done.
The mathematical attributions are what the gate depends on; the numbers are
convenience.

[^1]: Michael O. Rabin and Dana Scott, "Finite automata and their decision problems," *IBM Journal of Research and Development* 3 (1959), 114–125. The subset construction, which `project` uses to determinise after dropping a track.
[^2]: Edward F. Moore, "Gedanken-experiments on sequential machines," in *Automata Studies*, Annals of Mathematics Studies 34, Princeton University Press, 1956, 129–153. Partition refinement, which `minimised` implements.
[^3]: Jean-Marie Dumont and Alain Thomas, "Systèmes de numération et fonctions fractales relatifs aux substitutions," *Theoretical Computer Science* 65 (1989), 153–169. The numeration this repository implements, and the prefix-path decomposition it is read from.
[^4]: Christiane Frougny, "Representations of numbers and finite automata," *Mathematical Systems Theory* 25 (1992), 37–60. Normalisation, and recognisability of addition, in a Pisot numeration system.
[^5]: Christiane Frougny and Boris Solomyak, "Finite beta-expansions," *Ergodic Theory and Dynamical Systems* 12 (1992), 713–723. The finiteness property of beta-expansions, which the same parameters govern.
[^6]: Véronique Bruyère, Georges Hansel, Christian Michaux and Roger Villemaire, "Logic and p-recognizable sets of integers," *Bulletin of the Belgian Mathematical Society — Simon Stevin* 1 (1994), 191–238, with a corrigendum in the same volume. Recognisable sets as the models of a first-order theory: the step this gate does not take.
[^7]: Véronique Bruyère and Georges Hansel, "Bertrand numeration systems and recognizability," *Theoretical Computer Science* 181 (1997), 17–43. The extension to linear numeration systems attached to a Pisot base.
[^8]: Hamoon Mousavi, "Automatic theorem proving in Walnut," arXiv:1603.06017, 2016. The tool, and the shape of the formulas it accepts.
[^9]: Jeffrey Shallit, *The Logical Approach to Automatic Sequences: Exploring Combinatorics on Words with Walnut*, London Mathematical Society Lecture Note Series 482, Cambridge University Press, 2022.
[^10]: Pierre Arnoux and Shunji Ito, "Pisot substitutions and Rauzy fractals," *Bulletin of the Belgian Mathematical Society — Simon Stevin* 8 (2001), 181–207. Strong coincidence as this repository uses it.
[^11]: Gérard Rauzy, "Nombres algébriques et substitutions," *Bulletin de la Société Mathématique de France* 110 (1982), 147–178. The substitution whose numeration the tests pin, and the origin of the geometric picture behind the conjecture.

## Non-claims

This gate decides nothing about the Pisot substitution conjecture, about
`OverlapProductivity`, or about any specimen's coincidence. The census it
describes is a bounded experiment on its own stated scope. A decision procedure
does not exist here until the formula is written, the addition automaton is
supplied or imported, and the encoding agrees with the census on a family the
census already covers.
