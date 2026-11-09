# Quantifier and transfer audit: literature stop/go gate — 2026-11-09

**Status:** stop/go note (AGENTS.md "Targeted literature stop/go check") for the
first item of the 2026-11-09 priority addendum of `README.llm.txt`
("P0 QUANTIFIERS") and the part of "P0 C4/G1 SEPARATION" that is graph logic.
It moves no governed claim status and adds no ledger claim. The audit itself is
[quantifier-transfer-audit-2026-11-09.md](quantifier-transfer-audit-2026-11-09.md).

## 0. Decision

**Proceed, narrowed.** The three quantifier readings below, their implications
and their separating examples are textbook temporal logic and textbook Markov
chain theory; the reading that the spectral criteria use is fixed in the
substitution literature. Nothing in the logic is new. The work is restricted to

1. a typed Lean interface that states the three readings once, with the valid
   implications and minimal countermodels, so that a repository statement can
   be bound to exactly one of them;
2. bindings of that interface to definitions the repository already has
   (`Psc.StrictSystem.Productive`, `TerminatesWithCoincidence`, `StrictSystem`);
3. a source-bound crosswalk of the repository's bridges against the interface.

No census, no new corpus computation and no new theorem-facing diagnostic on the
standing corpus is licensed by this note.

## 1. The proposed claim

For a directed graph with states `S`, a child relation and a target set `T`
(coincidences), and a state `s`:

| Reading | Formula | Temporal logic |
| --- | --- | --- |
| (E) | `∃ t, s →* t ∧ t ∈ T` | `EF T` |
| (AE) | `∀ t, s →* t → ∃ u, t →* u ∧ u ∈ T` | `AG EF T` |
| (A) | every infinite child path from `s` meets `T` | `AF T` |

Proposed statements, all graph logic:

- (A) ⇒ (AE) ⇒ (E), the first when `T` is child-closed and every non-target
  has a child; neither converse holds.
- (AE) ⇔ no nonempty child-closed `T`-free set is reachable from `s`.
- If the set reachable from `s` is finite: (AE) ⇔ no child-closed strongly
  connected `T`-free set is reachable; (A) ⇔ no `T`-free cycle is reachable
  through non-targets. Finiteness cannot be dropped from the first.
- With a positive mass conserved at the inflation rate `θ`, strict mass
  `o(θⁿ)` below `s` gives (AE). It does not give (A), and it gives nothing
  without conservation.
- A family in which every member satisfies (A) need not have a uniform hitting
  depth, and a bounded-depth inspection does not separate such a member from a
  graph with no productive state.

## 2. Prior art

Sources marked *read* were fetched and read for this note on 2026-11-09; the
quotations are from the fetched text. Sources marked *not re-read* are cited
from general knowledge and carry no weight in the decision.

1. **J.-P. Katoen, *Modeling and Verification of Probabilistic Systems*,
   lecture of 2018-10-22, RWTH Aachen** (*read*; the material of
   Baier–Katoen, *Principles of Model Checking*, ch. 10, whose theorem numbers
   were not checked).
   - "For finite DTMCs, qualitative properties do only depend on their state
     graph and not on the transition probabilities! For infinite DTMCs, this
     does not hold."
   - Long run theorem: almost surely a finite DTMC reaches a bottom strongly
     connected component and visits all its states infinitely often.
   - Almost sure reachability theorem: for a finite DTMC and a set `G` of
     absorbing states, `Pr(s ⊨ ◇G) = 1` iff `s ∉ Pre*(S ∖ Pre*(G))`.

   The last statement is "probability one ⇔ (AE)". The bottom strongly connected
   components are the closed strongly connected sets of §1.
2. **B. F. Martensen, *A generalized balanced pair algorithm*,
   arXiv:math/0309194** (*read*).
   - Termination: "If `I(w)` is finite, then we say that the balanced pair
     algorithm associated to a prefix `w` … terminates."
   - "We say that a balanced pair … leads to a coincidence if there exists `m`
     such that the reduction of [its `m`-th inflation] contains a coincidence.
     Notice that coincidences lead to coincidences".
   - Theorem 3.10(a): if `bpa(w, L)` terminates "and every equivalent pair in
     `I(w, L)` leads to a coincidence", the system has pure discrete spectrum;
     (b) is the converse for a suitable prefix.

   The spectral criterion is therefore "finite and (AE)", with the quantifier
   over *every* pair of `I(w, L)`.
3. **S. Akiyama, J.-Y. Lee, *Algorithm for determining pure pointedness of
   self-affine tilings*, arXiv:1003.2898** (*read*).
   - Definition 2.4: overlap coincidence is "there exists `ℓ` such that for each
     overlap `O` in `T`, `Φ^ℓ O` contains a coincidence" (`∃ℓ ∀O`).
   - Theorem 3.4: under the Meyer hypothesis the pointwise form `∀O ∃ℓ(O)`
     suffices; the proof passes through the density estimate of Lemma 3.3, and
     the proof of Theorem 4.1 uses that "there are only finitely many overlaps
     up to translations".
   - Lemma 3.3: `lim dens(D_{Qⁿα}) = 1` ⇔ `1 − dens ≤ b rⁿ` ⇔ `∃ℓ ∀O`.
   - Theorem 4.1: overlap coincidence ⇔ `ρ(G_coin) > ρ(G_res)`, where `G_res`
     is induced on the potential overlaps with no path to a coincidence. In the
     proof: "`G_res` cannot contain any real overlap" (each real overlap grows
     at the full rate `βⁿ`), whereas boundary-touching potential overlaps
     "[give] infinite walks on the graph".

   So in the source the residual graph is in general **nonempty** and of smaller
   growth rate; what is excluded from it is the positive-measure (real)
   overlaps, and the exclusion uses that a real overlap carries mass at the
   Perron rate.
4. **V. F. Sirvent, B. Solomyak, *Pure discrete spectrum for one-dimensional
   substitution systems of Pisot type*, Canad. Math. Bull. 45 (2002)**
   (*not re-read*; abstract only): the non-constant-length balanced pair
   algorithm of Livshits as a pure-discrete-spectrum test.
5. **CTL**: E. M. Clarke, E. A. Emerson (1981); E. A. Emerson, J. Y. Halpern,
   *"Sometimes" and "not never" revisited* (1986) (*not re-read*): the operators
   `EF`, `AF`, `AG` and their separation.

## 3. Hypotheses that transfer, and those that do not

| Fact | Transfers to the standing regime? |
| --- | --- |
| probability one ⇔ (AE), finite graph | Yes, **given** a finite graph. Finiteness of the balanced-pair automaton is G1-type input and is not supplied by the logic. |
| "qualitative properties depend only on the graph" | No for an infinite graph (source 1); `ray` in the Lean module. |
| `∀O ∃ℓ` ⇔ `∃ℓ ∀O` | Only with finitely many states (source 3). The quantifier swap fails across a family (`chain N`). |
| null residual ⇒ no strict closed set | Only for a positive mass conserved at the Perron rate (source 3, "real overlap"). Counts of potential overlaps do not qualify (`slow`). |
| (AE) ⇒ (A) | Never, already for Fibonacci (`fib_lasso`). |

Sources 2 and 3 do not assume a unit Pisot root; source 3 states that its
method covers non-unit cases. No unimodularity is used anywhere in this note or
in the Lean modules.

## 4. Known negative controls

- Repository: `proof/psc_routes/R1ProductivityScope.lean` (Thue–Morse
  `0 ↦ 01, 1 ↦ 10`, root `(001, 100)`: a productive parent with a strict
  closed child class; singular incidence matrix, outside the standing class).
- Literature: source 3 (examples after Theorem 4.1) reports two substitutions
  whose suspension tilings "do not give overlap coincidence":
  `0 ↦ 03, 1 ↦ 0, 2 ↦ 21, 3 ↦ 2` (attributed there to B. Sing) and
  `0 ↦ 051000, 1 ↦ 324100, 2 ↦ 24100, 3 ↦ 324333, 4 ↦ 051433, 5 ↦ 51433`
  (attributed there to its reference [7], Ex. 5.3). Both are primitive with a
  reducible characteristic polynomial, computed for this note:
  `(x² − x − 1)(x² − x + 1)`, eigenvalue moduli `1.618, 1, 1, 0.618`; and
  `(x − 1)²(x² − 6x + 1)(x² − 4x + 1)`, moduli `5.83, 3.73, 1, 1, 0.27, 0.17`.
  Their first violated standing premise is irreducibility. Neither is used
  here; they are recorded in the side-notes ledger as literature-settled
  specimens.
- New, abstract: `fork`, `lasso`, `ray`, `chain`, `lassoMass`, `slow` in
  `proof/PscVerif/PscVerif/QuantifierInterface.lean`; new, literal:
  `fib_lasso`, `tm_fork` in `QuantifierBinding.lean`.

## 5. Non-claims

This note and the modules it licenses prove nothing about the existence or
non-existence of a strict closed set, about finiteness of any balanced-pair
automaton, or about the spectrum of any substitution. They do not close or
advance C4, G1, #84, #138, #139 or PSC.
