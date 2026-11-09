# Quantifier and transfer audit — 2026-11-09

**Status:** audit note for item (1) of the "Immediate sequence" of
[research-roadmap-2026-09-21.md](research-roadmap-2026-09-21.md) (2026-11-09
neglected-interface roadmap) and the "P0 QUANTIFIERS" and "P0 C4/G1
SEPARATION" items of the priority addendum of `README.llm.txt`. It is **not a
proof** of any open statement. It moves no governed claim status, adds no
ledger claim, and does not close or advance C4, G1, #84, #138, #139 or PSC.
The literature gate is
[quantifier-transfer-audit-stop-go-2026-11-09.md](quantifier-transfer-audit-stop-go-2026-11-09.md).

Source revision audited: branch `ccr-5059e568-lh2509` at `c5ed4e5`, which
contains `main` at `33a1f6b` (#523). Every statement about another file is a
reading of that file at that revision; receipts of other work are quoted as
the sources report them and were not replayed here unless §8 says so.

**Part I** (this revision) is the interface, its bindings and controls, and
the C4/G1 separation. **Part II**, the source-bound crosswalk of the
repository's bridges against the interface, is not in this revision.

## 1. The three readings

For a directed graph with states `S`, a child relation, a target set `T` and a
state `s`:

| Reading | Formula | In words |
| --- | --- | --- |
| (E) | `∃ t, s →* t ∧ t ∈ T` | some path from `s` reaches a target |
| (AE) | `∀ t, s →* t → ∃ u, t →* u ∧ u ∈ T` | every state reachable from `s` reaches a target |
| (AE°) | (AE) restricted to the `t` that lie on a cycle | every reachable cyclic state reaches a target |
| (A) | every infinite child path from `s` meets `T` | no admissible path avoids the targets |
| (A⁺) | (A), and no dead end is reached from `s` through non-targets | every maximal trajectory meets a target |

`proof/PscVerif/PscVerif/QuantifierInterface.lean` (namespace
`Psc.QuantifierInterface`) states them once, as `ChildGraph.Productive`,
`HereditarilyProductive`, `CyclicProductive`, `Inevitable` and `InevMax`, and
proves the following. A *dead end* is a non-target with no child; a *maximal
trajectory* is an infinite child path or a finite one ending at a state with no
child. Only `propext`, `Classical.choice` and `Quot.sound` are used.

| Statement | Lean name | Hypotheses |
| --- | --- | --- |
| (A) ⇒ (AE) | `Inevitable.hereditarilyProductive` | targets child-closed; every non-target has a child |
| (AE) ⇒ (AE°), (AE) ⇒ (E) | `HereditarilyProductive.cyclicProductive`, `.productive` | none |
| (E) transports backward along `→*`, (AE) forward | `productive_of_reach`, `HereditarilyProductive.of_reach` | none |
| (AE) ⇔ no strict closed set is reachable | `hereditarilyProductive_iff_no_strictClosed` | none (no finiteness) |
| not (AE) ⇒ a finite strict closed **strongly connected** set is reachable | `exists_strictComponent_of_finite` | reachable set finite |
| (AE) ⇔ no finite strict closed strongly connected set is reachable | `hereditarilyProductive_iff_exclusion_of_finite` | reachable set finite |
| (AE°) ⇒ (AE) | `hereditarilyProductive_of_cyclic_of_finite` | reachable set finite; every non-target has a child |
| (A) ⇔ no cycle of non-targets is reachable through non-targets | `inevitable_iff_no_strict_cycle_of_finite` | reachable set finite |
| path form of (A) ⇔ inductive form | `inevitable_iff_inev` | none (dependent choice) |
| (A⁺) ⇔ (A) ∧ no dead end reachable through non-targets | `inevMax_iff` | none |
| (A⁺) ⇔ no cycle of non-targets and no dead end is reachable through non-targets | `inevMax_iff_of_finite` | reachable set finite |
| (A⁺) ⇒ (AE) | `InevMax.hereditarilyProductive` | targets child-closed |
| two-obstruction skeleton: (`hB`) every reachable cyclic state has a `zero` descendant, (`hA`) every reachable `zero` state is productive ⇒ (AE) | `two_obstruction_skeleton` | reachable set finite; every non-target has a child |
| null strict mass ⇒ (AE) | `MassGraph.hereditarilyProductive_of_nullStrict` | mass positive and conserved at rate `θ > 0` |

A *strict closed set* is a nonempty, child-closed, target-free set
(`ChildGraph.StrictClosed`).

Minimal countermodels, each a Lean theorem in the same module:

| Invalid inference | Countermodel | States | Lean name |
| --- | --- | --- | --- |
| (E) ⇒ (AE); (E) transports forward | `fork` | 3 | `fork_not_hereditarilyProductive`, `productive_not_forward` |
| (AE) ⇒ (A) | `lasso` | 2 | `lasso_not_inevitable` |
| (A) ⇒ (E), at a dead end | `stub` | 1 | `stub_inevitable_not_productive` |
| "no closed strict component" ⇒ "no strict cycle" | `lasso` | 2 | `lasso_cycle_not_closed` |
| exclusion of finite closed strict components ⇒ (E), without finiteness | `ray` | ℕ | `ray_exclusion_vacuous` |
| (AE°) ⇒ (E), without finiteness | `ray` | ℕ | `ray_cyclicProductive_vacuous` |
| exclusion of finite closed strict components ⇒ (AE°), without finiteness | `loopRay` | ℕ + 1 | `loopRay_recurrent_not_closed` |
| (AE) ⇒ finite reachable set | `comb` | ℕ + 1 | `comb_productive_infinite` |
| `∀N ∃d` ⇒ `∃d ∀N` (uniform depth) | `chain N` | family | `chain_not_uniform` |
| agreement to bounded depth ⇒ same verdict | `chain N` vs `ray` | family | `chain_agrees_with_ray` |
| two-obstruction skeleton without `hA`; without `hB` | `fork` | 3 | `fork_without_A`, `fork_without_B` |
| null strict mass ⇒ (A); null ⇒ empty | `lassoMass` | 2 | `lassoMass_null_not_inevitable` |
| null strict mass ⇒ (AE), without conservation | `slow` | 3 | `slow_null_not_hereditarilyProductive` |

`inevMax_iff_of_finite` is item 2 of the "elementary finite-graph lemma" of
[c4-ordered-word-completion-interface-2026-11-02.md](c4-ordered-word-completion-interface-2026-11-02.md)
§3, which had no formal encoding: every maximal root-started trajectory hits
the target set iff no target-avoiding reachable part contains a cycle or a
non-target with no outgoing edge in the full graph. Item 1 of that lemma is
the definition of (E). The note's warning stands and is now two theorems apart:
a certificate of (E) for every root is not (A⁺) (`lasso`), and C4 does not ask
for (A⁺).

Minimality (an argument, not a Lean theorem). (AE) without (A) needs a
non-target on an infinite path and a target, so two states: `lasso` is minimal.
(E) without (AE) needs a target and a reachable non-productive state; when
targets are child-closed the root is neither, so three states: `fork` is
minimal among graphs with child-closed targets.

## 2. Binding to the repository's definitions

`proof/PscVerif/PscVerif/QuantifierBinding.lean` (namespace
`Psc.QuantifierBinding`) instantiates the interface on the balanced-pair
automaton of `def:bpa`: `bpaGraph s` has child relation
`Psc.Descendants.ChildNC s` (coincidence blocks terminal) and the coincidence
blocks as targets.

| Repository notion | Reading | Lean |
| --- | --- | --- |
| `Psc.StrictSystem.Productive s T` | (E) at `T` | `productive_iff` (`Iff.rfl`) |
| `Psc.StrictSystem.TerminatesWithCoincidence s T₀` | reachable set finite ∧ (AE) at `T₀` | `terminatesWithCoincidence_iff` (`Iff.rfl`) |
| `Psc.StrictSystem.StrictSystem s C` | a strict closed set | `strictClosed_of_strictSystem` |
| termination with coincidence | finite reachable set ∧ no reachable finite strict closed strongly connected set | `terminatesWithCoincidence_iff_finite_and_exclusion` |

Two literal controls, replayed independently in Mojo by
`kernel/tests/test_quantifier_controls.mojo`:

- **`fib_lasso`** (inside the standing class). Fibonacci `0 ↦ 01, 1 ↦ 0`, seed
  `(01, 10)`: the algorithm terminates with coincidence, so (AE) holds; the
  states `(01, 10)` and `(10, 01)` form a cycle of non-coincident states, so
  (A) fails. No interface that asks for "every admissible path meets a
  coincidence" can be satisfied inside the standing class.
- **`tm_fork`** (outside the standing class). Thue–Morse `0 ↦ 01, 1 ↦ 10`:
  the irreducible balanced pair `(001, 100)` has the children
  `(01, 10), (0, 0), (1, 1), (10, 01)`, so it is productive, and its child
  `(01, 10)` lies in the strict system `{(01, 10), (10, 01)}`. The incidence
  matrix is singular (`tm_incidence_singular`): the first violated standing
  premise is irreducibility. This is the control of
  `proof/psc_routes/R1ProductivityScope.lean` on the definitions of
  `Psc.Descendants`.

## 3. C4/G1 separation

**Statement.** For a substitution `σ` and a seed `T₀`, with `G = bpaGraph σ`:

```text
TerminatesWithCoincidence σ T₀
  ⇔  (F)  {U | T₀ →* U} is finite
   ∧  (X)  no finite strict closed strongly connected set is reachable from T₀
```

(`terminatesWithCoincidence_iff_finite_and_exclusion`.) The two conjuncts are
different kinds of statement and neither implies the other:

| Input | Kind | Governed status | What supplies it |
| --- | --- | --- | --- |
| (F) | extraction / termination (G1-type) | `G1`: open | families and finite domains as the ledger records; not the logic |
| (X) | component exclusion (C4-type) | `C4`: conditional on the open #138; `C4StandingCorpus`: finite-domain; `prob:C4`: open | C3-local for every strict component, through `prop:chain` |

- (X) without (F) gives nothing: in `ray` (X) holds vacuously and no state is
  productive (`ray_exclusion_vacuous`); in `loopRay` (X) holds vacuously and a
  recurrent strict strongly connected set has no productive state, so SCC
  Producer in the form (AE°) fails (`loopRay_recurrent_not_closed`).
- (AE°) without (F) gives nothing either: `ray` has no cycle
  (`ray_cyclicProductive_vacuous`).
- (AE) without (F) is not termination: `comb` (`comb_productive_infinite`).
- With (F), the three exclusion forms agree: (AE) ⇔ (X) ⇔ (AE°), the last
  using that every noncoincident state has a child.

**What C4 takes as input.** A *supplied* finite, strict, child-closed,
strongly connected set of balanced pairs with its full word factorization: in
Lean `Psc.StrictSystem.StrictComponent`, or `BpaStrictComponent` when it is a
component of `B_σ`. The existence of such a set, given a failure of
productivity, is the sink step `thm:sink` and needs (F):
`Psc.StrictSystem.exists_bpaStrictComponent_of_finite` carries `hfin`, and the
abstract form is `exists_strictComponent_of_finite`. The statements C3-local,
C2 and `Sync_±` themselves have no Lean form (no file under `proof/` mentions
them); `prop:chain` is a manuscript proof.

**Where the premise was dropped.** The manuscript (`prop:chain`: "with finite
`B_σ`"; `thm:sink`: conditional on G1), Lean and the generated ledger
(`SCCProducer` depends on `G1`, `SinkSCCReduction`, `C2`) keep (F). Three prose
surfaces printed the chain without it and carry a dated correction from this
revision: `docs/proof-ladder.md` ("The C4 chain"), `docs/conjecture-ledger.md`
(§E) and `docs/c4-finite-domain-closure-2026-11-05.md` (§1).

## 4. Null is not empty

`MassGraph` adds multiplicities, a mass `h` and an inflation factor `θ` to a
child graph; `strictMass n s` is the mass of the non-target descendants of `s`
at level `n`, with multiplicity, and `NullStrict s` says it is `o(θⁿ)`.

- **Valid.** If `h > 0` is conserved (`θ · h(s) = Σ h(children of s)`), null
  strict mass below `s` gives (AE): a reachable strict closed set would keep
  its whole mass `θⁿ h(t)` at every level (`strictMass_of_strictClosed`,
  `hereditarilyProductive_of_nullStrict`).
- **Not (A), and not emptiness.** In `lassoMass` the mass is positive and
  conserved, the strict mass below the non-target is one unit out of `2ⁿ` at
  every level, and an admissible path never meets the target
  (`lassoMass_null_not_inevitable`). Null strict mass is compatible with a
  nonempty strict set at every level and with a strict infinite path.
- **Nothing without conservation.** In `slow` the strict mass below the root
  is one unit against `2ⁿ`, the mass is positive, and a strict closed set is
  reachable (`slow_null_not_hereditarilyProductive`); conservation fails at the
  strict state, which has one child where `θ = 2`. Counting states, or
  potential overlaps, is not a conserved mass.

So a null-measure conclusion transfers to a combinatorial one only in the form
"no strict closed set carrying conserved positive mass", and never as
"the strict set is empty". This matches the source read for the literature
gate: in Akiyama–Lee the residual graph is nonempty in general, and what it
cannot contain is a real (positive-measure) overlap.

## 5. Finite at each parameter is not uniform

`chain N` (`0 → 1 → ⋯ → N`, targets `≥ N`) satisfies (A) with hitting time
exactly `N`. Hence `∀N ∃d` holds and `∃d ∀N` fails (`chain_not_uniform`), and
on the states below `N` the member `chain N` has the same children and targets
as `ray`, where no state is productive (`chain_agrees_with_ray`). A verdict
read from a finite set of specimens, or from an inspection to a fixed depth,
is a statement about those specimens and that depth.

## 6. Conditional theorem and antecedent

`two_obstruction_skeleton` is the graph logic of the proof of
`thm:two-obstruction-completion` (manuscript lines 147–166: a nonproductive
vertex of the finite graph leads to a nonproductive cyclic vertex; lemma B
gives it an offset-zero descendant; lemma A with `prop:aligned-overlaps` makes
that descendant productive). In the Lean statement both lemmas are hypotheses
`hA`, `hB`, and `fork_without_A`, `fork_without_B` show that the conclusion
fails when either is dropped. The theorem is the implication; it establishes
neither antecedent, and the governed nodes `UniversalAlignedCoincidence` and
`UniversalBoundaryHitting` are open.

**An imported antecedent the ledger did not name.** The ledger node `PDS`
(the finite-BPA route, `thm:main-conditional`) listed `G1` and `SCCProducer`
as its dependencies. The manuscript proof obtains termination with coincidence
from one swap seed and then applies the imported spectral bridge `thm:bridge`,
whose ledger node is `StandardBPAEquivalence`; no node depended on it. The
dependency models `MCLedgerG1AndProducer` and `MCLedgerG1AndC4` therefore
listed `PDS` as reachable while asserting `StandardBPAEquivalenceNotEstablished`.
The generator's own convention is that an imported theorem is established only
by assumption and a route names the import it needs (comment at
`OverlapGateAssumed` in `tools/make_ledger.py`). The record table now gives
`PDS` the dependency `StandardBPAEquivalence`, and the two models assume it.
No status changes: `PDS` stays conditional with the same open premises.

## 7. Corrections made in this revision

- The three dated corrections of §3.
- The ledger dependency of §6: `tools/make_ledger.py` (record `PDS`,
  assumption sets `G1AndProducer`, `G1AndC4`), the seven generated surfaces it
  rewrites, and one comment in `proof/tla/check.sh`.
- No governed status and no manuscript was changed.

## 8. Evidence and replay

```sh
cd proof/PscVerif && lake build PscVerif
lake env lean ProofBankAudit.lean        # axioms: propext, Classical.choice, Quot.sound
cd ../../kernel && pixi run --locked mojo run -I . -I tests tests/test_quantifier_controls.mojo
```

Replayed locally at this revision: the Lean build and axiom audit (4,249
declarations, 3,201 theorems), and the Mojo test, which passes; two mutated
copies of the Mojo test (a wrong nonproductive set, a wrong child order) fail.
For the ledger dependency of §6: `tools/make_ledger.py --check`,
`tests/test_ledger_generation.py`, and `proof/tla/check.sh` with
`tla2tools.jar` v1.8.0 (18 models pass; hosted CI fetches the latest release).
No hosted CI has run on this revision. Independent human review is pending.

The Mojo test is an independent replay of the two literal controls only. Its
states are pairs up to side swap, so the Lean two-cycle
`(01, 10) → (10, 01) → (01, 10)` is a self-loop there.

## 9. Non-claims

- Nothing here shows that a strict closed set exists or does not exist for any
  substitution in the standing class, that any balanced-pair automaton is
  finite beyond Fibonacci from the seed `(01, 10)`, or anything spectral.
- The abstract graphs are not substitutions. `ray`, `loopRay` and `comb` are
  not claimed to be realised by any substitution; whether an infinite
  balanced-pair automaton occurs in the standing class is the G1 question.
- `tm_fork` is outside the standing class and refutes an inference, not a
  theorem about primitive irreducible Pisot substitutions.
- The mass statements are finite algebra on a graph with multiplicities. They
  assert no geometric overlap cover and no measure on a tiling space.
