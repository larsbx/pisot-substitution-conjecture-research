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

**Part I** (sections 1 to 9) is the interface, its bindings and controls, and
the C4/G1 separation. **Part II** (sections 10 onward) is the source-bound
crosswalk of the repository's bridges against the interface, cited at `2201a5b`.
It was produced from six read-only route maps at `c5ed4e5` (their readers
executed nothing), a per-hazard synthesis and an adversarial re-check of every
locator; §19 states its limits.

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

## 10. Part II: the reading of each load-bearing statement

Part II reads branch `ccr-5059e568-lh2509` at `2201a5b`, which contains
`e7853fb` and `main` at `33a1f6b`; every line number below is of that tree.
`QuantifierInterface.lean` and `QuantifierBinding.lean` did not change between
`4a22b96` and `2201a5b`. Abbreviations: **ms** =
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`; **QI**, **QB**, **SS** =
`proof/PscVerif/PscVerif/{QuantifierInterface,QuantifierBinding,StrictSystem}.lean`;
**ML** = `tools/make_ledger.py`; **CG** = `claim_governance.toml`. A bare `.md`
name is under `docs/`, a bare `R1*.lean` name under `proof/psc_routes/`, any
other bare `.lean` name under `proof/PscVerif/PscVerif/`, a bare `test_*.mojo`
name under `kernel/tests/`. 𝒪_σ is the seed-patch overlap graph (ms L536,
L857), B_σ the balanced-pair automaton (`def:bpa`, ms L291). Status words are
those of CG (read with `tomllib`) or of `docs/ledger-index.md`. "Root" says
where a reading is anchored.

| Statement | Locator | Reading | Exact; abbreviated at |
| --- | --- | --- | --- |
| productive state; termination with coincidence | ms L291; `Productive`, `TerminatesWithCoincidence` (SS L602-610) | (E) on B_σ with target a coincidence block; (F) ∧ (AE) from one seed | exact; "terminates" means (F) only at ms L567, L903 and `BPrime.lean` L22-23 |
| `thm:bridge` (Imported) | ms L318, L321 | ∃ one seed with (F) ∧ (AE) ⇒ PDS of the flow; "We use only the forward implication stated" | exact; its ledger node is named `StandardBPAEquivalence` (ML L230, status imported) without saying which direction |
| `conj:producer` (Open); `SCCProducer` (open) | ms L310; ML L222-223 | (AE°) on B_σ, every seed; no (F) in the statement | exact; the record encodes only the route through G1 |
| `thm:sink` (Conditional on G1) | ms L589; `exists_bpaStrictComponent_of_not_terminates`, SS L2606-2610 | (F) ∧ ¬(AE) ⇒ a closed nonproductive recurrent noncoincident SCC | exact; the Lean conclusion does not record that the component is reachable from T₀ |
| `prop:chain` | ms L646 | per supplied component: C3-local ⇒ C2 ⇒ contradiction; the passage to SCC Producer is "with finite B_σ" | exact |
| `prob:C4` (Open); C4 interface | ms L836; `c4-ordered-word-completion-interface-2026-11-02.md` L63-66 | ∀σ ∀ supplied finite strict component C ∃ T ∈ C ∃ one-step interior zero return with a Sync₊ or Sync₋ neighbour | exact; "uniformly in" the size of C has no constant to be uniform: read "for every C of every size" |
| lemma A, #138; `UniversalAlignedCoincidence` (open) | ms L129-130; ML L142 | ∀ pairs of distinct letters ∃ level | exact; A1′ has three written forms (ms L1119; `p1a-template-collapse-2026-10-05.md` L93-95; ms L171-173) and a fixed-word form with h a letter (`c4-cut-attractor-window-2026-11-05.md` L259-261) |
| Theorem A(4); `C4FromStrongCoincidence` (proved) | `c4-cut-pair-productivity-2026-11-04.md` L64; `not_witness`, SS L518 | ∀ cut pairs of a strict system: no left strong-coincidence witness | exact; the record (ML L215) says "has a first-letter pair", an existential |
| `cor:scc-reduction`(i) (Theorem) | ms L972 | lemma A ⇒ (E) at every noncoincident state of B_σ, no (F); (F) re-enters only for PDS | exact |
| `thm:BD` (Imported); `thm:BD-eliminator` (Theorem, d = 3) | ms L688-690; L692-697 | ∃ one eventually coincident pair; the eliminator covers every closed nonproductive set, finite or not | exact |
| `prob:overlap-productivity` (Open Problem 5.35) | ms L900-901 | all-vertex (AE) on 𝒪_σ ⇔ (X) on 𝒪_σ, where (F) is `thm:overlap-finite` | exact; the alias "Open Problem 5.35" sits on the one-seed node `OverlapProductivity` (CG L1648) |
| #84; `OverlapProductivity` (open) | ML L119; `README.md` L33; `thm:main-density`, ms L923 | ∀σ ∃ a ≠ b: (AE) on 𝒪_σ rooted at the seed overlaps of (ab, ba); one seed ⇔ every seed only through PDS (Theorem SC, `p1-seed-strength-2026-10-08.md` L66-97, review-pending imports) | exact there; (E)-shaped at `README.llm.txt` L93, ms L150-151, `direct-attack-frontier-2026-10-23.md` L39; `kernel/psc/class_a_boundary_w_children.mojo` L3 calls one selected path (E) "one-seed productivity" |
| `thm:density` (ii)-(v) (Theorem) | ms L863-866 | (ii) (E) ⇔ δ(T) > 0; (iii) (AE) on 𝒪_σ from s ⇔ δ(s) = 1; (iv) δ(s) = 1 ⇒ (AE) on B_σ from s, no (F); (v) with (F): δ(s) = 1 ⇔ termination from s | exact |
| `AllStatesProductiveViaOverlaps` (conditional) | ML L131 | one-seed premise; conclusion "every reachable balanced-pair state" | abbreviated: by (iv) only the states reachable from that seed |
| lemma B, #139; `UniversalBoundaryHitting` (open) | ms L139-140; ML L144 | (AE°) with target "offset zero" on 𝒪_σ, every seed; (F) from `thm:overlap-finite` | exact; ms L141-142 adds an "Equivalently" in undefined terms; hybrid wordings in §17; the potential-overlap "BH" (`p1b-boundary-hitting-progress-2026-10-08.md` L113; `bpa-termination-by-overlap-depth-2026-10-02.md` L216-217) is another universe under the same name |
| `prop:G1-from-half-coincidences` | ms L1081 | per seed: (AE) at offset zero ⇔ no closed offset-zero-free set reachable: Part I's (AE) ⇔ (X) | exact |
| `thm:two-obstruction-completion` (Conditional) | ms L147-151 | per ternary σ: A(σ) ∧ B(σ) ⇒ (AE) at every vertex of 𝒪_σ | exact; "every swap seed is productive" (L150) abbreviates that conclusion |
| `cor:universal-completion` (Conditional) | ms L168-177 | (∀ ternary σ: A1′) ∧ (∀ ternary σ: BH) ⇒ ternary PSC; A1′ enters only under ∀ | exact |
| R1 `rankCheck`; `SelectedRank` | `R1SupportCertificate.lean` L85-101, L196-216; `SelectedRank.lean` L70-85 | ∀ represented state ∃ one lower-ranked child ⇒ (E) per state; (AE) only on a closed covered carrier (`rankCheck_all_literal_descendants`, L221) | exact |
| finite packet-graph lemma; class-A every-child results | `c4-ordered-word-completion-interface-2026-11-02.md` L86-92, L102-105; `class-a-boundary-y0-every-child-2026-10-31.md` L42-44 | item 1 = (E) at every root, item 2 = (A⁺), "C4 need not require item (2)"; ∀ first child ∃ continuation = (E) at each child | exact |
| `SourceLoss`; `MassGraph.NullStrict` | `PhysicalMass.lean` L192-209; QI L949, L1019 | ∀ source SCC ∃ losing member ⇔ (finite graph) every vertex is reached from a losing vertex: (X) ⇔ (AE) on the reversed graph; null strict mass is a limit o(θⁿ) and, with positive conserved mass, gives (AE), never (A) | exact; no binding of `SourceLoss` to `ChildGraph` is written |
| `fib_lasso` | QB L23-28, L140 | an (A)-shaped requirement over the whole class is refuted by one binary member; nothing on disk says (A) fails for every member | Part I §2 (its last sentence on `fib_lasso`) has this reading; ternary interfaces use the ternary controls of row A5 |

**Canonical wordings** (cite these, not the abbreviations; none is new):

- *BH, positive form* (`UniversalBoundaryHitting`, ML L144; ms L139-140): for every
  ternary PIP σ, every vertex of the finite seed-patch overlap graph on a
  directed cycle has a descendant of offset zero. *Exclusion form*
  (`AllSeedStrictZipperExclusion`, ML L125; ms L1081): no nonempty child-closed
  set of non-coincidence vertices without an offset-zero vertex is reachable
  from any swap seed. Per σ they agree by finite-graph logic (row C9). A
  strict-zipper vertex has no offset-zero descendant by definition (ms L1022),
  so "every cyclic strict-zipper overlap has an offset-zero descendant" mixes them.
- *#84*: there are letters a ≠ b such that every overlap reachable from the seed
  overlaps of (ab, ba) has a coincidence descendant. A *seed coincidence path* is
  (E) at a seed overlap; *one-seed overlap productivity* is (AE) rooted there.
- *C4* (`prob:C4`): for every ternary PIP σ and every strict component C of σ
  (finite by definition, ms L595; of any size), C3-local holds for C; nothing
  is said about an infinite closed nonproductive set (the G1 side).
- *G1* (`hyp:G1`, ms L306): for every σ some N_σ bounds the states reachable
  from the swap seeds, with no bound uniform in σ; *G1b-1* (ms L388): for each
  σ one box D_σ, uniform in state, level and seed, not in σ.

## 11. Transfer matrix

Classes: **valid: proved** (lemma and where); **valid: needs a lemma** (the
missing typed statement); **invalid: exists** (a control on disk, with its
rejection layer); **invalid: needed** (the sources refuse the step, no control
on disk; inside the class one would often refute an open claim);
**unverified**. An abstract control is graph logic, not a claim about a
substitution. *Form of a control:* formal (a Lean theorem), executable (a
Mojo, Python or Quint test on disk), *written* (a proof or finite computation
in a note or the manuscript, no test located) or *branch only* (not on
`main`); unmarked controls are formal or executable, and none was run for
Part II. Most strict-system controls are rejected at PIP screening; those
inside the class (`fib_lasso`, the 1/02/202 packet cycles, 01/12/021,
1/02/220, the class-A cycles, the Tribonacci germ cycle of row L2) each refute
an intermediate lemma or a stronger reading, never C4, BH or PSC. Continued in
§12.2 (mass → C4), §13.3 (finite → uniform) and §15.

### 11.1 Path readings, all routes

| # | Attempted transfer | Class | Lemma, missing statement, or control (layer) |
| --- | --- | --- | --- |
| A1 | (E) at a root ⇒ (AE) there (R1 forward productivity; a "productive seed" read as #84) | invalid: exists | `fork_not_hereditarilyProductive`, `productive_not_forward` (QI L563, L570); `tm_fork` (QB L168; PIP screening); `productive_parent_has_unproductive_child` (`R1ProductivityScope.lean` L173) |
| A2 | (E) transports backward; (AE) forward (nonproductivity is child-closed) | valid: proved | `productive_of_reach`, `HereditarilyProductive.of_reach` (QI L151, L160); `productive_of_reflTransGen` (SS L612); `productivity_backward`, `nonproductivity_forward_closed` (`R1SupportCertificate.lean` L33, L39) |
| A3 | (AE) ⇔ no strict closed set reachable, of any cardinality | valid: proved | `hereditarilyProductive_iff_no_strictClosed` (QI L192); `unproductive_iff_closed_target_free_support` (`R1SupportCertificate.lean` L68), the pointwise ingredient: ¬(E) at s ⇔ s lies in a closed target-free set, possibly infinite |
| A4 | (A) ⇒ (AE) | valid: proved | `Inevitable.hereditarilyProductive` (QI L268; child-closed targets, no dead end), `InevMax.hereditarilyProductive` (L491); dead end: `stub_inevitable_not_productive` (L841) |
| A5 | (AE), or density one, ⇒ (A) | invalid: exists | `lasso_not_inevitable` (QI L657); in the class `fib_lasso` (QB L140; `kernel/tests/test_quantifier_controls.mojo`); ternary: `ex:flipped` (ms L1241, a productive recurrent noncoincident SCC; written: a manuscript finite computation, with the TLA model `proof/tla/MCFlippedTribonacci.tla`), the packet cycle 209 → 429 → 209 of 1/02/202 (`kernel/tests/test_packet_hub_analysis.mojo` L26-71), class-A Y0 ↔ CY (`class-a-boundary-cy-carrier-2026-10-31.md` L102-106; written); mass form `lassoMass_null_not_inevitable` (QI L1090) |
| A6 | no closed strict component ⇒ no strict cycle; every recurrent noncoincident SCC synchronizes | invalid: exists | `lasso_cycle_not_closed` (QI L666); `fib_lasso`; `ex:flipped`; 1/02/220, recurrent flat rows with exits (`c4-recurrent-flat-exits-2026-11-04.md` L66-79; `kernel/tests/test_c4_recurrent_flat_exits.mojo` L188); layer: closure |
| A7 | (E) at every root ⇒ (A⁺) (packet item 1 ⇒ item 2); a target-free recurrent packet SCC ⇒ a strict component | invalid: exists | 1/02/202: four target-free recurrent packet SCCs over productive sources, "They are not nonproductive BPA SCCs" (`target-aware-bpa-diagnostic-2026-10-02.md` L123-131, L186-189); `inevMax_iff_of_finite` (QI L477); layers: conclusion, closure |
| A8 | selected rank ⇒ all-edge descent, every walk terminates | invalid: exists | `productive_support_keeps_target_avoiding_cycle` (`R1SupportFixtures.lean` L110); Quint `rankDoesNotRequireAllEdgesDecreaseTest` (reported) |
| A9 | selected rank on a closed covered carrier ⇒ (AE) from the seeds | valid: proved | `covered_descendants_productive` (`SelectedRank.lean` L70; `seed_covered`, `closed`); `rankCheck_all_literal_descendants`; controls `control_carrier_not_closed`, `control_trap_has_no_terminal_path` (L123, L136) |
| A10 | ∀ first child ∃ continuation ⇒ (AE); a union of outgoing labels or selected exits ⇒ a child-closed carrier | invalid: needed; invalid: exists | firewalls `class-a-boundary-y0-every-child-2026-10-31.md` L6-7, `README.llm.txt` L408, proposed control `stem` (W6); `control_carrier_not_closed`, "This is an outgoing image, not a forward-closed carrier." (`class-a-boundary-cy-carrier-2026-10-31.md` L83) |
| A11 | (A) on a retained (truncated) graph ⇒ a conclusion on the full graph | invalid: exists | `stub_inevitable_not_productive`, `inevMax_iff` (QI L446); `Psc.GraphRefinement` (branch `9338b7a`) separates the obligations |
| A12 | a terminal path in a quotient ⇒ one from every actual source; every finite prefix lifts ⇒ the infinite path lifts | first: valid, proved under `Refinement` (lifts from every source); second: invalid, exists, valid with finite branching | `terminal_path_iff`, `one_sided_cannot_lift` (`QuotientDistance.lean` L51, L170); `liftsPaths_of_liftsPrefixes`, `fan_no_lift` (`GraphRefinement.lean` L281, L666) |
| A13 | `lem:descendants` (path ends = blocks of red(σⁿu, σⁿv)) read on B_σ | identity: invalid, exists; inclusion: valid, proved | `fib_descR_two`, `fib_one_not_mem_bpaStatesNC` (`Descendants.lean` L994, L980); `descR_of_isBlock` (L333) on the full graph; `exists_red_of_mem_bpaStatesNC` (L746) |

### 11.2 C4 ↔ G1, SCC Producer and PDS

| # | Attempted transfer | Class | Lemma, missing statement, or control (layer) |
| --- | --- | --- | --- |
| B1 | (X) without (F) ⇒ (AE°) or (AE) (C2 ⇒ SCC Producer without G1) | invalid: exists | `ray_exclusion_vacuous`, `loopRay_recurrent_not_closed` (QI L732, L782); abstract, not realised (§9) |
| B2 | (F) ∧ (X) ⇔ termination with coincidence, one seed | valid: proved | `terminatesWithCoincidence_iff_finite_and_exclusion` (QB L89); `hereditarilyProductive_iff_exclusion_of_finite` (QI L311); ms L589 |
| B3 | (AE°) ⇒ (AE) on B_σ with (F) (the step of ms L336) | valid: needs a lemma | `hereditarilyProductive_of_cyclic_of_finite` (QI L324) asks `NonTerminal` of every pair of lists; missing: the hypothesis relative to the reachable set and, for nonerasing σ, `Reach T₀ U → U.1 ≠ U.2 → ∃ V, child U V` on `bpaGraph` (W1); without (F): `ray_cyclicProductive_vacuous` (L717) |
| B4 | (AE) without (F) fed to `thm:bridge` | invalid: exists | `comb_productive_infinite` (QI L817); under lemma A the route "reads: G1 implies PDS" (ms L972) |
| B5 | a reachable strict system ⇒ ¬(AE), no (F) | valid: proved | `not_hereditarilyProductive_of_strictSystem` (QB L98); `StrictSystem.not_terminates` (SS L646) |
| B6 | the witness of (X) (ordered, reflexive strong connectivity on all pairs of lists, QI L135) ⇔ a `BpaStrictComponent` | valid: needs a lemma | for a seed of a nonerasing σ: the swap closure of a finite strongly connected strict closed set reachable from T₀ is a `BpaStrictComponent`, and a component meets such a set (W2); not the identity on sets: `altSubst` (`Descendants.lean` L866; connected only up to swap), `erase_control` (SS L2636; a dead-end singleton) |
| B7 | no `StrictSystem` ⇒ no `BpaStrictComponent` | valid: proved | `toStrictComponent` (SS L891); `no_strictComponent_of_strongCoincidence` (L2653); the one-line corollary has no name (W2) |
| B8 | no `BpaStrictComponent` ⇒ no `StrictSystem` | invalid: needed | the conversion needs `hswap`, `hmeet` (`StrictComponent.toBpa`, SS L911); for `cycC` reachability from a seed "is not proved" (`c4-reductio-lemmas-2026-11-07.md` L155); proposed control `idSubst`, not primitive (W6) |
| B9 | global C4 ∧ (F) at a seed ∧ nonerasure ⇒ termination | valid: proved, with C4 read as "no `BpaStrictComponent`" (C3-local ⇒ contradiction is `prop:chain`, a manuscript proof with no Lean form) | contrapositive of SS L2606; `nonerasing_of_irreducible` (SS L1899) |
| B10 | lemma A ⇒ no finite strict system (C4 vacuous) | valid: proved | `no_strictSystem_of_strongCoincidence` (SS L538) from `not_witness` (L518); `C4FromStrongCoincidence`: proved |
| B11 | lemma A ⇒ (AE) at every block, no (F) (second route to SCC Producer) | valid: proved in ms | `cor:scc-reduction`(i), ms L972, proof L978; `thm:BD-eliminator` L693; Lean form missing (W3); no ledger branch (§17, O6) |
| B12 | C4 ⇒ lemma A | invalid: needed | extraction needs finiteness: `strictSystem_of_factorSet` (SS L569, `hfin`); bounded gaps in Proposition 3 of `c4-cut-attractor-window-2026-11-05.md` (L262-263); "a failure of strong coincidence is **not** known to yield a strict system" (SS L199-200) |
| B13 | one witnessed pair, or the Barge-Diamond pair, ⇒ no strict system or all pairs | invalid: exists | `carrier_witnesses` (SS L1822) with `carrierSink_strictComponent` (L1845) on 10/102/211; PIP screening (`carrier_not_irreducible`, L2805) |
| B14 | `C4StandingCorpus` ∧ per-specimen (F) ⇒ termination and PDS on the 4,554 | valid: proved as an implication, finite domain; the conclusion is not a governed claim | `terminates_of_strongCoincidence` (SS L689: all-pairs witnesses `hw`, a seed, `hfin`); QB L89; then the imported `thm:bridge`; the inputs are the Mojo census behind `C4StandingCorpus` (Lean decides eight specimens, SS L2661) and the finite computation `comp:bpa` (ms L1189), not Lean facts |
| B15 | recurrence with nonsynchronizing rows in place of child closure; C3-local for every recurrent noncoincident SCC | invalid: exists | 1/02/220, "Exact negative to replacing closure by recurrence" (`c4-recurrent-flat-exits-2026-11-04.md` L66-79), in PIP; 60 of the 5,022 recurrent noncoincident corpus SCCs have no newborn or inherited synchronizing boundary, all singletons with an exit (`comp:bpa`, ms L1189; written: a manuscript finite computation); layer: closure |
| B16 | acceptance by `build_derived_system` (`kernel/psc/derived_system.mojo` L90) ⇒ strict component | invalid: exists | `carrierC` (SS L1789-1816) with `carrierSink_strictComponent`: the validator checks a strict system up to swap, not strong connectivity (its checks read from the code, `derived_system.mojo` L90-136: nonempty, balanced, noncoincident, irreducible, distinct, child-closed; its acceptance of `carrierC` was not executed) |
| B17 | "terminates" (finite state set) ⇒ terminates with coincidence | invalid: exists | `tm_finite` (`Descendants.lean` L924) with `tm_not_terminates` (SS L1676); outside the class (`tm_incidence_singular`, QB L182) |
| B18 | reductio lemmas cited as facts about an existing component | invalid: exists (vacuity) | `specimens_no_strictSystem`, `trib_no_strictSystem`, `u021_no_strictSystem` (SS L2661, L1634, L1882): the hypothesis class is empty on those PIP specimens |
| B19 | a necessary condition read as a certificate: a nonzero `candidate_good_edge_mask` bit ⇒ the Barge-Diamond pair; first-child phase agreement ⇒ a phase on interior children | invalid: needed; invalid: exists (written) | "This is a one-way necessary condition. A surviving bit is only *compatible* with being the Barge–Diamond pair" (`c4-good-edge-system-bridge.md` L39-41); the first-child phase agrees on the PIP and the non-Pisot strict rows and "has no discriminatory force" between them (`c4-ordered-hub-offset-negative-2026-10-06.md` L74-76); rank three: row U12 |
| B20 | `thm:towers` (for every T ∈ C and all large n, *one* zero return of σⁿ(T) with legal radius-R contexts at q + 1 levels, ms L809) read as legality of every cut, every state or the swap seeds | invalid: needed | statement scope; seeds and states need not be legal (`rem:legality`, ms L301-302) |

### 11.3 Direct route (#84, #138, #139) ↔ G1 and C4

| # | Attempted transfer | Class | Lemma, missing statement, or control (layer) |
| --- | --- | --- | --- |
| C1 | #84 (one seed) ⇒ PDS | valid: proved | `thm:main-density`, ms L922-927, through the imported `thm:bsw`; governed `PDSOverlapRoute`: conditional |
| C2 | (AE) on 𝒪_σ from s ⇔ the closure of s is finite and productive | valid: proved | `prop:G1-from-overlaps` (ms L1069-1073); `thm:density`(iii)-(v) |
| C3 | (AE) at one seed ⇒ at every seed, or G1 | valid: needs a lemma | Theorem SC (`p1-seed-strength-2026-10-08.md` L66-97), through PDS and review-pending imports; unusable inside a proof of #84; the seeds reach different recurrent parts on 444 of 4,554 specimens (`kernel/tests/test_seed_strength.mojo` L119-132) |
| C4 | #84 ⇒ every pair eventually coincident | valid: needs a lemma | Proposition SA (`p1-seed-strength-2026-10-08.md` L36-61); `prop:aligned-overlaps` (ms L935-951) |
| C5 | A(σ) ∧ B(σ) ⇒ all-vertex (AE) on 𝒪_σ | valid: proved | ms L147-166; `two_obstruction_skeleton` (QI L340); neither hypothesis can be dropped: `fork_without_A`, `fork_without_B` (L590, L610) |
| C6 | `TwoObstructionCompletion` read as its consequent | invalid: exists | `fork_without_A`, `fork_without_B`; both antecedents open |
| C7 | A1′(σ) ∧ BH(σ) ⇒ PDS(σ) for one σ (PR #281 body) | valid: needs a lemma | Theorem C, Corollary C1 (`p1a-template-collapse-2026-10-05.md` L38-98) trade an obstruction for σ against A1′ at σ²; the family must be closed under σ ↦ σ², or A1′ asked of the squares |
| C8 | #84 ⇔ A1′ ∧ BH ("exactly", `direct-attack-frontier-2026-10-23.md` L25-26), universal forms | ⇐: valid, proved in ms; ⇒: valid, needs a lemma | ⇐ is the proof of `cor:universal-completion` (ms L179-186: Theorem C, then `thm:two-obstruction-completion`); ⇒ passes through PDS (Proposition SA; proof of `thm:seedwise`, ms L576); a direct rooted converse `two_obstruction_iff` is missing (W4) |
| C9 | lemma B ⇒ all-seed strict-zipper exclusion, per σ | valid: needs a lemma | `hereditarilyProductive_of_cyclic_of_finite` with target offset zero; written analogue `bpa-termination-by-overlap-depth-2026-10-02.md` L212-224; Lean instance missing (W4); no ledger edge (§17, O4) |
| C10 | all-seed strict-zipper exclusion ⇒ G1 | valid: proved in ms | ms L1080-1087; `G1HalfCoincidenceRoute`: conditional |
| C11 | G1 (finite closure of s) ⇒ lemma B rooted at s | valid: needs a lemma | derived during the Part II synthesis, unreviewed; ingredients ms L294, L955-966, L1069-1089 (W17) |
| C12 | governed BH (seed graph) ⇒ BH on potential overlaps | invalid: needed | universe gap: the seed graphs miss box cycle vertices of cube (38), golden pump (100), plastic (16) (`kernel/tests/test_vertex_coincidence.mojo` L90-97); the only route is through PDS, with lemma A and the three-letter `thm:seedwise` (ms L558-559, L576) |
| C13 | a boundary hit (offset zero, common vertex, equal letter at an index) ⇒ a coincidence target | invalid: exists | `fork_without_A`; PIP 1/02/202, second inflation of (01, 10) (`kernel/tests/test_target_packets.mojo` L224-232); (12, 21) has "a terminal zero return and no diagonal child" (`side-notes-ledger.md` L109-123; a side-notes record, written) |
| C14 | a hit at one vertex, path or selected exit ⇒ BH or #84; conversely a productive cycle refutes BH or (AE) | invalid: exists (both) | `fork`; `control_trap_has_no_terminal_path` (`SelectedRank.lean` L136); `lasso_hereditarilyProductive` (QI L641) with `lasso_cycle_not_closed`; `fib_lasso` |
| C15 | `CoincidenceDensityOne` "Repository-proved" read as δ = 1; `PDSImpliesRepoG1` (proved) read as G1 | invalid: needed (a control would refute an open claim) | the first label belongs to the equivalence `lem:three-forms`, the conclusion needs the open `OverlapProductivity` (`docs/ledger-index.md` L32); ms L566-571, instance only through `BoundedPureDiscreteSpectrum` (finite-domain) |
| C16 | all-vertex statements about Open Problem 5.35 (ms L903) applied to the one-seed gate | valid: needs a lemma | only through Theorem SC (row C3) |

## 12. Null versus empty on the repository's bridges

*N1* is coincidence density one, δ(s) = 1: the mass is the non-common physical
length on the graph itself, conserved at rate β (`cor:overlap-mass`, ms
L881-886). *N2* is a null internal-space overlap of a letter pair,
μ(R̂_c ∩ R̂_c′) = 0 in E^s × H_M (eq. (6), L184-189 of
`c4-nonunit-madic-counting-bridge-2026-11-04.md`, the *M-adic bridge*).
`hereditarilyProductive_of_nullStrict` (QI L1019) type-checks on N1 (h = λ,
θ = β) and gives the (AE) of `thm:density`(iv) without (F); it does not
type-check on N2, since `NullStrict` (QI L949) measures non-target descendants
of the graph itself. The only transfer from N2 is Theorem M1 (M-adic bridge
L195-229) or Corollary B′ (`c4-cut-pair-productivity-2026-11-04.md` L178-181):
nullity on **every** cut pair excludes a supplied finite strict system. The
output is (X); (AE) needs (F) as well (row B2). This sharpens Part I §4, whose
text is kept. Null is weaker than empty (residue-slice separation, M-adic
bridge L333-336) and differs from empty interior (Lemma G(2),
`c4-cut-attractor-window-2026-11-05.md` L137-138; equal to null only for unit
σ, through an imported null boundary, L188-191, L286) and from a small finite
bound (`c4-pair-overlap-class-2026-11-05.md` L184-195, the *class note*);
lifted null does not give Euclidean null (M-adic bridge L187-189). Density one
leaves a complement of measure zero and empty interior that is never empty (ms
L905, L911). One state carries a positive physical interval h and a null
internal-space measure v (`physical-mass-refinement-2026-11-08.md` L84, L87).

### 12.1 Stage-by-stage type-check: mass loss → physical overlap → literal Sync

| Stage | Source type | Target type | Typed statement and where | Class |
| --- | --- | --- | --- | --- |
| i.0 source loss → zero vector | finite T ≥ 0, h > 0, v ≥ 0, θv ≤ Tv, `SourceLoss` | v = 0 on the supplied index type | `PhysicalMass.zero_of_source_loss` (`PhysicalMass.lean` L265; #519, on main) | valid: proved (abstract) |
| i.1 packet row → measurable set | `Fin p.count` with a label (c, c′, z) (`OverlapPacket`; the #515 packet) | E i = K_c ∩ (K_c′ + z*) with `cover`, `scaling`, `finite` of `recurrence_of_cover` (`OverlapContraction.lean` L160) | a decoder with these proofs; absent: a state is "a coordinate label" (`c4-overlap-lean-packet-binding-2026-11-05.md` L23) | valid: needs a lemma |
| i.2 occurrence sum → matrix action | Σ_e μ(E(target i e)) | `action T v i` with T i j = #{e : target i e = j} | `sum_occurrences_eq_action` (W15); absent | valid: needs a lemma |
| i.3 T-edge → set-equation piece | literal prefix positions in σ^q(d), σ^q(d′) passing integrality, on track-swap orbits | an affine image of E(d, d′, z_new), Haar-scaled | written: `c4-pair-overlap-graph-2026-11-05.md` L88-121; class note L98-134 (review pending) | valid: proved (written) |
| i.4 T-graph component → strict component | SCC of (letter, letter, offset) states | strict component of B_σ (word pairs) | none: different state and edge types | invalid: exists (the 18-source class, §15.3) |
| i.5 null roots + cut pairs of a supplied C → cover | roots indexed by unordered letter pairs | Ẑ = ∪ over A(C) of R̂_c ∩ R̂_c′ | `cutPair_ne` (SS L455), `no_positive_subset_of_null` (`OverlapContraction.lean` L234), written M1 bound κ/L_max (M-adic bridge L195-209) | valid: needs a lemma (`no_strictSystem_of_null_cutPairs`, W15); output ¬∃ finite strict system |
| i.6 nullity → addressed coincidence witness | μ(K_c ∩ K_c′) = 0 | (T, occurrences, depth, two addresses) with equal letter and equal Parikh prefixes | the converse of eq. (6): "Only ⇐ is found" (cut-attractor L287); inside a strict component no cut pair has a witness (`not_witness`, SS L518) | unverified |
| i.7 addressed witness → C3-local | an addressed witness for an actual irreducible noncoincident T | some T′ ∈ C with a one-step interior Sync± zero return | written lemma `c4-addressed-overlap-to-newborn-2026-11-04.md` L22-29, with a Mojo contract (reported) | valid: proved (written) |

The chain reaches the word level only by reductio (i.5), excluding every
supplied finite strict system and exhibiting nothing; i.6 has no lemma. The
three zero-offset distinct-letter roots of i.1 are a construction choice of
#497/#515: "They are not a declaration that every strict-PIP problem has these
roots" (`physical-mass-refinement-2026-11-08.md` L76-77).

### 12.2 Transfers on the mass route (matrix continued)

| # | Attempted transfer | Class | Lemma or control (layer) |
| --- | --- | --- | --- |
| Z1 | nullity of every root ⇒ emptiness | invalid: exists | pair {0, 1} of 1/021/001: null by eq. (6), contains the origin (`c4-finite-cylinder-overlap-verifier-2026-11-04.md` L204-215; written proof: nonemptiness from the set equations, nullity from eq. (6); no test, W8); conclusion |
| Z2 | null strict mass ⇒ (A), or ⇒ an empty strict set | invalid: exists | `lassoMass_null_not_inevitable` (QI L1090); `fib_lasso` |
| Z3 | null strict mass ⇒ (AE) without conservation | invalid: exists | `slow_null_not_hereditarilyProductive` (QI L1152) |
| Z4 | h > 0 ⇒ v > 0 (positive physical overlap ⇒ positive measure) | invalid: exists | the three zero-offset roots of 1/021/001 (h > 0 by the typed strip F1 of #497, branch only; v = 0 by eq. (6), written); in PIP |
| Z5 | Theorem B (λ(Z_A) ≥ κ/L_max, so positive overlap for *some* cut pair, `c4-cut-pair-productivity-2026-11-04.md` L124-125) used for every cut pair, or merged with Lemma G(2) (nonempty interior for every first pair represented in a sink SCC C′, `c4-cut-attractor-window-2026-11-05.md` L137-138); one null pair excludes C | invalid: exists | transient closure of (02, 20) under 10/102/211, a cut pair {0, 2} not carried by the sink SCC (`c4-cut-pair-productivity-2026-11-04.md` L362-367; written, outside PIP, so it calibrates the combinatorial step only, L372-373); per-pair positivity needs a strongly connected C (`c4-every-cut-pair-positive-density-2026-11-04.md` L9); layer: PIP screening for the specimen |
| Z6 | one null pair, or a bound v_root < ε at one n, ⇒ no strict system | invalid: needed | a control in PIP would refute C4; Corollary B′ asks every pair, and the limit form is M-adic bridge L289-313 |
| Z7 | Lemma P (unit, Euclidean) for non-unit σ; lifted null ⇒ Euclidean null | invalid: needed | use the lifted eq. (6) and M1 (M-adic bridge L173-189) |
| Z8 | θ_c ≤ 1/2 for every letter ⇒ a strict system exists | invalid: exists | 1/021/001 (`c4-nonunit-residue-occupancy-2026-11-04.md` L17-19; written measure argument, executable residue table, L3-6); in PIP |
| Z9 | mean of defects → 0 ⇒ some defect is 0 | invalid: exists | `meanZeroWithoutReturnTest` (`proof/quint/PscR2.qnt` L42-44, not run here); `deck_score_average_counterexample` (`R2.lean` L138) |
| Z10 | a recurrent coincidence-free set keeps its mass | invalid: exists | 1/02/220: exits lose Parikh mass (`c4-recurrent-flat-exits-2026-11-04.md` L47, L69-99) |
| Z11 | a feasible positive ray ⇒ positive measure; the supersolution θv ≤ Tv used with the equality rules CE2-CE4 | invalid: exists | v = 0 and CE4; T = [3], θ = 2, v = [1]; equality needs within-letter measure-disjointness (F3); all on the #497 branch, not on main |
| Z12 | `SourceLoss` read as "some losing vertex" or "every sink SCC loses" | invalid: exists | `conservativeSourceRefusedTest`, `losingSinkIsNotLosingSourceTest` (`proof/quint/PhysicalMass.qnt` L230, L241; not run here) |
| Z13 | N2 ⇒ N1 (null pair overlaps ⇒ δ(s) = 1) | unverified | no lemma; `NullStrict` does not type-check on N2 |
| Z14 | (AE) on B_σ without (F) ⇒ δ(s) = 1; a measure statement ⇒ BH | invalid: needed | `thm:density`(v) needs (F), proposed control `drip` (W6); BH is a pointwise hit (`p1b-madic-carry-reduction-2026-10-01.md` L254-255) |
| Z15 | null roots ∧ M1 ⇒ (AE), termination or PDS without (F) | invalid: exists | `ray`, `loopRay` (row B1); with (F) valid (row B2) |

**Which output type.** (a) exclusion of every supplied finite strict system,
C4 then vacuous for the source (class note L53-55), or (b) an exhibited Sync±
newborn, which needs a coincidence witness (i.6). The kernel and refinement
notes ask for (b) (`physical-mass-kernel-2026-11-08.md` L220-228;
`physical-mass-refinement-2026-11-08.md` L325-328); the class and closure notes
deliver (a); the choice is O24. The twelve and the eighteen sources have
images of length at most three (`physical-mass-refinement-2026-11-08.md`
L191-204; class note L35-39), and the class note states PIP incidence for the
eighteen (L41-43); a PIP source of that shape is a corpus member by definition
(ms L1185), where the exclusion is already `C4StandingCorpus`. Membership of
all thirty was checked only by a scratch call of the Python `pip_corpus()`
(§19). #497: "The new finite certificate adds no source coverage" (PR body,
reported).

## 13. Finite versus uniform

### 13.1 Senses of "uniform"

| Sense | Shape | Valid direction and control |
| --- | --- | --- |
| domain | ∀σ in the standing class against ∀σ in a finite set or family | no swap; a domain enlargement (governance refusal) |
| bound in σ | ∃B ∀σ | asked by no open statement (G1, #84, #138, #139 are ∀σ ∃...); false for the hitting depth on the class-A line |
| state | ∀σ ∃B_σ ∀ states, levels, seeds | G1b-1 (ms L388), `thm:overlap-finite` (L538-541), K, K′ (L1070, L1081); G1 has this shape |
| parameter | ∃B ∀n over a family | holds for two-tail depth 5 and class-D b = 0 depths 4, 6; fails on class A |
| size of C | `prob:C4` "uniformly in" the size of C | read "every finite C"; the constants on disk (B_C, L_max, κ/L_max) depend on C |
| supplied object | ∀ supplied matrix, packet or component | not existence of the object for each σ (`physical-mass-kernel-literature-gate-2026-11-08.md` L51-53) |
| depth in one graph | ∀v ∃k ⇒ ∃K ∀v | valid when the vertex set is finite (ms L874); for (A) when finitely branching (König, W14) |

`chain_not_uniform` (QI L896) bounds every path (`HitsWithin`, L857); the
repository's depths (K, K′, L_n, witness levels) are least depths of *some*
descendant, and the interface has no depth-bounded (E) yet (W5). The literal
instance in the class is the class-A line, n/10 < L_n ≤ n + 2 for n ≥ 4
(`p1b-class-a-run-index-2026-10-21.md` L98-117). This sharpens Part I §5, kept.

### 13.2 Finite-domain, family and capped results with the scope of their evidence

| Result | Status | Scope of the evidence | Not to be read as |
| --- | --- | --- | --- |
| `C4StandingCorpus`; the strong-coincidence census (not a governed claim) | finite-domain | the 4,554 specimens: witnesses for all 13,662 letter pairs, least level ≤ 15 (`c4-finite-domain-closure-2026-11-05.md` L64-81); Lean decides eight specimens (`specimens_no_strictSystem`, SS L2661); the census keeps maximum 15 on nested domains up to 408,798 specimens (`strong-coincidence-census-2026-10-04.md` L45-48) | C4 for every ternary PIP; ∃n₀ ∀σ |
| `BoundedPureDiscreteSpectrum` | finite-domain | 145,806 box certificates | formal productivity or PDS for every PIP |
| `comp:bpa`, `comp:overlap`, `comp:disc` | Finite computation | the corpus (ms L1188-1229); a capped run is inconclusive (L1185) | bounds for other σ: the cube-image specimen exhausts budgets of 10⁵ to 4·10⁵ letters on a finite automaton (`bpa-termination-by-overlap-depth-2026-10-02.md` L111-112) |
| `ClassDBoundaryHitting`, `ClassDFiniteBPA` | proved | determinant-two class-D normal form, p − q ∈ {−1, +1} (ML L177, L184); ∀σ ∃K_σ (`class-d-g1-corollary-2026-10-22.md` L132-134) | ∃K ∀σ; a cover of the class |
| `ClassABoundaryHittingLowGaps` | proved | eight lines (n+d, n, n±1), d ≤ 4 (`claim-status-and-source-map-2026-09-13.md` L64) | a uniform hitting depth |
| class-A run-index bound | not a governed claim (`require_contract` only) | the line (n+1, n, n+1), n ≥ 4, vertex family A_n | a statement about every line of the L64 row (§17, O12) |
| two-tail theorem | not a governed claim | a, b ≥ 0, tails 102 and 120 (`experiments/c4_two_tail_uniform/docs/two-tail-uniform.md` L30-32, L279-282) | a uniform spectral margin |
| 18-source class; 12 sources of #497/#515 | not governed claims | named sources with one incidence matrix each, corpus members as §12.2 states | non-unit nullity in general; new C4 coverage |
| `PhysicalMass.zero_of_source_loss` | Lean, not governed | every supplied finite matrix; no instance (`PhysicalMass.lean` L405-410) | a statement about any σ |
| uniform conservative-source exclusion | not a governed claim (route-map label) | open; checked on twelve sources (`physical-mass-kernel-2026-11-08.md` L204-214) | evidence for every σ |
| Quint models; R1 checkers and fixtures | not governed | bounded fixtures (`proof/quint/PhysicalMass.qnt` L5; the R1 models count letters 0 and 1 only); a supplied `actual` | unbounded theorems; ternary or PIP statements (§15.4) |
| K₂ ≡ 0 window search | not governed | 11,838 non-PIP specimens, states of length ≤ 13 (`c4-closed-component-search-2026-11-07.md` L324-326) | nonexistence at every length, or in PIP |
| `LeftmostChainG1Certificate` | proved, per specimen | hypothesis met by 1,794 corpus specimens and failed by all 210 catch-up-free ones (`claim-status-and-source-map-2026-09-13.md` L109; `p1b-leftmost-chain-periodic-pair-2026-10-05.md` L350-351; two pinned in `kernel/tests/test_leftmost_chain.mojo` L103) | G1 universally |
| level and state caps | budgets | 20,000 BPA states; level cap 12 of `kernel/psc/c4_cut_pair_reduction.mojo` (L107-108) | verdicts: the plastic reversal needs level 15 (`plasticRev_least`, SS L1564) |

### 13.3 Transfers (matrix continued)

| # | Attempted transfer | Class | Lemma or control |
| --- | --- | --- | --- |
| U1 | inside one finite graph, ∀v ∃k ⇒ ∃K ∀v | valid: proved | ms L874; `prop:G1-from-overlaps`; abstract lemma missing (W5) |
| U2 | across a family, ∀N ∃d ⇒ ∃d ∀N | invalid: exists | `chain_not_uniform` (QI L896); class-A A_n (literal, in PIP; a written proof with finite exact replays, `p1b-class-a-run-index-2026-10-21.md` L98-117) |
| U3 | agreement on a finite grid ⇒ every parameter | invalid: exists | class-D fitted index 9 − a (`class-d-g1-corollary-2026-10-22.md` L152; written); `chain_agrees_with_ray` (QI L904) |
| U4 | finite-prefix replay with a parameter-symbolic tail ⇒ the family | valid: proved, as recorded | class-D and class-A family certificates; their negative controls in the same notes |
| U5 | a productivity depth uniform over all states ⇒ (F) | invalid: exists | `comb` (QI L817); the depth-1 statement is not named (W5) |
| U6 | ∀σ ∃D_σ: Disc ≤ D_σ ⇒ G1; finite 𝒪_σ ⇒ finite B_σ | invalid: needed | "a bounded box contains arbitrarily long such walks" (ms L449); ms L547 |
| U7 | finite 𝒪_σ ∧ all-seed hitting ⇒ G1 for σ | valid: proved in ms | ms L1069-1089; cube-image K′ = 17 on 1,142 vertices (L1089) |
| U8 | uniform hitting depth ⇒ uniform state length | invalid: needed | H₋(a) = 2(3a+8)⁶ grows with a (`class-d-g1-corollary-2026-10-22.md` L112; "Nor do those depth bounds make the displayed word-length bounds constant", L143) |
| U9 | uniform word depth ⇒ uniform spectral margin | invalid: exists (written) | two-tail note §9; class-D note L140-143; `proof-ladder.md` L36-37 |
| U10 | ∀n ∃G_n (gaps per level) ⇒ ∃G ∀n (premise of Lemma F(b)); a statement about finite components ⇒ one about an infinite closed set (M1's κ/L_max → 0) | invalid: exists (schema) | `chain_not_uniform`; Proposition 3 calls the clause "G1-type" (cut-attractor L262-263); `ray_exclusion_vacuous` (QI L732) |
| U11 | budget exhausted ⇒ infinite; no witness within a cap ⇒ no witness | invalid: exists | cube-image specimen (a budget exhaustion on a finite automaton, `bpa-termination-by-overlap-depth-2026-10-02.md` L111-112; written record, the finiteness certificate is executable); `plasticRev_least` (SS L1564) |
| U12 | a complete flat rank-three depth-two cone ⇒ a Sync newborn by depth two | invalid: exists | 01/12/021, newborn at depth three (`kernel/tests/test_c4_two_generation_rank.mojo` L132) |
| U13 | three-letter statements (ms L148, L559) on larger alphabets | invalid: needed | statement scope |
| U14 | a theorem over supplied matrices, or twelve or eighteen sources, ⇒ nullity for every non-unit PIP σ | valid: needs a lemma, resp. invalid: needed | carrier existence per σ, the supersolution and uniform conservative-source exclusion (open); enclosure refusals on six sources (class note §2) |
| U15 | a `−1` of `psc.coincidence_formula`, "a decided negative, not an exhausted budget" (`kernel/psc/coincidence_formula.mojo` L236-238), read outside the Pisot regime | invalid: needed | the exploration "is finite by the Pisot property" (`c4-finite-domain-closure-2026-11-05.md` L70-71); a decided `−1` is a verdict inside that regime only |

## 14. Conditional theorems, their antecedents, and status surfaces

**Reading rule.** "\Status{Conditional}: proved here from named hypotheses that
are themselves open" (ms L115); a proved node with open dependencies "is a
conditional theorem" (ML L56-57); `ProvedDef` of `proof/tla/Ledger.tla` holds
implications that can be discharged, open premises included (CG L182-186). No
row supplies its antecedent.

| Conditional result | Antecedents and their status | It does not give |
| --- | --- | --- |
| `TwoObstructionCompletion` (conditional); ms L147 | `UniversalAlignedCoincidence`, `UniversalBoundaryHitting` (both open) | #84, PDS or G1 as facts (row C6) |
| `cor:universal-completion` (Conditional), ms L168 | A1′ and BH for every ternary PIP; A1′ is not a governed name | the per-substitution statement with A1′ (row C7) |
| `C4`, `C3Local`, `C2` (conditional) | `UniversalAlignedCoincidence` (open) through `C4FromStrongCoincidence` (proved); C4 | a Sync± newborn (C4 "holds vacuously wherever none exists", `c4-finite-domain-closure-2026-11-05.md` L26-27; the governed node is conditional through `C4FromStrongCoincidence`, L52-54, while `prob:C4` stays open); SCC Producer without G1 (row B1) |
| `SinkSCCReduction` (conditional) | `G1` (open); the Lean form carries `hfin` (SS L2606-2626) | existence of a strict component |
| `PDS`; `PDSOverlapRoute`; `PDSSpectralRoute` (conditional) | `G1`, `SCCProducer` (open), `StandardBPAEquivalence` (imported, since `e7853fb`); `OverlapProductivity` (open), `DensityToPDSBridge` (imported); `G1`, `SpectralSCCProducer` (open), the imported `thm:bridge` not named (§14.2) | PDS |
| `G1HalfCoincidenceRoute`, `G1OverlapRoute`, `G1FromRenewal`; `AllStatesProductiveViaOverlaps` (conditional) | all-seed gates or G1b-2 (open); `OverlapProductivity` (open) | G1; the all-seed conclusion the last one prints (§10) |
| `C4FromStrongCoincidence`, `PDSImpliesRepoG1`, `PDSImpliesSeedwiseTermination` (proved) | the antecedent is not a dependency: all-pairs witnesses (open as `UniversalAlignedCoincidence`), PDS (open) | the antecedent; G1 (row C15) |
| `CoincidenceDensityOne` (proved, closure incomplete) | `OverlapProductivity` (open) | δ = 1 for any σ (row C15) |
| `PhysicalMass.zero_of_source_loss`; `OverlapContraction.null_of_cover` (Lean, not governed) | every hypothesis an argument (`PhysicalMass.lean` L406-427; `OverlapContraction.lean` L13-16) | an instance: packet acceptance, a digest or a green job supplies none |
| `R1.no_positive_periodic_orbit_with_nonnegative_digits` | a one-sign digit premise, violated by `tribonacci_three_step_signed_forcing` (`proof/psc_routes/R1.lean` L180-184) | exclusion of literal ancestry cycles |
| reductio lemmas (`c4-reductio-lemmas-2026-11-07.md` L27-29) | a hypothetical strict component | facts about any existing object in PIP (row B18) |
| leave-one-out controls (`Psc.ReductioControls`; the Lean controls of B′) | a concrete system meeting every hypothesis but h, with h false | that h is needed: a control "does **not** show that `h` is needed for the conclusion, except where a negative control (the conclusion fails) is stated" (`proof/PscVerif/PscVerif/ReductioControls.lean` L20-26); each B′ control "refutes the weakened *step*, not B′ itself" (`c4-bprime-lean-2026-11-09.md` L73-75) |

### 14.1 Status surfaces that can be misread

| Surface | Can be read as | Means |
| --- | --- | --- |
| "[PROVED assembly]", "[proved assembly]" (`proof-ladder.md` L87; `direct-attack-frontier-2026-10-23.md` L21) | #84 proved | the status of the implication into the line; both antecedents open |
| "Repository-proved" on `CoincidenceDensityOne` with closure "incomplete: OverlapProductivity" (`docs/ledger-index.md` L32) | δ = 1 holds | the equivalence `lem:three-forms` |
| `settled_classes` contains "conditional" (CG L144) | a clean promotion audit near C4 or PDS | the promotion audit never reports a proving phrase next to a conditional node with open antecedents (`tools/claim_governance/checks/promotion.py` L15) |
| `proof_reviewed`: "true" on all 91 repository-theorem records of `proof/tla/ledger.json` | independently reviewed | a field the vendored schema demands (`tools/proof_records/records.py` L161; ML L483), also on `G1` and `SCCProducer` |
| `REVIEWED` = "independently reviewed 2026-10-08 ..." (ML L43), on seven proved records | independent human review | the cited review calls itself "an internal mathematical and implementation review, not human peer review" (`review-box-leftmost-ledger-2026-10-08.md` L3-8) |
| `require_claim("G1b2RenewalFiniteness")` in seven tests (e.g. `kernel/tests/test_renewal.mojo` L142) | evidence for an open claim | a link, not evidence (AGENTS.md) |
| one Scope string for every record (ML L32) | universal scope | family and per-specimen restrictions appear in the Statement cell only |
| coverage `partial` in `docs/proof-bank.md` (rows `C4FromStrongCoincidence`, `G1b1BoundedDiscrepancy`, `SinkSCCReduction`); `none` on `G1`, the three `G1…Route` rows, `PDS`, `PDSImpliesRepoG1`, `PDSImpliesSeedwiseTermination` | a Lean proof of the node | "A partial Lean binding proves only the listed algebraic component" (generated header of `docs/proof-bank.md`); the Lean `thm:sink` does not record reachability from the seed (§10) |
| `<Name>NotEstablished` invariants of `proof/tla/MCLedger*.cfg` | the statement fails | relative to the encoded edges; pending records cannot be derived, so `MCLedgerTwoObstructionsAssumed` keeps `OverlapProductivity`, `SCCProducer` and `G1` not established |
| `StandardBPAEquivalence` named an equivalence | both directions imported | "We use only the forward implication stated" (ms L321; seed clause unverified, L564) |
| issue #9 state closed, state_reason completed (closed by #226); #84, #138, #139 open, reopened, still listing #161, #162, #326 as closing PRs | closure of C4, or of the trackers | routing events (`README.llm.txt` L5: "closed for routing, NOT a proof") |

### 14.2 The PDS repair of `e7853fb`, and nodes of the same kind (reported, not changed)

`e7853fb` gave the record `PDS` the dependency `StandardBPAEquivalence` and added
it to the assumption sets `G1AndProducer`, `G1AndC4` (ML L227-228, L322, L324;
Part I §6). Three records of the same kind apply an import no dependency names;
none is changed here. (1) `PDSSpectralRoute` (ML L213) depends on (`G1`,
`SpectralSCCProducer`); the spectral route ends at SCC Producer (ms L785) and
the step to PDS is `thm:main-conditional`, whose proof ends "Imported
Theorem~\ref{thm:bridge} concludes" (ms L336); `SpectralGateAssumed` (ML L326,
used by `proof/tla/MCLedgerSpectralGateAssumed.cfg`) does not assume the import.
Proposed: the repair of `PDS` (O13). (2) `PeriodicPairOneFibre` (ML L236-238)
uses Solomyak's eigenvalue criterion, "Not read directly, used only through the
restatements above" (`p1b-periodic-pair-fibre-literature-gate-2026-10-02.md`
L40, L80), and Barge-Kellendonk (L34). (3) `DefectTheorem` (ML L61) applies the
imported `thm:defect` (ms L264); `thm:mosse` (L256) has no node either. The
mirror defect: `ConcentrationAuxB` (ML L205-206), an exclusion over supplied
components, depends on `G1` and `SinkSCCReduction`, while `C4`, `C3Local`, `C2`
(ML L217-221) do not (O23). W11 is a regression that would have caught `PDS`.

## 15. Literal versus affine or quotient edges; objects that share a name

### 15.1 Three child-graph conventions

(R) raw ordered pairs with full rows, coincidences included
(`R1SupportFixtures.lean` L94-97; `kernel/psc/ordered_occurrence_graph.mojo`
L43); (T) ordered pairs with coincidences terminal (ms L291, there modulo side
swap; `ChildNC`; `bpaGraph`, QB L54); (N) one representative per unordered
pair, coincidences terminal (`kernel/substitution_dynamics/automaton.mojo`
L48-50, L65-66; `normalise`, `balanced_pairs.mojo` L47). From (01, 10) under Fibonacci
they have four, three (`fib_bpaStatesNC`, `Descendants.lean` L958) and two
states, and the Lean two-cycle is a Mojo self-loop (`test_quantifier_controls.mojo`
L17-19). Productivity verdicts agree; rows, cycle lengths and strong
connectivity do not, and no Lean statement relates the three yet (W12).

### 15.2 Objects that share a name

| Name | Distinct objects (locators) |
| --- | --- |
| strict set | (M) strict component: SCC of the seed-reachable B_σ, states modulo swap, finite (ms L595); (N) strict system: no strong connectivity, no seed reachability (`c4-cut-pair-productivity-2026-11-04.md` L50-52); (L1) `StrictSystem`, closed under the full child relation (SS L250); (L2) `StrictComponent`, connected up to swap by nonempty paths (SS L703); (L3) `BpaStrictComponent`, swap-closed with states in `bpaStatesNC`, the Lean form of (M) (SS L859); interface `StronglyConnected`, ordered and reflexive, so a loopless singleton qualifies (QI L135); R1 strict support, a closed set, no SCC (`R1SupportCertificate.lean` L142-144); Mojo strict carrier, the Mojo form of (M) (`kernel/psc/carrier.mojo` L8-10); `build_derived_system`, which checks a strict system up to swap although its docstring says component (`kernel/psc/derived_system.mojo` L90) |
| strict zipper | closed nonproductive set of 𝒪_σ vertices with no offset-zero vertex (ms L1022); the census rows of `formal-overlap-carriers-2026-10-04.md` L96 count carriers without an offset-zero vertex, none closed ("closed carriers", L88: 0) |
| overlap | a tile pair of two tilings, vertex of 𝒪_σ (ms L536); physical interval h and internal-space measure v (`physical-mass-refinement-2026-11-08.md` L84, L87); a physically crossing factor (`c4-physical-hub-density-2026-11-04.md` L54-56); potential and realized overlaps are not identified (`physical-mass-kernel-literature-gate-2026-11-08.md` L35-36; ms L929) |
| terminates | with coincidence: (F) ∧ (AE) (ms L291); finiteness only (ms L567, L903; `BPrime.lean` L22-23) |
| coincidence | equal letters at offset zero (ms L536); "boundary coincidence" = offset zero, letters possibly different (ms L955-956); `coincidence_boundaries` returns zero returns (vendored `kernel/substitution_dynamics/balanced_pairs.mojo` L15-16); equal letters at an index (`R1OrderedAncestry.lean` L93-97: index two is a non-cut position) |
| BH | seed-graph form (ML L144) and potential-overlap form (`p1b-boundary-hitting-progress-2026-10-08.md` L113) |
| productive | (E) (ms L291, L857); "one-seed overlap productivity" is (AE) (ML L119); "one-seed productivity" at `class_a_boundary_w_children.mojo` L3 is (E) |
| A1′ | three forms and a fixed-word form (§10, row lemma A) |
| realizable, realized | `G1b2RenewalFiniteness` says "realizable" (ML L104), the manuscript "reachable" (ms L439); "realized" means seed-reachable in `formal-overlap-carriers-2026-10-04.md` L30-31, "realized by pairs of points of X_σ" at ms L302, and whether seed-patch overlaps "can be identified with the overlaps of two tilings in one fibre" is "the earlier form of the question" at ms L929 |
| PDS | of the tiling flow (Ω_σ, ℝ), the conclusion of the imported `thm:bridge` (ms L318) and `thm:bsw` (ms L916-917); of the ℤ-subshift, whose equivalence with the flow statement for irreducible Pisot σ is cited, not proved: `discussed in~\cite{CS,ABBLS}` (ms L321) |
| labels | "Corollary B′", "Theorem A", "Proposition B′", "Corollary B" name different statements in the cut-pair, every-cut-pair and general-structure notes; cite them with the note's name |

### 15.3 Literal versus affine or quotient edges (matrix continued)

| # | Attempted transfer | Class | Lemma or control (layer) |
| --- | --- | --- | --- |
| L1 | aggregate data (P N = M P, rank three, endpoint identities) ⇒ a literal strict system | invalid: exists | ms `sec:synthetic` L1261; `kernel/tests/test_target_packets.mojo` L134-164 (actual children 1, 2, 5 against the template's 1, 1, 3); layer: literal factorization |
| L2 | an affine residual, ancestry or germ cycle ⇒ a literal recurrent cycle | invalid: exists | `tribonacci_locally_admissible_nonzero_period_three`, `tribonacci_nonzero_three_cycle_survives_proper_cut_germs` (`R1Modular.lean` L206, L343); a germ is not an ordered balanced-pair SCC state (L311-314) |
| L3 | a packet edge ⇔ an actual ordered occurrence edge | valid: needs a lemma | a `Psc.GraphRefinement` instance (Complete, SoundEvery, target preservation and reflection) for the packet graph; a reported lead says the projection is Complete and not SoundEvery (`side-notes-ledger.md` L2708), unverified here |
| L4 | a potential overlap, or a box state, ⇒ a seed-reachable vertex of 𝒪_σ | invalid: exists | the census (`formal-overlap-carriers-2026-10-04.md` L81-98); `test_vertex_coincidence.mojo` L90-97 |
| L5 | a T-edge of the pair-overlap graph ⇒ a child edge of B_σ; a T-graph SCC ⇒ a strict component | invalid: exists | the 18-source class (`c4-pair-overlap-class-2026-11-05.md` L42-56): states (letter, letter, offset), not word pairs; each source has images of length at most three and PIP incidence (class note L35-43), so it is a corpus member by definition (ms L1185) with no strict component (`C4StandingCorpus`, finite-domain), while its finite nonempty pair-overlap graph has an SCC: a countermodel by composition with a finite-domain claim |
| L6 | a boundary-hitting certificate on a quotient ⇒ BH on 𝒪_σ | valid: needs a lemma | `cyclicProductive_of_quotient` (`GraphRefinement.lean` L231) needs Complete and SoundEvery; `broken_productive` (L525) refutes it with SoundSome only |
| L7 | the #515 unweighted transpose identity on mixed orbits; the measure normalisation in the set equation | invalid: needed | weights H_i = m_i h_i (`physical-mass-refinement-2026-11-08.md` L126-130); the track-swap quotient is valid for the measure only (`c4-pair-overlap-graph-2026-11-05.md` L115-117) |
| L8 | the naive six-state letter-pair inflation as a sound quotient | invalid: exists | `test_documented_seed_and_naive_pair_negatives` (`test_target_packets.mojo` L209-236); `target-aware-bpa-literature-gate-2026-10-02.md` L36-42 |
| L9 | an edge at one parameter value ⇒ an edge of every family member | invalid: exists | the Y0 LAST/LAST child is CC only at t = 0 (`class-a-boundary-y0-every-child-2026-10-31.md` L104-105; written) |
| L10 | the R1 transport identity ⇒ a literal cut address with a proper digit | valid: proved with the address lemma | `cutAddr_spec`, `cut_defect_transport` (`OccurrenceAddress.lean` L47-81, L145-171; branch `2201a5b`, not on main); `actualCut_prefix_mass_transport` itself takes any offset (`R1Source.lean` L79-88) |
| L11 | a zero source-prefix defect at an interior cut ⇒ the same parent tile | invalid: exists | `c4-cut-attractor-zero-defect-repair-2026-11-05.md` L20-30 |

### 15.4 R1 complete support or rank → canonical Mojo PIP carrier

| Gap | R1 side | Canonical side | Missing typed statement | Control for the untyped version |
| --- | --- | --- | --- | --- |
| T1 source | a supplied `actual : Raw → List Raw` | `Child s` (`fun T => red (subst s T.1) (subst s T.2)`) | `r1_edge_eq_child` (by `rfl`) and fixture agreement; no module imports both `proof/psc_routes` and `PscVerif` | |
| T2 orientation | raw ordered rows | normalised states | `productive_swap`, `terminatesWithCoincidence_swap`, a normalised `bpaGraphN` (W12); ingredient `child_swap` (`Descendants.lean` L436) | `altSubst` (L866): swap changes strong connectivity |
| T3 terminal targets | rows for diagonal states | coincidences terminal | state the bridge on predicates: R1 `Productive` with `actual = red ∘ subst` ⇔ `Psc.StrictSystem.Productive` | Fibonacci: four rows against three states |
| T4 PIP | a packet over any substitution | a specimen of `pip_corpus()` | a producer-side domain declaration | `Binary.actual_strict_support_accepted` (`R1SupportFixtures.lean` L49) with `incidence_has_nonzero_kernel` (`R1ProductivityScope.lean` L107) |
| T5 finiteness | an accepted rank packet with complete rows | `TerminatesWithCoincidence s T₀` | `terminatesWithCoincidence_iff_exists_rankPacket`; finiteness is an input, the packet being the finite closed carrier | `unproductive_iff_closed_target_free_support` allows an infinite witness (`R1SupportCertificate.lean` L66-68) |
| T6 strong connectivity | an accepted strict packet | `StrictSystem` → `StrictComponent` → `BpaStrictComponent` | `strictSystem_of_strictCheck`, then `exists_strictComponent_subset` (SS L2593) and `StrictComponent.toBpa` (`hswap`, `hmeet`) | `carrierC` (row B16) |
| T7 mass and length | `wordMass` over an arbitrary additive `label` (`R1.lean` L189); equal length a separate hypothesis (`equal_length_child_list`, `R1Source.lean` L344; `hlength`, L388) | Parikh prefixes and lengths of `def:bpa` | the basis-labelling instance (`wordMass` = Parikh vector) and the length premise discharged for balanced pairs | `NoAlignedInteriorReturn` (`R1Source.lean` L235) tests k < `topWord.length` only, so its swap needs `hlength` |
| T8 irreducibility | `HasAlignedInteriorReturn`, `NoAlignedInteriorReturn` (`R1Source.lean` L100, L235); Boolean `irreducible` (`R1ProductivityScope.lean` L37) | `IsBlock` (`Reduction.lean` L89); `coincidence_boundaries` (vendored `balanced_pairs.mojo` L15-16) | equivalences of the R1 predicates with each other and with `IsBlock` | none located: no theorem on disk relates them |

All eight gaps need a lemma and none is refuted. No R1 packet is today a C4 input
or a termination certificate for a PIP substitution (PR #520 states the scope:
a supplied `actual`, binary fixtures, no PIP predicate).

### 15.5 C4 → BH and C4 → #138

| Arrow | Source type → target type | Class | Lemma or control |
| --- | --- | --- | --- |
| A ⇒ C4 | ∀ c ≠ c′ a witness (letter pairs) → no finite `StrictSystem`, hence no `BpaStrictComponent` | valid: proved | rows B10, B7 |
| C4 ⇒ #138 | no finite strict system (word pairs) → every letter pair eventually coincident | invalid: needed | row B12; under G1 a composition of manuscript statements (`thm:sink`, `thm:density`(v), (iii), `prop:aligned-overlaps`(i)) made during the synthesis, unreviewed |
| target predicate | diagonal, Sync±, eventually coincident, packet diagonal → C3-local, which needs Sync± at a one-step interior cut | interchange invalid: exists | diagonal ⊂ Sync₊ (m = 0, ms L614) ⊂ eventually coincident, each giving productivity (ms L620, L696); 01/12/021 has a zero return with neither adjacent pair in Sync± (`side-notes-ledger.md` L2234; a side-notes record, the depth-two control is executable, row U12) |
| dictionary | strict component C of B_σ → closed nonproductive set S(C) of 𝒪_σ, case (a) of `prop:zipper-dichotomy`, A₊(S) ⊇ A(C) | valid: needs a lemma | pieces ms L536, L843-852, L857, L863, L1017-1022; 𝒪_σ has no Lean definition |
| BH ⇒ C4 (C3-local) | a cyclic vertex of 𝒪_σ with an offset-zero descendant → a state of C with a Sync± interior zero return | invalid: exists | `fork_without_A` with `fork_strictClosed` (QI L541); every state of a strict system starts with distinct letters at offset zero (`first_letters_ne`, SS L443; ms L978), so its overlaps include offset-zero vertices (ms L857) and lemma B holds there without contradicting strictness; the two-obstruction route uses lemma A |
| C4 ⇒ BH | exclusion of finite strict components → no seed-reachable strict zipper | invalid: needed | only with G1 and through PDS (ms L332-337, L576), circular when BH is wanted for G1; or the derived converse of `prop:G1-from-half-coincidences` (row C11); `loopRay_recurrent_not_closed` |
| A versus A1′ | A1′ (residual hub pair) → lemma A (all pairs) | valid: needs a lemma | Theorem C at σ² (row C7) |
| C4 ∧ (F) ⇒ termination | global C4, finite reachable set, nonerasing → `TerminatesWithCoincidence s T₀` | valid: proved | row B9 |

## 16. Proof and PR crosswalk

States read through the GitHub API on 2026-11-10; "on main" checked with `git
merge-base` against `origin/main` `33a1f6b`; check-run counts from the
check-runs API, logs not opened. No item has been independently reviewed.

| Ref | State | Contributes | Scope | Receipt kind |
| --- | --- | --- | --- | --- |
| #457 | merged 2026-11-02 (merge `0f7f2ca`, on main) | strict-birth atlas: every one-step interior boundary of a supplied complete strict list (`kernel/tests/test_c4_strict_birth_atlas.mojo`) | conditional event completeness on a supplied input; fixture 10/102/211 is outside PIP | reported local Python; hosted at head `6a14362`: 13 of 70 check runs failed (among them mojo-kernel, exact-kernels, python-tests, lean-proofs), completed after the merge; the note on main still says hosted runs had not completed (`c4-strict-birth-atlas-2026-11-02.md` L145-146) |
| #459 | open, unmerged (head `e18c475`) | negative control: strict closure with flat ordered hub words does not force C4 on 10/102/211 | refutes a weakened lemma outside PIP; its test is not on main | reported only; cite at head |
| #460 | merged 2026-11-03 (`4993a59`, on main) | two-generation Parikh-span note and kernel; the rank-three delayed-synchronization control 01/12/021 (row U12) | executable control in PIP; refutes a depth-two reading | hosted at head `38e2b30`: 5 of 73 check runs failed (mojo-kernel, exact-kernels, diagnostic), completed after the merge; the note on main says hosted acceptance "remains to be established" (`c4-two-generation-parikh-span-2026-11-02.md` L534-535) |
| #462 | merged 2026-11-04 (`11017ad`, on main) | conditional integral obstruction: Parikh rank exactly two forces an integer eigenvalue | necessary-condition instrument on a supplied system | reported local Python; hosted at head `43014c5`: mojo-kernel and exact-kernels failed before the merge |
| #497 | open, unmerged (head `0f4b9a05`) | F0-F5, CE1-CE6; 36 null lifted root overlaps for twelve sources | finite domain; exclusion of supplied strict systems through written M1; its notes and kernels are not on main | reported; one hosted SCC run passed at the original head, others failed on an evidence-pin assertion (PR body) |
| #499 | merged 2026-11-05 (`ba09fdb`, on main) | nodes `C4FromStrongCoincidence` (proved), `C4StandingCorpus` (finite-domain); `C4` re-filed conditional on #138; cut-attractor Lemmas F, N, G, Propositions 1-3, R | as the governed statuses | reported local; hosted at head `8d97d7d`: python-tests and exact-kernels failed after the merge |
| #504 | merged 2026-11-06 (`873316d`, on main) | Proposition Q(b), Theorems R2/R3, Proposition B′, Corollary B (general-structure note) | off the Pisot cone; not governed claims | reported; hosted at head `e9cfafe`: python-tests and exact-kernels failed |
| #515 | merged 2026-11-08 into the #497 branch, not into main (head `51dd090`) | physical mass loss on the twelve overlap graphs: a losing row in every inverse source SCC | finite certificate; consumes the supersolution "as supplied in equality form by the parent proof" | reported; on main only as a pinned revision |
| #519 | merged 2026-11-08 (`a751029`, on main) | `PscVerif.PhysicalMass`, bounded Quint model, source binding of the #515 packet | universal over supplied matrices; no instance | hosted run 42468257407 at the exact head, three dedicated jobs passed; "scoped kernel/refinement acceptance, not complete branch acceptance" (PR body); the Quint and source-binding gates run only in `.github/workflows/physical-mass-kernel.yml`, and `tools/verify_all.sh` has no line for them |
| #520 | merged 2026-11-08 (`4ae8733`, on main; merge tree differs from the head tree, not under `proof/psc_routes`) | R1 support, rank and rank-witness checkers with Quint mutants | a supplied `actual`; binary fixtures; standalone modules outside the proof bank | hosted runs at the tested head; "not a newly compiled merge-SHA receipt" (PR body) |
| #521 | merged 2026-11-09 (`c15d0e3`, on main) | Lean `StrictSystem` (Theorem A(1)-(5), strict components, `thm:sink` with `hfin`), `Descendants`, reductio register | implications conditional on witnesses, finiteness or a hypothetical component | hosted at head `b29766d`: 79 of 81 runs succeeded, 2 cancelled duplicates; mojo-kernel and exact-kernels completed after the merge on the identical tree |
| #461 | open issue | successor target of #9: a theorem uniform in the number of states on a supplied finite strict SCC, or a reproducible negative | "not global G1 extraction from an arbitrary failure" | none |
| #9; #84, #138, #139 | #9 closed for routing; the three trackers open, reopened | statements of the targets | routing only | none |

The branch commits that carry Part I and its Lean modules (`a95588a`,
`e7853fb`, `4a22b96`, `9338b7a`, `2201a5b`) are not on `main`; their receipts
are local (§8), and no hosted CI was queried for them.

## 17. Findings and dispositions

Dispositions: **corrected** (only Part I §3 and the ledger repair of §6);
**dated correction**, proposed and not applied (a dated paragraph at a stated
anchor; no manuscript, vendored file, generated surface or digest pin is
touched); **record** (no edit now); **owner** decision.

| # | Surface | Defect | Disposition |
| --- | --- | --- | --- |
| X1 | `proof-ladder.md`, "The C4 chain" | (F) dropped on C2 ⇒ SCC Producer | corrected (Part I §3) |
| X2 | `conjecture-ledger.md` §E | same | corrected (Part I §3) |
| X3 | `c4-finite-domain-closure-2026-11-05.md` §1 | same | corrected (Part I §3) |
| X4 | ML record `PDS`; sets `G1AndProducer`, `G1AndC4` | imported antecedent not named | corrected in `e7853fb` (Part I §6) |
| D1 | `README.llm.txt` L93 (and L111) | the #84 premise printed as (E) at a seed; "appropriate" undefined | owner: the file is outside `docs/` and carries the owner's addendum, so no dated correction is proposed; the exact wording is `README.md` L33 and §10 |
| D2 | `README.llm.txt` L107-108 | BH mixes the positive and the exclusion form; "relevant" undefined | owner (as D1); canonical wording in §10 |
| D3 | `proof-ladder.md` L86; `conjecture-ledger.md` L37-38; `completion-ledger-2026-11-02.md` L21, L129; `project-onboarding-2026-10-23.md` L46; `current-proof-architecture-2026-09-14.md` L53; `direct-attack-frontier-2026-10-23.md` L41; `issue-139-tracker-mathematics-reconciliation-2026-10-23.md` L31, L36 | the hybrid BH wording; a "seed-reachable strict-zipper overlap graph" is defined nowhere | dated correction per file, pointing to the canonical wordings of §10 |
| D4 | `direct-attack-frontier-2026-10-23.md` L21, L25-26, L39; `proof-ladder.md` L87 | "[proved assembly]" and "[PROVED assembly]" read as the status of #84 (outside the vocabulary, bound to no claim); "exactly" prints an implication as an equivalence; "**one** swap seed productive" is (E)-shaped | dated correction |
| D5 | `claim-status-and-source-map-2026-09-13.md` L98 | an all-vertex consequence (two-sided strong coincidence) in the one-seed row | dated note below the table |
| D6 | `p1b-boundary-hitting-progress-2026-10-08.md` L113; `bpa-termination-by-overlap-depth-2026-10-02.md` L216-217 | "BH" there is the potential-overlap form, a different universe | dated clarification |
| D7 | `c4-cut-pair-productivity-2026-11-04.md` L312-316, L178; `c4-prefix-subtile-convention-literature-gate-2026-11-04.md` L69 | "disjoint" written for measure-disjoint; "Corollary B′ (productivity from disjointness)" concludes non-existence of finite strict systems, and the label collides with three others | dated correction and gloss |
| D8 | `c4-finite-domain-closure-2026-11-05.md` L34-36, L64-81, L110-112 | "exactly" drops seed reachability and side swap; "vacuously" omits the stronger statement the witnesses give; an empty-interior statement on unwitnessed pairs is called "#138 itself", though #138 implies it | dated corrections at three anchors |
| D9 | `physical-mass-kernel-2026-11-08.md` L204-210, L220-225; `physical-mass-refinement-2026-11-08.md` L296-298; `side-notes-ledger.md` L2421 | the domain of the "next condition" is ambiguous (three-root carrier of a source, or carrier of a supplied strict system); a newborn "from" nullity conflates two output types | dated clarification (beneath the side-notes entry); the interface choice is O24 |
| D10 | `c4-pair-overlap-class-2026-11-05.md` L49-53 | "unrestricted" is exact for finite sets only; the exclusion adds no source to `C4StandingCorpus` | dated note |
| D11 | `c4-cut-attractor-window-2026-11-05.md` L258-259, L318; `c4-finite-domain-closure-2026-11-05.md` L94 | Proposition 3 stated "for primitive σ", but (ii) ⇒ (i) uses Lemma F(b), stated for irreducible χ_M (L27) | dated correction in both notes |
| D12 | `research-roadmap-2026-09-21.md` L18-28; `README.llm.txt` L43 | the REUSE list mixes open PRs (#459, #497) and #515 (merged into the #497 branch) with PRs on main | dated line under the roadmap table; `README.llm.txt` is the owner's |
| D13 | `c4-strict-birth-atlas-2026-11-02.md` L145-146; `c4-complete-cone-rank-hub-audit-2026-11-03.md` L203-204; `c4-two-generation-parikh-span-2026-11-02.md` L534-535 | hosted acceptance described as pending; hosted runs at the heads of #457, #460 and #462 include failed canonical jobs (§16) | dated receipt line, only after the logs are classified (W19) |
| D14 | `formal-overlap-carriers-2026-10-04.md` L96, L104-106 | its "strict zipper" is a carrier without an offset-zero vertex and is not closed; "realized" means seed-reachable | dated note |
| D15 | `verification-architecture.md` L112-117 | C2 ⇒ SCCProducer printed without G1, and G1 + SCCProducer ⇒ PDS without the imported criterion | dated correction |
| D16 | this note, Part I §3 ("With (F), the three exclusion forms agree"; "What C4 takes as input"), §4 (last paragraph), §5 | the (AE°) ⇒ (AE) leg needs nonerasure and has no Lean form on `bpaGraph`; the witness of (X) and `BpaStrictComponent` are different types; N1 and N2 not separated; one sense of uniformity, the valid swap and literal instances not named | addressed by rows B3, B6, §12, §13 and W1, W2; Part I kept |
| R1 | ms L150-151; L141-142; L81-82, L199-207; L1073 with L294-295; L836 | "every swap seed is productive" abbreviates the all-vertex conclusion; an "Equivalently" in undefined terms, no proof located (unverified); stale class-D "proving ground"; the path-end identity is false on B_σ, only the inclusion is used; "uniformly in" the size of C | record (manuscript revision; readings fixed in §10) |
| R2 | `R1OrderedAncestry.lean` L81-86; `proof/quint/PscR1OrderedAncestry.qnt` L71-74; `R1Source.lean` L8-9 | the withdrawn (E) ⇒ (AE) reason survives; "positions zero and two" (two is not a cut); "proper" is not a hypothesis of the transport identity | record; comment-only repair (W20) |
| R3 | SS L199-200, L2500-2501; SS L2606-2610 | an extraction step labelled "that is C4"; the extraction conclusion drops reachability from T₀ | record; read as the converse of `C4FromStrongCoincidence`; reachability-carrying variants (W2) |
| R4 | `kernel/psc/class_a_boundary_w_children.mojo` L3; `README.llm.txt` L93-94; `kernel/psc/derived_system.mojo` L90; vendored `balanced_pairs.mojo` L15-16 | "one-seed productivity" used for (E); a validator of strict systems whose docstring says component; `coincidence_boundaries` returns zero returns | record; glossary of §10; the vendored docstring only upstream |
| R5 | `proof/tla/MCNonProductive.tla` L3-4 | wrong reason: χ_M = x(x − 2)(x + 1) has no root of modulus > 1 besides 2 (ms L1245) | record; side-notes entry (W20) |
| O1 | `README.md` L48 | hybrid BH on the front page | owner |
| O2 | CG L1648; ML L350; title of #84 | the alias "Open Problem 5.35" names the all-vertex problem on the one-seed node | owner |
| O3 | ML L131; ML L215 | `AllStatesProductiveViaOverlaps`: conclusion not scoped to the seed; `C4FromStrongCoincidence` worded existentially | owner |
| O4 | ML L125-128, L144; `MCLedgerTwoObstructionsAssumed` | BH and all-seed strict-zipper exclusion are independent gates; "BH alone ⇒ G1" (`direct-attack-frontier-2026-10-23.md` L29) is no edge | owner |
| O5 | ML L146-148 | `TwoObstructionCompletion` has no dependents; the models under-derive | owner |
| O6 | ML L222-223 | `SCCProducer` models only the route through G1 | owner |
| O7 | PR #281 body; #84 banner; #139 body; ML L142 | A1′ per substitution; "#84 = A1′ ∧ BH"; hybrid BH; three strengths travel under #138 | owner (tracker comments linking §10) |
| O8 | `research-roadmap-2026-09-21.md` L191-193 | hybrid BH and the undefined "reverse offset-zero basin" | owner |
| O9 | ML L32 | one Scope string for every record | owner |
| O10 | `docs/ledger-index.md` L49 (from ML L102); `conjecture-ledger.md` L13 | "uniformly bounded" with no index | owner |
| O11 | `claim-status-and-source-map-2026-09-13.md` L92; ML L218 | "General C4 is equivalent to bounded-gap A1′" drops "for every power of σ" and reads universally | owner |
| O12 | `README.md` L78; `research-roadmap-2026-09-21.md` L155-157; `claim-status-and-source-map-2026-09-13.md` L64 | the class-A depth bound printed without its own scope and status | owner |
| O13 | ML L213, L326 | `PDSSpectralRoute` omits the imported `thm:bridge` (§14.2) | owner |
| O14 | ML L87 | `GlobalEndpointSync` cites `c4-barge-diamond-endpoint-eliminator.md` (endpoint type G); its statement and dependency are Proposition 2 of `c4-endpoint-core-program.md` (L99-118) and ms `thm:global-sync` (L623) | owner |
| O15 | ML L236-238; ML L61 | `PeriodicPairOneFibre`, `DefectTheorem`: imports not nodes (§14.2) | owner |
| O16 | `docs/ledger-index.md` L32; ML L129-130; CG L2034-2035; CG L144 | `CoincidenceDensityOne` "Repository-proved" with an incomplete closure; two encodings of "A implies B" (§14); `settled_classes` contains "conditional" | owner |
| O17 | `tools/proof_records/records.py` L161; ML L483; ML L43 | `proof_reviewed` is a schema field, not a review; `REVIEWED` says "independently reviewed" | owner (the first upstream) |
| O18 | ML L230 | `StandardBPAEquivalence` imports one direction | owner |
| O19 | `kernel/tests/test_renewal.mojo` L142 and six more | `require_claim` on the open `G1b2RenewalFiniteness` | owner |
| O20 | `README.llm.txt` L5; issues #9, #84, #138, #139 | tracker states read as closure | owner (tracker) |
| O21 | ML L104; ML L240 | "realizable" where the manuscript says "reachable"; `StrictZipperPeriodicPairForm` drops the reachability clause of its source | owner |
| O22 | ms L955-956; alias of `BoundaryCoincidenceCriterion` | "boundary coincidence" names a boundary hit | owner |
| O23 | ML L205-206 | `ConcentrationAuxB` carries the extraction premises | owner |
| O24 | `physical-mass-kernel-2026-11-08.md` L220-228; `c4-pair-overlap-class-2026-11-05.md` L53-55 | the output type of the mass interface to C4 (§12.2) | owner |
| O25 | `proof/psc_routes` and `PscVerif` | where an R1 binding module lives; whether R1 joins the proof bank | owner |

## 18. Work items, mapped to the immediate sequence

Steps of the roadmap's "Immediate sequence" (`research-roadmap-2026-09-21.md`
L65-69): (1) quantifier audit and countermodels; (2) packet square; (3) hub-word
invariant; (4) uniformization; (5) synthesis across mass, R1, C4 and BH.
Priority order; S, M are sizes.

| # | Step | Item | Size | Unblocks |
| --- | --- | --- | --- | --- |
| W1 | (1) | Lean: `NonTerminal` relative to the reachable set in `hereditarilyProductive_of_cyclic_of_finite` and `two_obstruction_skeleton`; `bpaGraph_child_of_reach` for nonerasing σ; `SccProducerAt`; `terminates_of_finite_of_sccProducer` | S | B3, D16 |
| W2 | (1) | Lean: `exists_bpaStrictComponent_below` (reachability carried), `terminatesWithCoincidence_iff_finite_and_no_component`, `bpaStrictComponent_of_stronglyConnected` and its converse, `no_bpaStrictComponent_of_no_strictSystem` | M | B6, B7, D16, R3 |
| W3 | (1) | Lean: `productive_of_strongCoincidence` with no finiteness, its (AE) and no-strict-closed corollaries, `exists_level_of_strongCoincidence` | M | B11 |
| W4 | (1) | Lean: boundary hitting as an instance (`boundaryHitting_iff_no_zeroFree_closed`, `reaches_of_cyclic_reaches_of_finite`) and the rooted `two_obstruction_iff` | S | C8, C9 |
| W5 | (1) | Lean: `Steps`, `ProductiveWithin`, `exists_depth_of_hereditarilyProductive_of_finite`; selected-rank and all-edge-rank lemmas, `productiveWithin_of_rank` | S | U1, U5, D16 |
| W6 | (1) | Lean countermodels: `stem`, `carrier_seed_fork` (10/102/211), `drip`, `forkMass`, `fibMass`, `comb_uniform_depth_not_finite`, `chain_bounded_subfamily`, `chain_no_uniform_productive_depth`, `idSubst` | S | A1, A10, B8, Z14, U5 |
| W7 | (1) | Lean: `MassGraph.nullStrict_of_hereditarilyProductive_of_finite`; `MassGraph` over an ordered field | M | §12 (N1) |
| W8 | (1) | Mojo controls, `require_contract`: 10/102/211 seed rows and Fibonacci/Thue-Morse factor counts in `test_quantifier_controls.mojo`; the class-A literal `chain_not_uniform`; the level cap on the plastic reversal; the origin witness of 1/021/001 | S | A1, Z1, U2, U11 |
| W9 | (1) | Quint bounded replays (`QuantifierReadings.qnt`, `NullStrictMass.qnt`, `FiniteVsUniform.qnt`), test names ending in `Test`, mutants that must fail | S | independent replay |
| W10 | (1) | apply the dated corrections D3-D15 with their side-notes entries; regenerate the proof bank if an opening moves | S | §17 |
| W11 | (1) | ledger: `PDSSpectralRoute` gets `StandardBPAEquivalence`, added to `SpectralGateAssumed` (O13); a regression that every established PDS record has an imported record in its closure | S | §14.2 |
| W12 | (2) | convention lemmas (truncation invariance, `productive_iff_exists_coincident_factor`, side-swap refinement `bpaGraphN`), a Mojo conventions test and a Quint model; a `Psc.GraphRefinement` instance for the packet graph with Complete and SoundEvery separate; on 1/02/202, which disjunct of `inevMax_iff_of_finite` fails | M | A7, L3, §15.1, T2, T3 |
| W13 | (3) | Lean types `SyncPlus`, `SyncMinus`, `C3Local`, so that the vacuity of C4 on a domain is a statement about one type | M | §15.5 |
| W14 | (4) | Lean: `exists_depth_of_inevitable_of_finitelyBranching` with the control `star`; compactness across a family with closed limits | M | §13.1, depth in one graph |
| W15 | (5) | mass glue: `forwardGraph` with `sourceLoss_iff_forall_hereditarilyProductive`; `sum_occurrences_eq_action`, `null_of_cover_of_source_loss`; `no_strictSystem_of_null_cutPairs`, `terminates_of_no_strictSystem`; `length_le_maxLen_mul_blocks`; Lean leave-one-out controls of `PhysicalMass` | S-M | i.1, i.2, i.5, Z12 |
| W16 | (5) | R1 binding (after O25): `r1_productive_iff`, `r1_edge_eq_child`, `strictSystem_of_strictCheck`, `terminatesWithCoincidence_iff_exists_rankPacket`, irreducibility equivalences, `terminatesWithCoincidence_of_rank`; Mojo admission of R1 packets on fixtures | M | T1-T6 |
| W17 | (5) | note with a literature check: the converse of `prop:G1-from-half-coincidences` (G1 ⇒ rooted lemma B), the dictionary C ↦ S(C), and whether under G1 lemma A ⇔ no strict component | M | C11, §15.5 |
| W18 | (5) | owner decisions on ledger and status surfaces (O2-O6, O9-O11, O14-O23) | M | §14 |
| W19 | (5) | open the failing job logs at heads `6a14362`, `43014c5`, `8d97d7d`, `e9cfafe` and `38e2b30` (#460; its check runs were read, §16), then D13 | S | D13 |
| W20 | (5) | record items: comment-only repair of R2 in a PR touching those paths; side-notes entries for R5 and the PR states of §16 | S | R2, R5 |

## 19. Non-claims and limits of Part II

- Part II proves nothing, moves no status and adds no ledger claim; it does not
  close or advance C4, G1, #84, #138, #139 or PSC. A row "valid: proved" names
  where the implication has its proof; it never supplies the antecedent.
- The six route maps (at `c5ed4e5`; their readers executed nothing) are leads.
  Every topic entry behind these rows was re-opened at its locator in an
  adversarial verification at `2201a5b` (quotes matched mechanically, Lean
  declaration lines checked, statuses read from CG with `tomllib`, PR and issue
  states read through the GitHub API on 2026-11-10); the writer re-opened the
  load-bearing locators and re-read PRs #459, #497 and #515.
- No Lean, Mojo, Quint, TLC or pytest replay was made for Part II and no hosted
  CI was triggered; only the documentation checks of this file were run.
  Hosted check-run counts are as the API reports them; no job log was opened,
  so no failure cause is known. Private scratch scripts (a `pip_corpus()`
  membership check, the 10/102/211 seed rows) are not oracles and not evidence.
- Unreviewed derivations of the synthesis: the converse of
  `prop:G1-from-half-coincidences` (row C11), "under G1, lemma A ⇔ no strict
  component" (§15.5) and the 10/102/211 seed rows (W6, W8). The Lean statements
  of §18 are work to be done, each with its proof and, for a new diagnostic,
  the literature gate of `AGENTS.md`. Independent human review is pending.
- A completeness and accuracy pass at `2201a5b` (this revision) re-opened more
  than 250 locators of Part II (Lean declaration lines in QI, QB, SS and
  twelve other modules, manuscript lines, `tools/make_ledger.py`,
  `claim_governance.toml`, notes, tests, PR and issue states, and check runs at
  six heads through the GitHub REST API). Four locators or quotes were wrong
  (ms L302, `c4-finite-domain-closure-2026-11-05.md` L52-54 for vacuity,
  `class-d-g1-corollary-2026-10-22.md` L143 for the formula,
  `automaton.mojo` L3-5) and one R1 lemma was read as an (AE) theorem (row
  A3); all are corrected in place. The pass marked the form of
  every control that is only written or only on a branch, added rows B19,
  B20, U15, T7, T8, the PDS row of §15.2 and the leave-one-out and proof-bank
  rows of §§14, 14.1, and mapped every route-map hazard to rows (§20). It ran
  no Lean, Mojo, Quint or TLC.

## 20. Coverage of the route-map hazards

Every entry of the field `quantifier_hazards` of the six route maps (session
scratch at `c5ed4e5`, not in the repository; `Hn` is the entry n, counted
from 0) is listed with the rows that treat it. None is out of scope.

| Route map | Hazard → rows |
| --- | --- |
| C4 interface (20) | H0 C3-local existential, strictness universal, vacuity is not a newborn → §14 (`C4` row), §12.2 (output type), B18; H1 (E) is not (A), no forward transport → A1, A5; H2 packet item 1 versus item 2, omitted split descendants → A7, A11; H3 (F) dropped on the C4 chain → X1-X3, B1; H4 three domains of "strict" → §15.2, B6-B8; H5 finiteness inside every strict object → §10 (C4 wording, `thm:BD` row), B11, U10; H6 null, empty, empty interior → §12, Z1, Z7; H7 Theorem B versus Lemma G(2) → Z5; H8 non-unit transfers → Z7, Z8; H9 finite-domain scope, the `−1` decision → §13.2, U15; H10 C4 conditional, `ProvedDef` → §14, §14.1; H11 one Barge-Diamond pair, mask, first-child phase → B13, B19; H12 existential wording of `C4FromStrongCoincidence` → §10, O3; H13 forms of A1′ → §10, C7, §15.5, O11; H14 Proposition 3 hypothesis, common vertex versus balanced cut → D11, C13; H15 affine, quotient and reductio-level edges → L1, L2, B18; H16 `thm:towers` legality → B20; H17 "termination" and B′ labels → §15.2, B17; H18 two routes to SCC Producer → B11, O6; H19 `PDS` without its import → X4, §14.2 |
| direct route (18) | H0 (E)-shaped #84 → §10, D1, D4; H1 one seed, all seeds, all vertices; the alias → §10, C3, C16, O2; H2 one seed ⇔ every seed only through PDS → C3; H3 BH is ∀ cyclic ∃ path → C9, C14, A10; H4 hybrid BH, "relevant" → §10, D2, D3, O1; H5 boundary hit versus coincidence → C13, §15.2; H6 A versus A1′ → C7; H7 three strengths of #138 → §10, O7; H8 status surfaces → §14.1, C15; H9 the TLA ledger is bookkeeping, "BH alone ⇒ G1" → §14.1, O4; H10 density one leaves a null nonempty complement → §12; H11 finite versus uniform, one Scope string → §13, §14.1, O9; H12 type edges versus occurrence edges → L4, L6; H13 seed-reachable, potential, realized overlaps → C12, L4, §15.2; H14 first-choice exit → A10; H15 ternary scope → U13; H16 flow versus subshift → §15.2 (PDS); H17 tracker states → §14.1, O20 |
| mass (18) | H0 kernel over supplied matrices → §13.2, §14; H1 finite evidence and caps → §13.2, U14; H2 quantifiers of `SourceLoss` → §10, Z12; H3 its orientation → §10; H4 some pair versus every pair → Z5, Z6, i.5; H5 null, empty, empty interior, small bound → §12, Z1; H6 lifted versus Euclidean → Z7; H7 Lean arguments are not instances → §14, i.1; H8 inequality versus equality → Z11; H9 T-edge versus BPA edge → i.3, i.4, L5; H10 three meanings of "overlap" → §15.2, Z4; H11 vacuous exclusion versus exhibited witness → §12.2, i.6, i.7; H12 no strict system gives no termination without (F) → Z15, B1; H13 root inventory → §12.1; H14 orbit weights → L7; H15 merged into a branch versus on main → §16, D12; H16 scoped CI → §16 (#519); H17 output type of the bridge → §12.2, O24, D9 |
| R1 (16) | H0 one lower-ranked child → A8, A9; H1 root versus descendants → A1, A2; H2 stale withdrawn reason → R2; H3 equal letter at an index → §15.2, C13; H4 R1 antecedents → §14; H5 affine or germ cycles → L2; H6 properness not a hypothesis → L10, R2; H7 mass, Parikh, length → T7; H8 irreducibility predicates → T8; H9 "strict" objects → §15.2; H10 bounded fixtures → §13.2; H11 finiteness is an input → T5; H12 density or mean versus hit → Z9, A5; H13 raw versus normalised edges → §15.1, T2, T3; H14 receipt scope → §16 (#520); H15 binary-only Quint → §13.2 |
| G1 (21) | H0 one seed versus every seed → C3, C10; H1 (A) false in the class → A5; H2 per-σ finiteness → §13.1, U2, U8; H3 finite overlap types → U6; H4 bounded box → U6; H5 "realizable" → §15.2, O21; H6 conditional G1 routes → §14, C15; H7 extraction needs (F) → B1, B12, Part I §3; H8 supplied versus extracted component → §13.1; H9 `lem:descendants` → A13; H10 "terminates" → B17, §15.2; H11 offset zero versus coincidence → C13; H12 four universes → C12, L4, §15.2; H13 type versus template edges → U3, L4; H14 measure versus emptiness → §12; H15 cap versus verdict → U11, §13.2; H16 meanings of "strict" → §15.2; H17 one-way import → §14.1, O18; H18 one Scope string → §14.1, O9; H19 Lean statement shapes, proof-bank coverage → R3, §10, §14.1; H20 `require_claim` is a link → §14.1, O19 |
| controls (18) | H0 (A)-shaped interfaces → A5; H1 forward transport → A1; H2 shortest depth versus every lineage → A7; H3 packet SCC versus strict SCC → A7; H4 selected path promoted to a carrier → A9, A10; H5 all-edge descent versus existential BH → A8, C14; H6 closed-SCC exclusion without (F) → B1, X1-X3; H7 closed components versus strict cycles → A6; H8 C4 supplies its own input → B12, Part I §3; H9 conditional read as antecedent, reductio vacuity → C6, B18, §14; H10 leave-one-out read as necessity → §14; H11 null mass read as (A) or empty, losing sinks → Z2, Z3, Z12; H12 finite read as uniform → §13, U2, U12; H13 budget read as verdict → U11; H14 affine and quotient edges → L1, L8, L11, A13; H15 necessary condition read as certificate → B19, U12; H16 "terminates" in Proposition B′ → §15.2; H17 control scope read as PIP evidence → §11 (form and scope of controls) |
