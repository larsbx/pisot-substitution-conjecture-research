# The reductio lemmas of the C4 attack: a register — 2026-11-07

**Status:** register of existing results; no new mathematics beyond what the
named Lean declarations prove. Every Lean name below is in the `PscVerif`
library (`proof/PscVerif`, root `PscVerif.lean`), which passes the proof-bank
axiom audit (`propext`, `Classical.choice`, `Quot.sound` only). Claim
statuses stay with `claim_governance.toml`; this note adds and promotes no
claim. Human review pending. Integrated 2026-11-09.

Sources: manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`
(`def:bpa`, `thm:parikh` line 601, `prop:cocycle` line 705,
`thm:defect-intertwiner` line 721, `thm:deg23` line 728, `thm:sieve` line 740,
`thm:sink` line 588, `prob:C4`, `comp:defect` line 1200); the
[cut-pair note](c4-cut-pair-productivity-2026-11-04.md) §2 (Theorem A, strict
systems); the [finite-domain closure](c4-finite-domain-closure-2026-11-05.md)
§3 (`C4StandingCorpus`); the [concentration attack](c4-concentration-attack-2026-11-06.md)
§§2, 8; the [solidify stop/go gate](c4-solidify-stop-go-2026-11-07.md) §5 (the
leave-one-out request); the [closed-component search](c4-closed-component-search-2026-11-07.md).

## 0. What a reductio lemma is here

A **reductio lemma** is a Lean theorem whose hypotheses describe a
hypothetical strict component: a normalised child system
(`Psc.Binomial.ChildSystem`, `Psc.SignedCocycle.Normalisation`) over three
letters with balanced states, a prescribed vanishing of the lower defects, a
nonzero defect column, and substitution-level hypotheses (`χ_M` irreducible,
primitivity, a Pisot root). No known object meets every hypothesis, and the
lemmas are used as necessary conditions, never as facts about a known
component.

Two levels are kept apart throughout.

- **`ChildSystem` level.** The original statements in `Psc.KernelCofactor`,
  `Psc.Degree2Sector`, `Psc.SectorBridge`, `Psc.Degree3Sector`,
  `Psc.Degree4Floor`. A `ChildSystem` takes any balanced factorization as
  children, so these statements cover more than strict systems.
- **`StrictSystem` / `StrictComponent` level** (`Psc.StrictSystem`). A strict
  system is a finite nonempty set of irreducible noncoincident balanced
  blocks closed under the zero-return factorization `red`; a strict component
  is a strongly connected one. Here every structural hypothesis is
  discharged for **every** normalisation `P` of the zero-return child system
  of the swap closure (`StrictSystem.swapSystem`): nonerasure
  (`nonerasing_of_irreducible`), balance, `∼₂`, `∼₃`, `C ≠ ∅`, the nonzero
  defect column at the first defect degree (`defectDegree`,
  `exists_rep_kw_of_two`, `_k3_of_three`, `_k4_of_four`), strong connectivity
  (`StrictComponent.nrep_stronglyConnected`), the Perron data and the root
  bound. Only substitution-level hypotheses remain.

## 1. The register

`Irr`: `χ_M` irreducible over `ℚ`. `Prim`: `M^k > 0`. `Pisot(β)`: `χ_M(β) = 0`
and every other complex root has modulus `< 1` (with `1 < ‖β‖` where stated).
`r`: the first defect degree (`Psc.StrictSystem.defectDegree`). `N_C = A + B`,
`S = A − B` on the representatives.

| Family | `ChildSystem`-level statements | `ChildSystem`-level hypotheses | `StrictSystem` / `StrictComponent` restatement |
| --- | --- | --- | --- |
| `thm:parikh` cofactor, Theorem A(iv) | `Psc.KernelCofactor.charpoly_nrep_eq_mul`, `cofactor_int`, `isCoprime_rep`, `rootMultiplicity_rep`, `simple_perron_root_rep`, `factor_through_rep` | a normalisation over `Fin 3`; every state `∼₁` (`hbal`); `C ≠ ∅` (`hC`); `N_C` strongly connected (`hSC`); `Irr` (`hM`); `ℓ > 0` with `ℓM = βℓ` | `Psc.StrictSystem.StrictComponent.kernel_cofactor` (`Prim`, `Irr`; any `r`) |
| `thm:deg23` (ii) | `Psc.Degree2Sector.rank_q2`, `charpoly_wedge2_dvd_ssign`, `charpoly_wedge2_dvd_ssign_int`, `lcm_dvd_nrep_mod_two`, `card_rep_ge_natDegree_lcm`, `card_rep_ge_six` | a normalisation over `Fin 3`; every state `∼₁`; some representative with `kw ≠ 0`; `Irr` | `Psc.StrictSystem.StrictSystem.deg2_sector` (`Irr`, `r = 2`); `StrictComponent.deg2_sector`; `StrictSystem.three_le_card_rep`, `three_le_card`, `lcm_le_card` |
| weights of `q₃`, `q₄` | `Psc.SectorBridge.exists_weight_root_q3`, `exists_weight_root_q4` | a normalisation over `Fin 3`; `∼₂` (resp. `∼₃`) states; a nonzero `K₃` (resp. `K₄`) column; `Irr` | none directly; their consumers below |
| `thm:deg23` (iii) | `Psc.Degree3Sector.root_q3_eq_det`, `q3_eq_pow`, `range_q3m_le_ker`, `rank_q3_le_two`, `deg23_iii`, `deg23_iii_of_ne`, `deg23_iii_of_perron`, `deg23_iii_of_primitive` | a normalisation over `Fin 3`; `∼₂` states; (`_of_ne`) a nonzero `K₃` column; `Irr` with roots `β, α, γ`, `‖α‖, ‖γ‖ < 1`; the root bound on `χ_S`, or a positive left eigenvector, or `Prim` | `Psc.StrictSystem.StrictSystem.deg23_iii` (`Prim`, `Irr`, `Pisot(β)`, `r = 3`); `StrictComponent.deg23_iii` |
| `thm:sieve` at `r = 4`, Theorem A(i)–(iii) | `Psc.Degree4Floor.sieve4`, `sieve4_roots`, `sieve4_pisot`, `sieve4_of_primitive`, `no_220_root`, `sieve4_211`, `gauge_of_sieve4`, `gauge_or_antiGauge_of_sieve4`, `theoremA_of_primitive` | a normalisation over `Fin 3`; `∼₃` states; a nonzero `K₄` column; `Irr` with a Pisot root; the root bound `hρ` (or `Prim`); `N_C` strongly connected for the Wielandt clauses | `Psc.StrictSystem.StrictSystem.sieve4` (`Prim`, `Irr`, `Pisot(β)`, `1 < ‖β‖`, `r = 4`); `StrictComponent.theoremA`, `StrictComponent.gauge_or_antiGauge`, `StrictComponent.closed_walk_sign`; `StrictComponent.sieve4` |

The restatements hold for every normalisation of the swap system, and the
component-level ones apply to every finite counterexample to seeded
termination of the balanced pair algorithm: such a seed yields a strict
system (`Psc.StrictSystem.exists_strictSystem_of_not_terminates`) and, for
nonerasing `σ`, a strict component of `B_σ`
(`exists_bpaStrictComponent_of_not_terminates`; `thm:sink` with G1 as a
hypothesis, `exists_bpaStrictComponent_of_finite`), of first defect degree at
least that of the system (`StrictSystem.defectDegree_le_of_subset`). A failure
of strong coincidence is **not** known to yield a strict system; that is C4.

## 2. Contrapositive exclusions with bite

The exclusion forms (`Psc.StrictSystem`). Each also assumes the substitution-level
hypotheses of the theorem it contraposes (`M` primitive, `χ_M` irreducible, and a Pisot
root for `r = 3, 4`; see the Lean statements), and the distinguishing condition below:

- `no_strictSystem_deg2_of_card_lt` (`r = 2`, `|R| < deg lcm(χ_M, χ_{Λ²M}) mod 2`),
  `no_strictSystem_deg2_odd` (`r = 2`, fewer than `6` states up to swap, `det M`
  odd, `tr M ≢ tr Λ²M mod 2`);
- `no_strictSystem_deg3_of_not_eigen` (`r = 3` and a state with
  `M^{⊗3}K₃(T) ≠ det M · K₃(T)`);
- `no_strictSystem_deg4_of_abs_det_ne_one` (`r = 4`, `|det M| ≠ 1`);
- `no_strictComponent_deg4_of_hasBothSigns` (`r = 4`, a state with a child in
  both orientations).

Where an exclusion has bite, it is at the `ChildSystem` level:

| Exclusion | Lean | What it excludes |
| --- | --- | --- |
| the 24 degree-three catalogue occurrences | `Psc.Degree3Catalogue.catalogue_spec` (field `not_mem`), with `occurrences_spec`, `catalogue_exact`, `catalogue_card`, `no_closed_equiv2` | each occurrence `(σ, T)` lies in **no** `∼₂` child system over `σ` that has a normalisation (contrapositive of `deg23_iii_of_primitive`, step (c)); over each of the 12 automata no nonempty child-closed coincidence-free `∼₂` set exists (by leakage) |
| the census state over `011/2/120` | `Psc.Degree3Sector.census_not_mem` | the same for one state, the first instance |
| `M0`, `det = −2` | `Psc.Degree4Floor.m0_no_degree4` | no normalised child system over `m0Subst` with `∼₃` states has a nonzero `K₄` column (contrapositive of `sieve4_of_primitive`) |

At the strict-system level these exclusions are **redundant with Theorem
A(4)** on every specimen where their extra hypotheses are known to hold:
`Psc.StrictSystem.census_vacuous` and `m0_no_strictSystem` show that
`011/2/120` and `m0Subst` carry no strict system at all, and the controls
`no_strictSystem_deg2_odd_control` (plastic), `no_strictSystem_deg3_control`
(the census state over `011/2/120`), `no_strictSystem_deg4_control`
(`m0Subst`) show only that the hypotheses of the exclusion forms are jointly
satisfiable. No exclusion form is shown to exclude a strict system that
Theorem A(4) leaves open.

## 3. Corpus emptiness

- **Theorem A(4)** (cut-pair note §2): a letter pair with a left
  strong-coincidence witness is the first-letter pair of no state of a strict
  system: `Psc.StrictSystem.StrictSystem.not_witness`, hence
  `no_strictSystem_of_strongCoincidence` (`C4FromStrongCoincidence`) and
  `no_strictComponent_of_strongCoincidence`.
- **Concrete specimens, kernel-decided:** `Psc.StrictSystem.specimens_no_strictSystem`
  (eight three-letter specimens, least witness levels by `leastWitnessLevel_spec`),
  `plastic_vacuous`, `census_vacuous` (every substitution-level hypothesis of
  the reductio lemmas holds and there is no strict system), `m0_no_strictSystem`.
- **The standing corpus:** `C4StandingCorpus` (finite-domain): for each of
  the 4,554 primitive irreducible Pisot substitutions on `{0,1,2}` with images
  of length `≤ 3` no strict component exists. Its warrant is the Mojo
  least-witness census over all 13,662 letter pairs
  (`kernel/tests/test_c4_standing_corpus.mojo`, finite-domain closure §3)
  composed with Theorem A(4), whose Lean form is above. So on the corpus every
  restatement of §1 is vacuous; the Lean proof covers only the step from the
  witnesses to the conclusion, not the census.
- **Off the corpus** (not a corpus claim): the
  [closed-component search](c4-closed-component-search-2026-11-07.md) decides
  5,754 of the 11,838 non-synchronizing one-outside and reducible specimens
  with images `≤ 3` by strong coincidence (no strict system at all; 870 of
  them rest also on Lemma 4 of that note), and records a window observation,
  not a verdict, for strict systems with `K₂ = 0` on every state and every
  state of length `≤ 13`: none.

## 4. The leave-one-out table (`Psc.ReductioControls`)

A leave-one-out control meets every hypothesis of a family except the one
dropped, which is proved false. It shows joint satisfiability of the others,
not that the dropped hypothesis is needed, unless a negative control is
stated.

| Family (Lean) | `N` | balance | defect column | `Irr` | other |
| --- | --- | --- | --- | --- | --- |
| `KernelCofactor` (`kernelCofactor_leave_one_out`) | `diagSys` | `towSys` | `C ≠ ∅`: `plasticEmpty` (degenerate by necessity) | `rotSys 0` (primitive), `wT` | `SC`: unknown; `PerronVec`: not independent |
| `Degree2Sector` (`degree2Sector_leave_one_out`) | `bpaSys` (primitive Pisot `σ`) | `towSys` | `plasticEmpty` (degenerate) | `rotSys 0`, `exA`; negative: `wedge2_dvd_needs_irreducible` | — |
| `Degree3Sector.deg23_iii_of_ne` (`degree3Sector_leave_one_out`) | not constructed | `towSys` (fails `Bal` too) | `censusEmpty` (degenerate) | jointly with `Distinct`: `rotSys 1`; jointly with `Moduli`: `cyc3Norm`; alone: not constructed | `RootBound`: not independent for primitive `σ` |
| `Degree4Floor.theoremA_of_primitive`, `sieve4_of_primitive` (`degree4Floor_leave_one_out`) | not constructed | `towSys` (fails `Bal` too) | `plasticEmpty` (degenerate; `m0_no_degree4` gives content) | `rotSys 2` (`det M = 0`; negative: `theoremA_needs_irreducible`); jointly with `Prim`, `PisotRoot`: `cyc4Norm` | `Prim`: not independent; `PisotRoot`, `SC`: unknown |
| `sieve4`, literal three-root form | — | `towSys` | `plasticEmpty` | `rotSys 2` drops `Irr` jointly with the root hypotheses (`rot_no_sieve4_roots`); `Irr` alone: not constructed | — |
| `Degree4Floor.ssign_root_bound_of_primitive` | — | — | — | — | non-degenerate **full** control `rotSys 0` (`ssign_root_bound_full_control`) |

`rotSys 0` is the zero-return system of an actual strict component: its
substitution is `Psc.StrictSystem.cycSubst` (`012/120/201`,
`Psc.ReductioControls.rotSubst_eq_cycSubst`) and its states are the swap
closure of the strict component `Psc.StrictSystem.cycC`
(`rot0_states_eq_cycC`). So the `Irr` rows of the `KernelCofactor` and
`Degree2Sector` tables are met by a strict component (`rot0_strictComponent : StrictComponent rotSubst cycC`; its reachability from a seed, i.e. membership in `B_σ`, is not proved) over a primitive
substitution with reducible `χ_M` (`χ_M = X²(X − 3)`); on it `cyc_lcm_control`
shows that `Irr` cannot be dropped from `deg2_sector`.

## 5. What a full control would be

A full control of a family is an object meeting all its hypotheses. At the
strict-system level it is a strict system (for the component-level lemmas, a
strict component) over a three-letter substitution with irreducible `χ_M`,
of the matching first defect degree, and, for `deg23_iii`, `sieve4`,
`theoremA`, primitive with a Pisot root. By `StrictSystem.counterexample` the
balanced pair algorithm started at any of its states, or at any seed whose
`B_σ`-path reaches it, does not terminate with coincidence, and some cut pair
has no left strong-coincidence witness. Over a PIP substitution it would be a
counterexample to C4 (`prob:C4`), and on the standing corpus none exists
(`C4StandingCorpus`). At the `ChildSystem` level a full control need not be a
strict system (its children need not be zero-return blocks), and nothing is
excluded there beyond the specimens of §2.

## Work shown

### Assumptions and hypotheses

The objects are those of §0: ordered pairs over `Fin 3`, child systems with a
normalisation, strict systems and components as defined in `Psc.StrictSystem`.
The only standing hypotheses of the restatements are substitution-level
(`Irr`, `Prim`, `Pisot(β)`) and the first defect degree.

### Derivation / reduction

Each restatement composes the `ChildSystem`-level lemma with the discharge of
its structural hypotheses on `StrictSystem.swapSystem` (§0); each exclusion
form is the contrapositive of a restatement; corpus emptiness is Theorem A(4)
composed with the census.

### Evidence and replay

```sh
cd proof/PscVerif && lake build PscVerif
cd proof/PscVerif && lake env lean ProofBankAudit.lean   # standard axioms only
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_standing_corpus.mojo)
```

### Negative controls

`erase_control` (the sink step needs nonerasure); `cyc_lcm_control` (`Irr` is
needed for `|R| ≥ deg lcm`); `wedge2_dvd_needs_irreducible`,
`theoremA_needs_irreducible`; `plastic_220_control` (the root-level sieve
alone does not exclude `(2,2,0)`); `m0_bound_needed`.

### Non-claims / remaining gaps

- No strict system or strict component is known for any primitive
  irreducible Pisot substitution, and none is claimed not to exist beyond the
  corpus and the listed specimens (C4 open).
- No exclusion form is shown to do work beyond Theorem A(4) at the strict
  level.
- The rows marked "not constructed" or "unknown" in §4 are open; a control
  keeping `N`, balance, `C ≠ ∅` and `Irr` together would be a strict
  component (§5).
- G1 is a hypothesis of the sink step; first defect degrees `r ≥ 5` are not
  covered; Theorem A(ii) is proved in eigenvalue form only and Theorem A(iv)
  only in abstract form (`StrictComponent.kernel_cofactor`), not composed with
  `Q₄D`.
- `C4StandingCorpus` rests on the Mojo census; the Lean library proves only
  Theorem A(4) and the kernel-decided specimens.
