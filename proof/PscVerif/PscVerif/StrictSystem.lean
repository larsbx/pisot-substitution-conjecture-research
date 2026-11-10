/-
# Strict systems, strict components, Theorem A of the cut-pair note, and the reductio lemmas

Manuscript `PSC_balanced_pair_state_2026-09-13.tex`, `def:bpa` (the
balanced-pair automaton `B_σ`, productive states, closed nonproductive
recurrent noncoincident SCCs, termination with coincidence), `lem:descendants`
(used through `Psc.Descendants`), `prob:C4` (C4 quantifies over strict
components); `docs/c4-cut-pair-productivity-2026-11-04.md` §2 (Theorem A) and
§5 (exact controls); `docs/c4-finite-domain-closure-2026-11-05.md` §§1–3 (a
strict component is a strongly connected strict system; `C4FromStrongCoincidence`;
the least-level histogram of `C4StandingCorpus`); the informal mismatch-density
step in the docstring of `Psc.Degree2Sector`; the first-defect selection of
`docs/c4-concentration-attack-2026-11-06.md` §§2, 8.  Part 2 (`## Part 2` below):
`thm:parikh` (line 601), `prop:cocycle` (line 705), `thm:deg23` (ii), (iii) (line 728) and
`thm:sieve` at `r = 4` (line 740), whose standing hypothesis "`d = 3` and `C` strict" is
read here as a `StrictSystem` or `StrictComponent` over `Fin 3`; the remark after
`thm:sieve` ("the sieves are necessary conditions on the algebra of a strict component");
`thm:sink` (line 588, with `thm:sink-summary`, line 346) and the last sentence of the
cut-pair note's Theorem A(5), in existence form; `thm:global-sync` (line 623, for
`m0_no_strictSystem`); the concentration note §2 (Theorem A (i)–(iv)) and §8.  The register
of the reductio lemmas, their restatements below and their leave-one-out controls
(`Psc.ReductioControls`) is `docs/c4-reductio-lemmas-2026-11-07.md`.

A **strict system** (`StrictSystem s C`) is a finite nonempty set `C` of ordered
pairs, each an irreducible balanced block (`Psc.Reduction.IsBlock`) and
noncoincident, closed under taking the blocks of `red (σ T.1) (σ T.2)`.  A
**strict component** (`StrictComponent`) is a strict system that is strongly
connected on states up to side swap by nonempty child paths.  The manuscript's
strict component of `B_σ` is `BpaStrictComponent`.

Proved here, in full (any alphabet with decidable equality unless stated):

* (a) the structure: `StrictSystem.balanced`, `childClosed`,
  `mem_of_red_iterate` (every block of `red (σⁿ T.1) (σⁿ T.2)`, `T ∈ C`, is in
  `C`, all `n ≥ 0`), `reflTransGen_mem`; `isBlock_swap`;
  **`StrictSystem.swapClosure`** (the swap closure of a strict system is strict);
  for nonerasing `σ`, `toChildSystem` (the `Psc.Reduction.redSystem` child
  system; `toChildSystem_equiv1`, `_nonempty`, `_isBlock`, `_noncoincident`,
  `_top_ne_nil`, `toChildSystem_desc`, the hypotheses the sector theorems take)
  and, on a linearly ordered alphabet, `lexNorm` (the
  `Psc.Descendants.lexNormalisation` of the swap closure, `lexNorm_R`);
  `StrictComponent`, its `swapClosure`, and
  **`StrictComponent.nrep_stronglyConnected`**: for every normalisation of the
  child system of a strict component, `N_C = A + B` (`Nrep`, cast to `ℝ`) is
  `Psc.PerronCore.StronglyConnected`; `lexNorm_stronglyConnected`;
* (b) **Theorem A** (cut-pair note §2): (1) `first_letters_ne`, `cutPair_ne`,
  `exists_cutPair`; (2) `cut_follow`, `cut_follow_index` (every balanced cut of
  `σⁿ(S)` before its end, the cut at `0` included, is followed by the first
  letters of a state); (3) `cutPair_subst`, `cutPair_first` (`g × g` preserves
  the cut-pair set and `g(c) ≠ g(c')` on it); (4) `StrongCoincidenceWitness`,
  **`StrictSystem.not_witness`**; (5) `factorSet`, `factorSet_eq_reachable`,
  **`strictSystem_of_factorSet`** (the conditional finite-sink converse) and
  `exists_strictSystem_iff`; **`no_strictSystem_of_strongCoincidence`**
  (`C4FromStrongCoincidence`);
* (c) `IndexWitness`, `WitnessAt`, `strongCoincidenceWitness_iff_index`,
  `witnessAt_iff_index`, `IndexWitness.aligned`, and `LeastWitnessLevel` with
  **`leastWitnessLevel_spec`** (a witness at level `m` and none below), decided in
  the kernel.  Least levels for the pairs `01, 02, 12`, hence no strict system:
  the plastic substitution `1/2/01` (`Psc.Degree2Sector.plasticSubst`) `13, 14, 12`;
  its reversal `1/2/10` `15, 1, 14` (level `15` is the deepest of the
  `C4StandingCorpus` histogram); the census substitution `011/2/120`
  (`Psc.Degree3Sector.censusSubst`) `5, 5, 7`; its image-wise reversal
  `110/2/021` `6, 4, 5`; that reversal's relabelling `1/210/002` `5, 6, 4`
  (`reversal_conventions` checks both conventions); Tribonacci `01/02/0`
  (`Psc.Descendants.tribSubst`) `1, 1, 1`; `01/121/012` `2, 1, 2` and
  `01/12/021` `4, 1, 4` (cut-pair note §5, at its recorded indices); Fibonacci
  `01/0` (`1`).  An `example` shows the plastic levels are sharp;
* (d) `Productive`, `TerminatesWithCoincidence` (`def:bpa` wording, on `ChildNC`
  paths); `StrictSystem.not_productive`, **`exists_seed_not_terminates`** (a strict
  system meeting `bpaStatesNC` gives a seed whose balanced pair algorithm does
  not terminate with coincidence), the converse
  `exists_strictSystem_of_not_terminates` (given finiteness of the states
  reachable from the seed), and `terminates_of_strongCoincidence`;
  `BpaStrictComponent` (the manuscript's strict component, on the swap-closed
  double cover), `nonproductive_iff_no_coincidence_child` (the last sentence
  but one of `def:bpa`), `BpaStrictComponent.toStrictComponent`,
  `StrictComponent.toBpa`;
* (e) `mismatch`, **`StrictSystem.mismatch_density`**: if every state has length
  `≤ L`, then `|σⁿ T.1| ≤ L · mismatch (σⁿ T.1) (σⁿ T.2)` for every state `T`
  and every `n`;
* (f) `nsub x w` (`N_x(w)`, the number of embeddings, `w.sublists.count x`) with
  `nsub_single`, `nsub_two` (`n2`), `nsub_three` (`n3`), `nsub_four`
  (`Psc.Defect4.n4`); `Kx`, `KNe` (`K_r ≠ 0`), `defectDegree`,
  `StrictSystem.defectDegree_spec` (it exists, is `≥ 2` and `≤` every state
  length), `defectDegree_eq_two_iff`, `_three_iff`, `_four_iff` and over `Fin 3`
  `defectDegree_eq_two_iff_kw`, `_three_iff_k3Vec`, `_four_iff_k4Vec`;
* the first-defect selection over `Fin 3` (`equiv2_comm`, `equiv3_comm`,
  `forall_swapClosureF`, `k3Vec_swap`, `k4Vec_swap`, `exists_rep_kw`,
  `exists_rep_k3Vec`, `exists_rep_k4Vec`): a nonzero defect vector on a state gives one
  on its representative, in every normalisation; (g) composes it with the sector
  theorems;
* controls (`decide`): Thue–Morse `01/10` and `012/120/201` (strict components,
  first defect degree `2`, `N_C` strongly connected; on `012/120/201` no letter
  pair has a left strong-coincidence witness at any level, `cyc_no_witness`); the
  six-state transient strict system of `10/102/211` from `(02, 20)`, which is
  that seed's factor set (`carrier_factorSet`, `carrier_A5`), so neither `{0,2}`
  nor `{1,2}` has a left strong-coincidence witness at any level while `{0,1}` has
  one at level `1` (`carrier_witnesses`); its four-state sink, a strict component
  (`StrictComponent.of_cycle`, `carrierSink_strictComponent`) with the single cut
  pair `(1, 2)`; `010/101` (a strict system that is not swap-closed); Fibonacci (a
  coincidence among the factors of `(01, 10)`);
* (g) **the reductio lemmas on a strict system or strict component over `Fin 3`**, with
  only substitution-level hypotheses and the first defect degree, for **every**
  normalisation `P` of `StrictSystem.swapSystem` (the zero-return child system of the
  swap closure).  The structural hypotheses are discharged: nonerasure
  (`nonerasing_of_irreducible`), balance, `∼₂`, `∼₃` (`swapSystem_equiv1`, `_equiv2`,
  `_equiv3`), `C ≠ ∅` (`swapSystem_nonempty`), the nonzero defect column
  (`exists_rep_kw_of_two`, `_k3_of_three`, `_k4_of_four`), strong connectivity
  (`StrictComponent.nrep_stronglyConnected`), the Perron data
  (`Psc.PerronExistence.perron_inc`), the other two roots
  (`Psc.Degree4Floor.exists_other_roots`) and the root bound `ρ(S) ≤ β`;
  `card_swapClosureF` (`|swap closure| = 2|R|`), `card_rep_le` (`|R| ≤ |C|`),
  `StrictSystem.three_le_card_rep` (`|R| ≥ 3`, `χ_M` irreducible, any defect degree):
  - **`StrictSystem.deg2_sector`** (`χ_M` irreducible, `r = 2`): `rank Q₂ = 3`,
    `χ_{Λ²M} ∣ χ_S` over `ℚ` and `ℤ`, `lcm(χ_M, χ_{Λ²M}) ∣ χ_{N_C}` mod `2`,
    `|R| ≥ deg lcm`, and `|R| ≥ 6` when `det M` is odd and `tr M ≢ tr Λ²M (mod 2)`;
  - **`StrictComponent.kernel_cofactor`** (`M` primitive, `χ_M` irreducible; any `r`):
    `PerronData` at `β`, `χ_{N_C} = χ_M · g` with `g = χ(N_C | ker P_R)` integral and
    `gcd(χ_M, g) = 1`, `β` a simple root and the spectral radius of `N_C`, and
    Theorem A(iv) in abstract form (`Q = L' P_R` for every intertwiner `Q` into a space
    where `χ_M` kills `R`, `L'` injective unless `Q = 0`);
  - **`StrictSystem.deg23_iii`** (`M` primitive, `χ_M` irreducible, a root `β` whose
    other roots have modulus `< 1`; `r = 3`): `β` is the Perron root, every root of `q₃`
    is `det M`, `q₃ = (X − det M)^{rank Q₃}`, `im Q₃ ⊆ ker (Φ₃ − det M)`,
    `1 ≤ rank Q₃ ≤ 2`, `det M` is a root of `χ_S`, and
    `M^{⊗3} K₃(T) = det M · K₃(T)` for every state `T ∈ C` (`phi3_neg`);
  - **`StrictSystem.sieve4`** (`M` primitive, `χ_M` irreducible, a Pisot root; `r = 4`):
    `β` is the Perron root `r > 1`, `|det M| = 1`, `ρ(S) = β`;
  - **`StrictComponent.theoremA`** (the same on a component; Theorem A(i), (iii), and
    (ii) in eigenvalue form): moreover every root of `q₄` is `det M` times a root of
    `χ_M`, `S = det M · D N_C D`, and a gauge (`det M = 1`) or an anti-gauge
    (`det M = −1`), `StrictComponent.gauge_or_antiGauge`;
    `StrictComponent.closed_walk_sign`: every closed walk of length `n` of the child graph
    on the representatives has sign product `(det M)ⁿ` (`isAntiGauge_walk`, the forward
    direction of the anti-gauge walk criterion only);
  - `StrictComponent.deg2_sector`, `.deg23_iii`, `.sieve4`: the instances on a strict
    component;
* (h) **exclusion forms**: `StrictSystem.three_le_card` (`|C| ≥ 3` for every strict system
  over an irreducible `χ_M`); `StrictSystem.lcm_le_card`,
  **`no_strictSystem_deg2_of_card_lt`** (no strict system of first defect degree `2` with
  `|R| < deg lcm`), `no_strictSystem_deg2_odd` (none with `|R| < 6` in the odd case);
  **`no_strictSystem_deg3_of_not_eigen`** (none of first defect degree `3` containing a
  state `T` with `M^{⊗3} K₃(T) ≠ det M · K₃(T)`); **`no_strictSystem_deg4_of_abs_det_ne_one`**
  (none of first defect degree `4` when `|det M| ≠ 1`); `HasBothSigns` (decidable),
  `StrictSystem.exists_both_of_hasBothSigns`,
  **`no_strictComponent_deg4_of_hasBothSigns`** (no strict component of first defect
  degree `4` in which some state has a child in both orientations,
  `Psc.CocycleSpectrum.not_gauge_of_both`); their hypotheses hold jointly on specimens
  (`no_strictSystem_deg2_odd_control`: plastic; `no_strictSystem_deg3_control`: the census
  state over `011/2/120`; `no_strictSystem_deg4_control`: `m0Subst`, `det M = −2`), over
  which there is no strict system at all, so there the exclusions are redundant with
  Theorem A(4);
* (i) **scope**: `StrictSystem.counterexample` (on a strict system the balanced pair
  algorithm started at any of its states, or at a seed whose `B_σ`-path reaches it, does
  not terminate with coincidence, and some cut pair has no left strong-coincidence
  witness; the direction strict system ⇒ failure only);
  **`thm:sink`**: `StrictSystem.exists_child`, `filter_childClosed`,
  `defectDegree_le_of_subset`, **`StrictSystem.exists_strictComponent_reachable`** (for
  nonerasing `σ` every state of a strict system reaches a strict component inside it, a
  sink SCC of the child graph), `exists_strictComponent_subset`,
  **`exists_bpaStrictComponent_of_not_terminates`** (a seed with finite `B_σ`-reachable set
  that does not terminate with coincidence gives a `BpaStrictComponent`), and
  `exists_bpaStrictComponent_of_finite` (`thm:sink` with G1 as a hypothesis); the
  negative control `erase_control` (`eraseSubst`, `0, 1 ↦ ε`: a strict system containing
  no strict component, so nonerasure cannot be dropped);
  `no_strictComponent_of_strongCoincidence`, `specimens_no_strictSystem` (the
  eight three-letter specimens of (c)), `plastic_vacuous`, `census_vacuous` (every
  substitution-level hypothesis holds and there is no strict system), `m0_no_strictSystem`
  (the `Psc.Degree4Floor` control `m0Subst`, an instance of `thm:global-sync`: `σ_+` is
  constant, level-`1` witnesses for all pairs);
  controls `cyc_primitive`, `cyc_not_irreducible`, `cyc_charpoly_Q`, `cyc_pisot_root`,
  `carrier_primitive`, `carrier_not_irreducible`, `carrier_not_pisot`,
  `strictComponent_controls` (`cycC` fails only `χ_M` irreducible; the sink of
  `10/102/211` fails `χ_M` irreducible and the Pisot root),
  `hasBothSigns_controls`; the negative control **`cyc_lcm_control`** (`cyc_inc_two`,
  `cyc_wedge2_two`, `cyc_charpoly_two`, `cyc_lcm_natDegree`, `cyc_card_rep`): on the strict
  component `cycC` of the primitive `012/120/201`, of first defect degree `2`, `|R| = 3`
  but `deg lcm ≥ 4`, so `χ_M` irreducible cannot be dropped from `deg2_sector`.

Not proved here:

* that a strict system or strict component exists for any primitive irreducible
  Pisot substitution, or that none does (C4, `prob:C4`, issue #138's
  `UniversalAlignedCoincidence`); the corpus-wide statement `C4StandingCorpus`
  rests on the Mojo census, and only the specimens listed in (c) are decided here;
* G1 (finiteness of `B_σ`, or of the states reachable from a seed): a hypothesis of
  `exists_strictSystem_of_not_terminates`, `exists_bpaStrictComponent_of_not_terminates`
  and `exists_bpaStrictComponent_of_finite`.  The nonerasure hypothesis of the sink step
  is needed (`erase_control`) and is not discharged in general (over `Fin 3` it follows
  from `χ_M` irreducible, `nonerasing_of_irreducible`);
* that the substitution-level hypotheses of (g) (`χ_M` irreducible, Pisot, primitive)
  can be met together with the existence of a strict component: the lemmas of (g) and (h)
  are reductio lemmas, necessary conditions on a strict system (resp. strict component),
  and no control meets all of their hypotheses.  Every finite counterexample to seeded
  termination of the balanced pair algorithm yields a strict system
  (`exists_strictSystem_of_not_terminates`) and, for nonerasing `σ`, a strict component
  of `B_σ` (`exists_bpaStrictComponent_of_not_terminates`), so the lemmas apply to it
  (the component-level ones at the first defect degree of the component found, which is
  at least that of the system, `defectDegree_le_of_subset`); a failure of strong
  coincidence is **not** known to yield a strict system (that is C4, `prob:C4`), so they
  are not established as necessary conditions on every counterexample to strong
  coincidence.  The strict components exhibited over three
  letters (`cycC`, the sink of `10/102/211`) have reducible `χ_M`; over the specimens of
  (c), `plasticSubst` and `censusSubst` among them, and over `m0Subst` there is no strict
  system at all.  The relation between these coincidence conditions and PSC itself is not
  formalized here;
* Theorem A(ii) only in eigenvalue form (every root of `q₄` is `det M` times a root of
  `χ_M`): the subspace form `im Q₄ ⊆ ker χ_{dM}(Φ₄)` needs the semisimplicity of
  `Φ₄|_{im Q₄}`, not formalized (as in `Psc.Degree4Floor`).  Theorem A(iv) only as the
  abstract factorisation of `StrictComponent.kernel_cofactor` (`Q = L' P_R` for every
  intertwiner `Q`), not composed with `Q = Q₄ D`, so "`K₄ ≠ 0` on every state of a
  first-defect-degree-`4` strict component" is not proved;
* the converse of `isAntiGauge_walk` (the anti-gauge walk criterion: closed walks of
  length `n` with sign `(-1)ⁿ` give an anti-gauge), as in `Psc.CocycleSpectrum`;
* the first defect degrees `r ≥ 5`, and any bound on the first defect degree of a strict
  component; `HasBothSigns` is met here only by a two-letter strict component
  (Thue–Morse), and fails on `cycC` and on the sink of `10/102/211`;
* negative controls at the strict-component level for the other hypotheses of (g): only
  `χ_M` irreducible in the bound `|R| ≥ deg lcm` (`cyc_lcm_control`); `deg lcm = 4` there
  is proved only as `≥ 4`;
* Theorems B and C of the cut-pair note (subtile measure), and anything
  measure-theoretic;
* states as unordered pairs: everything is on ordered pairs, i.e. on the
  swap-closed double cover;
* any agreement with the Mojo census `psc.coincidence_formula` beyond the
  specimens of (c); for those the least levels found here are consistent with the
  `C4StandingCorpus` histogram, which does not list specimens.
-/
import PscVerif.Descendants
import PscVerif.Degree2Sector
import PscVerif.Degree3Sector
import PscVerif.Defect4Lie
import PscVerif.CocycleSpectrum
import PscVerif.Degree4Floor
import PscVerif.KernelCofactor

set_option linter.dupNamespace false

namespace Psc.StrictSystem

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants Psc.SignedCocycle

variable {α : Type*} [DecidableEq α]

/-! ### Strict systems -/

/-- A **strict system** for `s` (cut-pair note §2): a finite nonempty set `C` of
ordered pairs, each an irreducible balanced block (`IsBlock`) and
noncoincident, closed under taking the blocks of `red (σ T.1) (σ T.2)`. -/
structure StrictSystem (s : α → List α) (C : Finset (List α × List α)) : Prop where
  nonempty : C.Nonempty
  isBlock : ∀ T ∈ C, IsBlock T
  noncoincident : ∀ T ∈ C, T.1 ≠ T.2
  closed : ∀ T ∈ C, ∀ U ∈ red (subst s T.1) (subst s T.2), U ∈ C

/-- Over a finite alphabet `IsBlock` is decidable (for the `decide` controls). -/
instance [Fintype α] (T : List α × List α) : Decidable (IsBlock T) := by
  unfold IsBlock; infer_instance

/-- A block with its sides swapped is a block. -/
theorem isBlock_swap {T : List α × List α} (h : IsBlock T) : IsBlock T.swap := by
  obtain ⟨hne, hbal, hirr⟩ := h
  refine ⟨?_, fun a => (hbal a).symm, fun k hk hkl hE => hirr k hk ?_ fun a => (hE a).symm⟩
  · intro h0
    apply hne
    apply List.length_eq_zero_iff.mp
    rw [hbal.length_eq]
    simpa using congrArg List.length h0
  · simpa [hbal.length_eq] using hkl

/-- The swap closure `C ∪ swap C` (the `Finset` form of `Psc.Descendants`). -/
abbrev swapClosureF (C : Finset (List α × List α)) : Finset (List α × List α) :=
  C ∪ C.image Prod.swap

theorem mem_swapClosureF {C : Finset (List α × List α)} {T : List α × List α} :
    T ∈ swapClosureF C ↔ T ∈ C ∨ T.swap ∈ C := by
  simp only [Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨U, hU, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hU)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨T.swap, h, Prod.swap_swap T⟩

namespace StrictSystem

variable {s : α → List α} {C : Finset (List α × List α)}

theorem equiv1 (h : StrictSystem s C) : ∀ T ∈ C, Equiv1 T.1 T.2 :=
  fun T hT => (h.isBlock T hT).2.1

/-- The hypothesis `hC` of `Psc.Reduction.redSystem`. -/
theorem balanced (h : StrictSystem s C) : ∀ T ∈ C, Equiv1 T.1 T.2 ∧ T.1 ≠ [] :=
  fun T hT => ⟨(h.isBlock T hT).2.1, (h.isBlock T hT).1⟩

theorem childClosed (h : StrictSystem s C) : ChildClosed s ↑C :=
  fun T hT U hU => h.closed T hT U hU

/-- Every block of `red (σⁿ T.1) (σⁿ T.2)`, `T ∈ C`, lies in `C`: the factor
closure used in the proof of Theorem A(2). -/
theorem mem_of_red_iterate (h : StrictSystem s C) (n : ℕ) :
    ∀ T ∈ C, ∀ U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2), U ∈ C := by
  induction n with
  | zero =>
    intro T hT U hU
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply,
      red_of_isBlock (h.isBlock T hT)] at hU
    rw [List.mem_singleton.1 hU]; exact hT
  | succ n ih =>
    intro T hT U hU
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      red_iterate_subst s n (equiv1_subst s (h.equiv1 T hT))] at hU
    obtain ⟨V, hV, hUV⟩ := List.mem_flatMap.1 hU
    exact ih V (h.closed T hT V hV) U hUV

/-- States reachable from a state of `C` in the full child graph lie in `C`. -/
theorem reflTransGen_mem (h : StrictSystem s C) {T U : List α × List α} (hT : T ∈ C)
    (hTU : Relation.ReflTransGen (Child s) T U) : U ∈ C := by
  induction hTU with
  | refl => exact hT
  | tail _ hVU ih => exact h.closed _ ih _ hVU

theorem transGen_mem (h : StrictSystem s C) {T U : List α × List α} (hT : T ∈ C)
    (hTU : Relation.TransGen (Child s) T U) : U ∈ C :=
  h.reflTransGen_mem hT hTU.to_reflTransGen

/-- **The swap closure of a strict system is strict.** -/
theorem swapClosure (h : StrictSystem s C) : StrictSystem s (swapClosureF C) where
  nonempty := h.nonempty.mono Finset.subset_union_left
  isBlock T hT := by
    rcases mem_swapClosureF.1 hT with hT | hT
    · exact h.isBlock T hT
    · simpa using isBlock_swap (h.isBlock _ hT)
  noncoincident T hT := swapClosureF_coincidenceFree (D := C) h.noncoincident T hT
  closed T hT U hU := swapClosureF_childClosed (D := C) h.childClosed T hT U hU

theorem swapClosure_swap_mem : ∀ T ∈ swapClosureF C, T.swap ∈ swapClosureF C :=
  fun T hT => swapClosureF_swapClosed (D := C) T hT

/-! ### The zero-return child system and its normalisations -/

/-- For nonerasing `s`, the zero-return child system (`Psc.Reduction.redSystem`)
of a strict system: states `C`, children `red (σ T.1) (σ T.2)`. -/
def toChildSystem (h : StrictSystem s C) (hs : ∀ a, s a ≠ []) : ChildSystem α :=
  redSystem s hs C h.balanced h.closed

variable (h : StrictSystem s C) (hs : ∀ a, s a ≠ [])

@[simp] theorem toChildSystem_C : (h.toChildSystem hs).C = C := rfl

@[simp] theorem toChildSystem_s : (h.toChildSystem hs).s = s := rfl

theorem toChildSystem_children (T : List α × List α) :
    (h.toChildSystem hs).children T = red (subst s T.1) (subst s T.2) := rfl

/-- The balance hypothesis `hbal` of the sector theorems (`Psc.ParikhRank`,
`Psc.Degree2Sector`, `Psc.KernelCofactor`, ...). -/
theorem toChildSystem_equiv1 : ∀ T ∈ (h.toChildSystem hs).C, Equiv1 T.1 T.2 := h.equiv1

/-- The hypothesis `hC : S.C.Nonempty` of the sector theorems. -/
theorem toChildSystem_nonempty : (h.toChildSystem hs).C.Nonempty := h.nonempty

theorem toChildSystem_isBlock : ∀ T ∈ (h.toChildSystem hs).C, IsBlock T := h.isBlock

theorem toChildSystem_top_ne_nil : ∀ T ∈ (h.toChildSystem hs).C, T.1 ≠ [] :=
  fun T hT => (h.isBlock T hT).1

theorem toChildSystem_noncoincident : ∀ T ∈ (h.toChildSystem hs).C, T.1 ≠ T.2 :=
  h.noncoincident

/-- `lem:descendants` in the child system of a strict system, at every depth. -/
theorem toChildSystem_desc (n : ℕ) (T : List α × List α) (hT : T ∈ C) :
    (h.toChildSystem hs).desc n T = red ((subst s)^[n] T.1) ((subst s)^[n] T.2) :=
  redSystem_desc_of_isBlock s hs C h.balanced h.closed n T hT (h.isBlock T hT)

/-- The lexicographic normalisation (`Psc.Descendants.lexNormalisation`) of a
swap-closed strict system. -/
def lexNormOf [LinearOrder α] (hswap : ∀ T ∈ C, T.swap ∈ C) :
    Normalisation (h.toChildSystem hs) :=
  lexNormalisation s hs C h.balanced h.closed hswap h.noncoincident

/-- The lexicographic normalisation of the swap closure of a strict system
(swap closure first, `swapClosure`). -/
def lexNorm [LinearOrder α] : Normalisation (h.swapClosure.toChildSystem hs) :=
  h.swapClosure.lexNormOf hs swapClosure_swap_mem

theorem lexNorm_R [LinearOrder α] :
    (h.lexNorm hs).R = (swapClosureF C).filter fun T => T.1 < T.2 := rfl

end StrictSystem

/-! ### Theorem A of the cut-pair note -/

/-- The **cut-pair set** `A(C)`, as ordered letter pairs: `(c, c')` is a cut pair
if some state of `C` has first letters `c` (top) and `c'` (bottom).  The note's
unordered `{c, c'} ∈ A(C)` is `CutPair C c c' ∨ CutPair C c' c`. -/
def CutPair (C : Finset (List α × List α)) (c c' : α) : Prop :=
  ∃ T ∈ C, T.1.head? = some c ∧ T.2.head? = some c'

/-- A *left strong-coincidence witness* for the letters `c, c'`:
`σⁿ(c) = P x Q`, `σⁿ(c') = P' x Q'` with `p(P) = p(P')` (`Equiv1`). -/
def StrongCoincidenceWitness (s : α → List α) (c c' : α) : Prop :=
  ∃ (n : ℕ) (P Q P' Q' : List α) (x : α), (subst s)^[n] [c] = P ++ x :: Q ∧
    (subst s)^[n] [c'] = P' ++ x :: Q' ∧ Equiv1 P P'

theorem strongCoincidenceWitness_comm {s : α → List α} {c c' : α} :
    StrongCoincidenceWitness s c c' ↔ StrongCoincidenceWitness s c' c := by
  constructor <;>
  · rintro ⟨n, P, Q, P', Q', x, h1, h2, hP⟩
    exact ⟨n, P', Q', P, Q, x, h2, h1, fun a => (hP a).symm⟩

/-- The first block of `red (c :: q) (c' :: q')` begins with `c` on top and `c'`
on the bottom. -/
theorem exists_first_block {c c' : α} {q q' : List α} (h : Equiv1 (c :: q) (c' :: q')) :
    ∃ U ∈ red (c :: q) (c' :: q'), U.1.head? = some c ∧ U.2.head? = some c' := by
  obtain ⟨U, rest, hr⟩ := List.exists_cons_of_ne_nil
    (red_ne_nil (u := c :: q) (v := c' :: q') (by simp) h.length_eq)
  have hmem : U ∈ red (c :: q) (c' :: q') := by rw [hr]; exact List.mem_cons_self
  have hU := red_isBlock h U hmem
  have htop := red_top h.length_eq
  have hbot := red_bot h.length_eq
  rw [hr] at htop hbot
  simp only [List.map_cons, List.flatten_cons] at htop hbot
  have h2 : U.2 ≠ [] := fun h0 =>
    hU.1 (List.length_eq_zero_iff.mp (by rw [hU.2.1.length_eq, h0]; rfl))
  refine ⟨U, hmem, ?_, ?_⟩
  · obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hU.1
    rw [hx] at htop ⊢
    simp only [List.cons_append, List.cons.injEq] at htop
    rw [htop.1]; rfl
  · obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil h2
    rw [hx] at hbot ⊢
    simp only [List.cons_append, List.cons.injEq] at hbot
    rw [hbot.1]; rfl

namespace StrictSystem

variable {s : α → List α} {C : Finset (List α × List α)} (h : StrictSystem s C)
include h

/-- **Theorem A(1).**  Every state has distinct first letters. -/
theorem first_letters_ne {T : List α × List α} (hT : T ∈ C) :
    ∃ (c c' : α) (u v : List α), T = (c :: u, c' :: v) ∧ c ≠ c' := by
  obtain ⟨hne, hbal, hirr⟩ := h.isBlock T hT
  have hnc := h.noncoincident T hT
  obtain ⟨u0, v0⟩ := T
  obtain ⟨c, u, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨c', v, rfl⟩ := List.exists_cons_of_ne_nil (l := v0) fun h0 => by
    simp [h0] at hbal
    exact absurd hbal.length_eq (by simp)
  exact ⟨c, c', u, v, rfl, Psc.Binomial.heads_ne hbal hirr hnc⟩

/-- **Theorem A(1)**, cut-pair form: `A(C)` consists of off-diagonal pairs. -/
theorem cutPair_ne {c c' : α} (hcp : CutPair C c c') : c ≠ c' := by
  obtain ⟨T, hT, h1, h2⟩ := hcp
  obtain ⟨d, d', u, v, rfl, hdd⟩ := h.first_letters_ne hT
  simp only [List.head?_cons, Option.some.injEq] at h1 h2
  exact h1 ▸ h2 ▸ hdd

/-- **Theorem A(1)**: `A(C)` is nonempty. -/
theorem exists_cutPair : ∃ c c', CutPair C c c' := by
  obtain ⟨T, hT⟩ := h.nonempty
  obtain ⟨c, c', u, v, rfl, -⟩ := h.first_letters_ne hT
  exact ⟨c, c', _, hT, rfl, rfl⟩

/-- **Theorem A(2)**, split form.  If `σⁿ(S) = (p c q, p' c' q')` for a state
`S ∈ C` with `p(p) = p(p')` (a proper balanced cut, the cut at index `0`
included), then `(c, c')` is a cut pair of `C`. -/
theorem cut_follow {T : List α × List α} (hT : T ∈ C) (n : ℕ) {p q p' q' : List α} {c c' : α}
    (hu : (subst s)^[n] T.1 = p ++ c :: q) (hv : (subst s)^[n] T.2 = p' ++ c' :: q')
    (hp : Equiv1 p p') : CutPair C c c' := by
  have hbal := equiv1_iterate_subst s n (h.equiv1 T hT)
  rw [hu, hv] at hbal
  have hrest : Equiv1 (c :: q) (c' :: q') := equiv1_cancel hp hbal
  obtain ⟨U, hU, h1, h2⟩ := exists_first_block hrest
  refine ⟨U, h.mem_of_red_iterate n T hT U ?_, h1, h2⟩
  rw [hu, hv, red_append hp hrest]
  exact List.mem_append_right _ hU

/-- **Theorem A(2)**, index form: a balanced cut at `k < |σⁿ(S.1)|` is followed by
the two letters of a cut pair. -/
theorem cut_follow_index {T : List α × List α} (hT : T ∈ C) (n : ℕ) {k : ℕ}
    (hk : k < ((subst s)^[n] T.1).length)
    (hcut : Equiv1 (((subst s)^[n] T.1).take k) (((subst s)^[n] T.2).take k)) :
    ∃ c c', ((subst s)^[n] T.1)[k]? = some c ∧ ((subst s)^[n] T.2)[k]? = some c' ∧
      CutPair C c c' := by
  have hlen := (equiv1_iterate_subst s n (h.equiv1 T hT)).length_eq
  have hk' : k < ((subst s)^[n] T.2).length := hlen ▸ hk
  refine ⟨_, _, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', ?_⟩
  refine h.cut_follow hT n (p := ((subst s)^[n] T.1).take k) (p' := ((subst s)^[n] T.2).take k)
    (q := ((subst s)^[n] T.1).drop (k + 1)) (q' := ((subst s)^[n] T.2).drop (k + 1)) ?_ ?_ hcut
  · rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  · rw [← List.drop_eq_getElem_cons hk', List.take_append_drop]

/-- **Theorem A(3)**: the first-letter map preserves the cut-pair set (and, by
`cutPair_ne`, separates it). -/
theorem cutPair_subst {c c' d d' : α} (hcp : CutPair C c c') (hd : (s c).head? = some d)
    (hd' : (s c').head? = some d') : CutPair C d d' := by
  obtain ⟨T, hT, h1, h2⟩ := hcp
  obtain ⟨u, hu⟩ := List.head?_eq_some_iff.1 h1
  obtain ⟨v, hv⟩ := List.head?_eq_some_iff.1 h2
  obtain ⟨x, hx⟩ := List.head?_eq_some_iff.1 hd
  obtain ⟨y, hy⟩ := List.head?_eq_some_iff.1 hd'
  refine h.cut_follow hT 1 (p := []) (p' := []) (q := x ++ subst s u) (q' := y ++ subst s v)
    ?_ ?_ (fun _ => rfl)
  · rw [Function.iterate_one, hu, subst_cons, hx]; rfl
  · rw [Function.iterate_one, hv, subst_cons, hy]; rfl

/-- **Theorem A(3)** for nonerasing `s`, with `g(a)` the first letter of `σ(a)`:
`(g × g)(A(C)) ⊆ A(C)` and `g(c) ≠ g(c')` on `A(C)`. -/
theorem cutPair_first (hs : ∀ a, s a ≠ []) {c c' : α} (hcp : CutPair C c c') :
    CutPair C ((s c).head (hs c)) ((s c').head (hs c')) ∧ (s c).head (hs c) ≠ (s c').head (hs c') :=
  have hg := h.cutPair_subst hcp (List.head?_eq_some_head (hs c)) (List.head?_eq_some_head (hs c'))
  ⟨hg, h.cutPair_ne hg⟩

/-- **Theorem A(4)**: no cut pair has a left strong-coincidence witness. -/
theorem not_witness {c c' : α} (hcp : CutPair C c c') : ¬ StrongCoincidenceWitness s c c' := by
  rintro ⟨n, P, Q, P', Q', x, hc, hc', hP⟩
  obtain ⟨T, hT, h1, h2⟩ := hcp
  obtain ⟨u, hu⟩ := List.head?_eq_some_iff.1 h1
  obtain ⟨v, hv⟩ := List.head?_eq_some_iff.1 h2
  have e1 : (subst s)^[n] T.1 = P ++ x :: (Q ++ (subst s)^[n] u) := by
    rw [hu, show c :: u = [c] ++ u from rfl, iterate_subst_append, hc]; simp
  have e2 : (subst s)^[n] T.2 = P' ++ x :: (Q' ++ (subst s)^[n] v) := by
    rw [hv, show c' :: v = [c'] ++ v from rfl, iterate_subst_append, hc']; simp
  exact h.cutPair_ne (h.cut_follow hT n e1 e2 hP) rfl

/-- **Theorem A(4)**, unordered form. -/
theorem not_witness_of_cutPair_swap {c c' : α} (hcp : CutPair C c' c) :
    ¬ StrongCoincidenceWitness s c c' :=
  fun hw => h.not_witness hcp (strongCoincidenceWitness_comm.1 hw)

end StrictSystem

/-- **Corollary (C4FromStrongCoincidence).**  If every pair of distinct letters
has a left strong-coincidence witness, no strict system exists. -/
theorem no_strictSystem_of_strongCoincidence {s : α → List α}
    (hw : ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') (C : Finset (List α × List α)) :
    ¬ StrictSystem s C := fun h => by
  obtain ⟨c, c', hcp⟩ := h.exists_cutPair
  exact h.not_witness hcp (hw c c' (h.cutPair_ne hcp))

/-! ### Theorem A(5): the conditional finite-sink converse -/

/-- The irreducible factors of all inflations of `T`: the blocks of
`red (σⁿ T.1) (σⁿ T.2)`, `n ≥ 0`. -/
def factorSet (s : α → List α) (T : List α × List α) : Set (List α × List α) :=
  {U | ∃ n, U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2)}

/-- For a block `T` the factor set is the set of states reachable from `T` in the
full child graph (`Psc.Descendants.reflTransGen_child_iff`). -/
theorem factorSet_eq_reachable {s : α → List α} {T : List α × List α} (hT : IsBlock T) :
    factorSet s T = {U | Relation.ReflTransGen (Child s) T U} := by
  ext U
  exact (reflTransGen_child_iff s hT).symm

theorem factorSet_childClosed {s : α → List α} {T : List α × List α} (hT : Equiv1 T.1 T.2) :
    ChildClosed s (factorSet s T) := by
  rintro U ⟨n, hn⟩ V hV
  refine ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
    red_subst s (equiv1_iterate_subst s n hT)]
  exact List.mem_flatMap.2 ⟨U, hn, hV⟩

/-- **Theorem A(5)** (conditional finite-sink converse).  A balanced pair `T` with
nonempty tracks whose set of irreducible factors over all inflations is finite
and contains no coincidence yields a strict system (that set). -/
theorem strictSystem_of_factorSet {s : α → List α} {T : List α × List α}
    (hT : Equiv1 T.1 T.2) (hne : T.1 ≠ []) (hfin : (factorSet s T).Finite)
    (hnc : ∀ U ∈ factorSet s T, U.1 ≠ U.2) : StrictSystem s hfin.toFinset where
  nonempty := by
    obtain ⟨U, hU⟩ := List.exists_mem_of_ne_nil _ (red_ne_nil hne hT.length_eq)
    exact ⟨U, hfin.mem_toFinset.2 ⟨0, hU⟩⟩
  isBlock U hU := by
    obtain ⟨n, hn⟩ := hfin.mem_toFinset.1 hU
    exact red_isBlock (equiv1_iterate_subst s n hT) U hn
  noncoincident U hU := hnc U (hfin.mem_toFinset.1 hU)
  closed U hU V hV := hfin.mem_toFinset.2 (factorSet_childClosed hT U (hfin.mem_toFinset.1 hU) V hV)

theorem StrictSystem.factorSet_subset {s : α → List α} {C : Finset (List α × List α)}
    (h : StrictSystem s C) {T : List α × List α} (hT : T ∈ C) : factorSet s T ⊆ ↑C :=
  fun _ ⟨n, hn⟩ => h.mem_of_red_iterate n T hT _ hn

/-- A strict system exists iff some balanced pair with nonempty tracks has a
finite, coincidence-free factor set (Theorem A(5) and its converse). -/
theorem exists_strictSystem_iff {s : α → List α} :
    (∃ C, StrictSystem s C) ↔ ∃ T : List α × List α, Equiv1 T.1 T.2 ∧ T.1 ≠ [] ∧
      (factorSet s T).Finite ∧ ∀ U ∈ factorSet s T, U.1 ≠ U.2 := by
  constructor
  · rintro ⟨C, h⟩
    obtain ⟨T, hT⟩ := h.nonempty
    exact ⟨T, h.equiv1 T hT, (h.isBlock T hT).1, (C.finite_toSet).subset (h.factorSet_subset hT),
      fun U hU => h.noncoincident U (h.factorSet_subset hT hU)⟩
  · rintro ⟨T, hT, hne, hfin, hnc⟩
    exact ⟨_, strictSystem_of_factorSet hT hne hfin hnc⟩

/-! ### Productivity (`def:bpa`) -/

/-- `def:bpa`: a state is **productive** if some directed path of `B_σ`
(coincidence blocks terminal, `ChildNC`) from it reaches a coincidence block. -/
def Productive (s : α → List α) (T : List α × List α) : Prop :=
  ∃ U, Relation.ReflTransGen (ChildNC s) T U ∧ U.1 = U.2

/-- `def:bpa`: the balanced pair algorithm started at `T₀` **terminates with
coincidence** if the set of states reachable from `T₀` in `B_σ` is finite and
every one of them is productive. -/
def TerminatesWithCoincidence (s : α → List α) (T₀ : List α × List α) : Prop :=
  {U | Relation.ReflTransGen (ChildNC s) T₀ U}.Finite ∧
    ∀ U, Relation.ReflTransGen (ChildNC s) T₀ U → Productive s U

theorem productive_of_reflTransGen {s : α → List α} {T U : List α × List α}
    (hTU : Relation.ReflTransGen (ChildNC s) T U) (hU : Productive s U) : Productive s T :=
  let ⟨V, hUV, hV⟩ := hU
  ⟨V, hTU.trans hUV, hV⟩

/-- From a nonproductive state every state reachable in the full child graph is
reachable in `B_σ` and is noncoincident. -/
theorem reachable_of_not_productive {s : α → List α} {T U : List α × List α}
    (hT : ¬ Productive s T) (hTU : Relation.ReflTransGen (Child s) T U) :
    Relation.ReflTransGen (ChildNC s) T U ∧ U.1 ≠ U.2 := by
  induction hTU with
  | refl => exact ⟨.refl, fun h => hT ⟨T, .refl, h⟩⟩
  | tail _ hVU ih =>
    obtain ⟨hV, hVnc⟩ := ih
    have hU : Relation.ReflTransGen (ChildNC s) T _ := hV.tail ⟨hVnc, hVU⟩
    exact ⟨hU, fun h => hT ⟨_, hU, h⟩⟩

namespace StrictSystem

variable {s : α → List α} {C : Finset (List α × List α)} (h : StrictSystem s C)
include h

/-- **Productivity, (d).**  No path of the full child graph from a state of a
strict system reaches a coincidence block. -/
theorem no_coincidence_reachable {T U : List α × List α} (hT : T ∈ C)
    (hTU : Relation.ReflTransGen (Child s) T U) : U.1 ≠ U.2 :=
  h.noncoincident U (h.reflTransGen_mem hT hTU)

/-- **Productivity, (d).**  Every state of a strict system is nonproductive. -/
theorem not_productive {T : List α × List α} (hT : T ∈ C) : ¬ Productive s T :=
  fun ⟨_, hTU, he⟩ => h.no_coincidence_reachable hT (hTU.lift id fun _ _ h => h.2) he

/-- No path of `B_σ` that reaches a state of a strict system terminates with
coincidence. -/
theorem not_terminates {T₀ T : List α × List α} (hT : T ∈ C)
    (hpath : Relation.ReflTransGen (ChildNC s) T₀ T) : ¬ TerminatesWithCoincidence s T₀ :=
  fun ⟨_, hprod⟩ => h.not_productive hT (hprod T hpath)

/-- **Productivity, (d).**  A strict system that meets the vertex set
`bpaStatesNC s` of `B_σ` gives a seed whose balanced pair algorithm does not
terminate with coincidence. -/
theorem exists_seed_not_terminates [Fintype α] {T : List α × List α} (hT : T ∈ C)
    (hbpa : T ∈ bpaStatesNC s) :
    ∃ T₀ ∈ (seeds : Finset (List α × List α)), ¬ TerminatesWithCoincidence s T₀ :=
  let ⟨T₀, h₀, hpath⟩ := hbpa
  ⟨T₀, h₀, h.not_terminates hT hpath⟩

end StrictSystem

/-- **Converse of (d)** (the conditional finite-sink step): if the states
reachable from a seed in `B_σ` form a finite set and the algorithm from it does
not terminate with coincidence, a strict system meets `B_σ`. -/
theorem exists_strictSystem_of_not_terminates [Fintype α] {s : α → List α}
    {T₀ : List α × List α} (h₀ : T₀ ∈ (seeds : Finset (List α × List α)))
    (hfin : {U | Relation.ReflTransGen (ChildNC s) T₀ U}.Finite)
    (hnt : ¬ TerminatesWithCoincidence s T₀) :
    ∃ C : Finset (List α × List α), StrictSystem s C ∧ ∃ T ∈ C, T ∈ bpaStatesNC s := by
  obtain ⟨U, hU, hnp⟩ : ∃ U, Relation.ReflTransGen (ChildNC s) T₀ U ∧ ¬ Productive s U := by
    by_contra hc
    exact hnt ⟨hfin, fun U hU => Classical.byContradiction fun hp => hc ⟨U, hU, hp⟩⟩
  have hUb : U ∈ bpaStatesNC s := ⟨T₀, h₀, hU⟩
  have hB : IsBlock U := bpaStates_isBlock s U (bpaStatesNC_subset_bpaStates s hUb)
  have hsub : factorSet s U ⊆ {V | Relation.ReflTransGen (ChildNC s) T₀ V} := by
    rw [factorSet_eq_reachable hB]
    intro V hV
    exact hU.trans (reachable_of_not_productive hnp hV).1
  have hfin' := hfin.subset hsub
  have hnc : ∀ V ∈ factorSet s U, V.1 ≠ V.2 := by
    rw [factorSet_eq_reachable hB]
    exact fun V hV => (reachable_of_not_productive hnp hV).2
  refine ⟨_, strictSystem_of_factorSet hB.2.1 hB.1 hfin' hnc, U, ?_, hUb⟩
  rw [Set.Finite.mem_toFinset, factorSet_eq_reachable hB]
  exact Relation.ReflTransGen.refl

/-- If every pair of distinct letters has a left strong-coincidence witness, the
balanced pair algorithm terminates with coincidence from every seed whose
reachable set in `B_σ` is finite. -/
theorem terminates_of_strongCoincidence [Fintype α] {s : α → List α}
    (hw : ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') {T₀ : List α × List α}
    (h₀ : T₀ ∈ (seeds : Finset (List α × List α)))
    (hfin : {U | Relation.ReflTransGen (ChildNC s) T₀ U}.Finite) :
    TerminatesWithCoincidence s T₀ := by
  by_contra hnt
  obtain ⟨C, hC, -⟩ := exists_strictSystem_of_not_terminates h₀ hfin hnt
  exact no_strictSystem_of_strongCoincidence hw C hC

/-! ### Strict components -/

/-- A **strict component**: a strict system that is strongly connected on states
up to side swap (every `T` reaches `U` or `U.swap` by a nonempty child path).
Taking `T = U` makes it recurrent. -/
structure StrictComponent (s : α → List α) (C : Finset (List α × List α)) : Prop
    extends StrictSystem s C where
  connected : ∀ T ∈ C, ∀ U ∈ C,
    Relation.TransGen (Child s) T U ∨ Relation.TransGen (Child s) T U.swap

namespace StrictComponent

variable {s : α → List α} {C : Finset (List α × List α)}

/-- The swap closure of a strict component is a strict component. -/
theorem swapClosure (h : StrictComponent s C) : StrictComponent s (swapClosureF C) := by
  refine ⟨h.toStrictSystem.swapClosure, fun T hT U hU => ?_⟩
  have lift : ∀ {V W : List α × List α}, Relation.TransGen (Child s) V W →
      Relation.TransGen (Child s) V.swap W.swap :=
    fun hVW => hVW.lift Prod.swap fun _ _ h => child_swap h
  rcases mem_swapClosureF.1 hT with hT | hT <;> rcases mem_swapClosureF.1 hU with hU | hU
  · exact h.connected T hT U hU
  · rcases h.connected T hT _ hU with h1 | h1
    · exact Or.inr h1
    · exact Or.inl (by simpa using h1)
  · rcases h.connected _ hT U hU with h1 | h1
    · exact Or.inr (by simpa using lift h1)
    · exact Or.inl (by simpa using lift h1)
  · rcases h.connected _ hT _ hU with h1 | h1
    · exact Or.inl (by simpa using lift h1)
    · exact Or.inr (by simpa using lift h1)

/-- In a strict component, paths of the full child graph are paths of `B_σ`. -/
theorem transGen_childNC (h : StrictSystem s C) {T U : List α × List α} (hT : T ∈ C)
    (hTU : Relation.TransGen (Child s) T U) : Relation.TransGen (ChildNC s) T U := by
  induction hTU with
  | single hTU => exact .single ⟨h.noncoincident _ hT, hTU⟩
  | tail hTV hVU ih =>
    exact ih.tail ⟨h.noncoincident _ (h.transGen_mem hT hTV), hVU⟩

/-- A strict system with a successor map `f` (`f T` a child of `T`) whose orbits pass
through every state is a strict component.  The covering hypothesis is decidable, for
the `decide` controls. -/
theorem of_cycle (h : StrictSystem s C) (f : List α × List α → List α × List α)
    (hf : ∀ T ∈ C, f T ∈ red (subst s T.1) (subst s T.2))
    (hcov : ∀ T ∈ C, ∀ U ∈ C, ∃ k < C.card, f^[k + 1] T = U) : StrictComponent s C := by
  have key : ∀ {T : List α × List α}, T ∈ C → ∀ k : ℕ,
      Relation.TransGen (Child s) T (f^[k + 1] T) ∧ f^[k + 1] T ∈ C := by
    intro T hT k
    induction k with
    | zero => exact ⟨.single (hf T hT), h.closed T hT _ (hf T hT)⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.tail (hf _ ih.2), h.closed _ ih.2 _ (hf _ ih.2)⟩
  refine ⟨h, fun T hT U hU => Or.inl ?_⟩
  obtain ⟨k, -, hk⟩ := hcov T hT U hU
  exact hk ▸ (key hT k).1

end StrictComponent

/-! ### `N_C` of a strict component is strongly connected -/

section Rep

variable {S : ChildSystem α} (P : Normalisation S)

/-- The representative of a state: `T` itself or `T.swap`, whichever lies in `R`. -/
def repOf {T : List α × List α} (hT : T ∈ S.C) : P.Rep :=
  if hR : T ∈ P.R then ⟨T, hR⟩ else ⟨T.swap, (P.cover T hT).resolve_left hR⟩

theorem repOf_spec {T : List α × List α} (hT : T ∈ S.C) :
    (repOf P hT).1 = T ∨ (repOf P hT).1 = T.swap := by
  unfold repOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem repOf_rep (i : P.Rep) (hi : i.1 ∈ S.C) : repOf P hi = i := by
  unfold repOf
  split_ifs with hR
  · rfl
  · exact absurd i.2 hR

theorem repOf_swap_rep (i : P.Rep) (hi : i.1.swap ∈ S.C) : repOf P hi = i := by
  unfold repOf
  split_ifs with hR
  · exact absurd hR (P.not_both _ i.2)
  · exact Subtype.ext (Prod.swap_swap _)

/-- A positive entry of `N_C = A + B`: `i` or `i.swap` is a child of `j`. -/
theorem nrep_pos_iff (i j : P.Rep) :
    0 < P.Nrep i j ↔ i.1 ∈ S.children j.1 ∨ i.1.swap ∈ S.children j.1 := by
  simp only [Normalisation.Nrep, Normalisation.A, Normalisation.B, Matrix.add_apply,
    Matrix.of_apply, Nat.add_pos_iff_pos_or_pos, List.count_pos_iff]

/-- A child edge `V → W` gives a positive entry `N_C (rep W) (rep V)`. -/
theorem nrep_pos_of_child {V W : List α × List α} (hV : V ∈ S.C) (hW : W ∈ S.C)
    (hVW : W ∈ S.children V) : 0 < P.Nrep (repOf P hW) (repOf P hV) := by
  rw [nrep_pos_iff]
  rcases repOf_spec P hV with hv | hv <;> rcases repOf_spec P hW with hw | hw <;>
    rw [hv, hw]
  · exact Or.inl hVW
  · exact Or.inr (by simpa using hVW)
  · rw [P.children_swap V hV]
    exact Or.inr (by simpa using List.mem_map_of_mem (f := Prod.swap) hVW)
  · rw [P.children_swap V hV]
    exact Or.inl (List.mem_map_of_mem hVW)

end Rep

namespace StrictComponent

variable {s : α → List α} {C : Finset (List α × List α)}

/-- **`N_C` of a strict component is strongly connected** (`Psc.PerronCore`), for
every normalisation of its child system: the hypothesis `hSC` of
`Psc.CocycleSpectrum`, `Psc.KernelCofactor` and `Psc.Degree4Floor`. -/
theorem nrep_stronglyConnected (h : StrictComponent s C) (hs : ∀ a, s a ≠ [])
    (P : Normalisation (h.toStrictSystem.toChildSystem hs)) :
    Psc.PerronCore.StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ)) := by
  have key : ∀ {T U : List α × List α} (hT : T ∈ C), Relation.TransGen (Child s) T U →
      ∃ hU : U ∈ C, Relation.TransGen (fun a b => 0 < (P.Nrep.map (Nat.cast : ℕ → ℝ)) a b)
        (repOf P (S := h.toStrictSystem.toChildSystem hs) hU) (repOf P hT) := by
    intro T U hT hTU
    induction hTU with
    | single hTU =>
      have hU := h.closed _ hT _ hTU
      refine ⟨hU, .single ?_⟩
      rw [Matrix.map_apply, Nat.cast_pos]
      exact nrep_pos_of_child P hT hU hTU
    | tail _ hVU ih =>
      obtain ⟨hV, ih⟩ := ih
      have hU := h.closed _ hV _ hVU
      refine ⟨hU, .head ?_ ih⟩
      rw [Matrix.map_apply, Nat.cast_pos]
      exact nrep_pos_of_child P hV hU hVU
  intro i j
  have hi : i.1 ∈ C := P.sub i.2
  have hj : j.1 ∈ C := P.sub j.2
  rcases h.connected _ hj _ hi with hp | hp
  · obtain ⟨hU, hpath⟩ := key hj hp
    rwa [repOf_rep P i hU, repOf_rep P j hj] at hpath
  · obtain ⟨hU, hpath⟩ := key hj hp
    rwa [repOf_swap_rep P i hU, repOf_rep P j hj] at hpath

/-- `N_C` strongly connected for the lexicographic normalisation of the swap
closure of a strict component. -/
theorem lexNorm_stronglyConnected [LinearOrder α] (h : StrictComponent s C)
    (hs : ∀ a, s a ≠ []) :
    Psc.PerronCore.StronglyConnected ((h.toStrictSystem.lexNorm hs).Nrep.map (Nat.cast : ℕ → ℝ)) :=
  h.swapClosure.nrep_stronglyConnected hs (h.toStrictSystem.lexNorm hs)

end StrictComponent

/-! ### The manuscript's strict component of `B_σ` -/

/-- `def:bpa`'s **strict component**, read on ordered pairs: the swap-closed set
`C` of both orientations of the states of a finite closed nonproductive
recurrent noncoincident SCC of `B_σ` (states are pairs up to side swap).
`connected` is strong connectivity of the SCC in the quotient by side swap,
with nonempty paths (so the SCC is recurrent). -/
structure BpaStrictComponent [Fintype α] (s : α → List α) (C : Finset (List α × List α)) :
    Prop where
  nonempty : C.Nonempty
  vertex : ∀ T ∈ C, T ∈ bpaStatesNC s
  swap_mem : ∀ T ∈ C, T.swap ∈ C
  noncoincident : ∀ T ∈ C, T.1 ≠ T.2
  closed : ∀ T ∈ C, ∀ U, Child s T U → U.1 ≠ U.2 → U ∈ C
  nonproductive : ∀ T ∈ C, ¬ Productive s T
  connected : ∀ T ∈ C, ∀ U ∈ C,
    Relation.TransGen (ChildNC s) T U ∨ Relation.TransGen (ChildNC s) T U.swap

/-- `def:bpa`: a closed noncoincident set of states is nonproductive iff no state
in it has a coincidence child. -/
theorem nonproductive_iff_no_coincidence_child {s : α → List α} {C : Finset (List α × List α)}
    (hnc : ∀ T ∈ C, T.1 ≠ T.2) (hcl : ∀ T ∈ C, ∀ U, Child s T U → U.1 ≠ U.2 → U ∈ C) :
    (∀ T ∈ C, ¬ Productive s T) ↔ ∀ T ∈ C, ∀ U, Child s T U → U.1 ≠ U.2 := by
  constructor
  · intro hnp T hT U hTU hU
    exact hnp T hT ⟨U, .single ⟨hnc T hT, hTU⟩, hU⟩
  · intro hch T hT ⟨U, hTU, hU⟩
    have : ∀ V, Relation.ReflTransGen (ChildNC s) T V → V ∈ C := by
      intro V hV
      induction hV with
      | refl => exact hT
      | tail _ hVW ih => exact hcl _ ih _ hVW.2 (hch _ ih _ hVW.2)
    exact hnc U (this U hTU) hU

namespace BpaStrictComponent

variable [Fintype α] {s : α → List α} {C : Finset (List α × List α)}

/-- A strict component of `B_σ` is a `StrictComponent`. -/
theorem toStrictComponent (h : BpaStrictComponent s C) : StrictComponent s C where
  nonempty := h.nonempty
  isBlock T hT := bpaStates_isBlock s T (bpaStatesNC_subset_bpaStates s (h.vertex T hT))
  noncoincident := h.noncoincident
  closed T hT U hU :=
    h.closed T hT U hU ((nonproductive_iff_no_coincidence_child h.noncoincident h.closed).1
      h.nonproductive T hT U hU)
  connected T hT U hU := (h.connected T hT U hU).imp
    (fun p => p.lift id fun _ _ h => h.2) (fun p => p.lift id fun _ _ h => h.2)

/-- A strict component of `B_σ` contains every state of `B_σ` reachable from it,
so it is the SCC of each of its states. -/
theorem reachable_mem (h : BpaStrictComponent s C) {T U : List α × List α} (hT : T ∈ C)
    (hTU : Relation.ReflTransGen (ChildNC s) T U) : U ∈ C :=
  h.toStrictComponent.reflTransGen_mem hT (hTU.lift id fun _ _ h => h.2)

end BpaStrictComponent

/-- Conversely, a swap-closed `StrictComponent` that meets `B_σ` is a strict
component of `B_σ`. -/
theorem StrictComponent.toBpa [Fintype α] {s : α → List α} {C : Finset (List α × List α)}
    (h : StrictComponent s C) (hswap : ∀ T ∈ C, T.swap ∈ C)
    (hmeet : ∃ T ∈ C, T ∈ bpaStatesNC s) : BpaStrictComponent s C where
  nonempty := h.nonempty
  vertex U hU := by
    obtain ⟨T, hT, hTb⟩ := hmeet
    obtain ⟨T₀, h₀, hpath⟩ := bpaStatesNC_subset_bpaStates s hTb
    have hU' : U ∈ bpaStates s := by
      rcases h.connected T hT U hU with hp | hp
      · exact ⟨T₀, h₀, hpath.trans hp.to_reflTransGen⟩
      · simpa using bpaStates_swapClosed s _ ⟨T₀, h₀, hpath.trans hp.to_reflTransGen⟩
    exact (mem_bpaStatesNC_iff s (h.noncoincident U hU)).2 hU'
  swap_mem := hswap
  noncoincident := h.noncoincident
  closed T hT U hU _ := h.closed T hT U hU
  nonproductive T hT := h.toStrictSystem.not_productive hT
  connected T hT U hU := (h.connected T hT U hU).imp
    (StrictComponent.transGen_childNC h.toStrictSystem hT)
    (StrictComponent.transGen_childNC h.toStrictSystem hT)

/-! ### (e) Mismatch density -/

/-- The number of mismatched positions `i < min(|u|, |v|)` with `u[i] ≠ v[i]`. -/
def mismatch (u v : List α) : ℕ := (u.zip v).countP fun p => decide (p.1 ≠ p.2)

@[simp] theorem mismatch_nil_left (v : List α) : mismatch [] v = 0 := rfl

theorem mismatch_cons (a b : α) (u v : List α) :
    mismatch (a :: u) (b :: v) = mismatch u v + if a = b then 0 else 1 := by
  simp only [mismatch, List.zip_cons_cons, List.countP_cons, decide_not]
  by_cases h : a = b <;> simp [h]

theorem mismatch_append {u v : List α} (u' v' : List α) (h : u.length = v.length) :
    mismatch (u ++ u') (v ++ v') = mismatch u v + mismatch u' v' := by
  simp only [mismatch, List.zip_append h, List.countP_append]

/-- Two distinct words of equal length have a mismatched position. -/
theorem mismatch_pos {u v : List α} (hl : u.length = v.length) (hne : u ≠ v) :
    0 < mismatch u v := by
  induction u generalizing v with
  | nil => exact absurd (List.length_eq_zero_iff.mp hl.symm).symm hne
  | cons a u ih =>
    obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil (l := v) fun h0 => by simp [h0] at hl
    rw [mismatch_cons]
    by_cases hab : a = b
    · subst hab
      have := ih (v := v) (by simpa using hl) fun e => hne (e ▸ rfl)
      omega
    · simp [hab]

/-- A concatenation of noncoincident equal-length blocks of length `≤ L` has at
least `|top| / L` mismatched positions. -/
theorem length_le_mul_mismatch (L : ℕ) (bs : List (List α × List α))
    (hbs : ∀ U ∈ bs, U.1.length ≤ L ∧ U.1.length = U.2.length ∧ U.1 ≠ U.2) :
    ((bs.map Prod.fst).flatten).length ≤
      L * mismatch (bs.map Prod.fst).flatten (bs.map Prod.snd).flatten := by
  induction bs with
  | nil => simp
  | cons U bs ih =>
    obtain ⟨h1, h2, h3⟩ := hbs U (by simp)
    have ih' := ih fun V hV => hbs V (by simp [hV])
    have hm := mismatch_pos h2 h3
    have hL : L ≤ L * mismatch U.1 U.2 := Nat.le_mul_of_pos_right L hm
    simp only [List.map_cons, List.flatten_cons, List.length_append, mismatch_append _ _ h2,
      Nat.mul_add]
    omega

/-- **(e) Mismatch density.**  If every state of a strict system has length
`≤ L`, then for every state `T` and every `n`, `σⁿ(T.1)` and `σⁿ(T.2)` disagree
at `≥ |σⁿ(T.1)| / L` positions. -/
theorem StrictSystem.mismatch_density {s : α → List α} {C : Finset (List α × List α)}
    (h : StrictSystem s C) {L : ℕ} (hL : ∀ U ∈ C, U.1.length ≤ L) {T : List α × List α}
    (hT : T ∈ C) (n : ℕ) :
    ((subst s)^[n] T.1).length ≤ L * mismatch ((subst s)^[n] T.1) ((subst s)^[n] T.2) := by
  have hlen := (equiv1_iterate_subst s n (h.equiv1 T hT)).length_eq
  obtain ⟨bs, hbs⟩ : ∃ bs, bs = red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := ⟨_, rfl⟩
  have e1 : (bs.map Prod.fst).flatten = (subst s)^[n] T.1 := hbs ▸ red_top hlen
  have e2 : (bs.map Prod.snd).flatten = (subst s)^[n] T.2 := hbs ▸ red_bot hlen
  rw [← e1, ← e2]
  refine length_le_mul_mismatch L bs fun U hU => ?_
  have hUC := h.mem_of_red_iterate n T hT U (hbs ▸ hU)
  exact ⟨hL U hUC, (h.isBlock U hUC).2.1.length_eq, h.noncoincident U hUC⟩

/-- The largest top-track length of a state. -/
def maxLen (C : Finset (List α × List α)) : ℕ := C.sup fun U => U.1.length

omit [DecidableEq α] in
theorem le_maxLen {C : Finset (List α × List α)} {U : List α × List α} (hU : U ∈ C) :
    U.1.length ≤ maxLen C :=
  Finset.le_sup (f := fun U : List α × List α => U.1.length) hU

/-- **(e)** with `L` the largest state length. -/
theorem StrictSystem.mismatch_density_maxLen {s : α → List α} {C : Finset (List α × List α)}
    (h : StrictSystem s C) {T : List α × List α} (hT : T ∈ C) (n : ℕ) :
    ((subst s)^[n] T.1).length ≤ maxLen C * mismatch ((subst s)^[n] T.1) ((subst s)^[n] T.2) :=
  h.mismatch_density (fun _ hU => le_maxLen hU) hT n

/-! ### (f) The first defect degree -/

/-- `N_x(w)`: the number of embeddings of `x` in `w` as a scattered subword
(the multiplicity of `x` in `w.sublists`, which lists all `2^|w|` index
choices). -/
def nsub (x w : List α) : ℕ := w.sublists.count x

theorem nsub_eq_count_sublists' (x w : List α) : nsub x w = w.sublists'.count x :=
  (List.sublists_perm_sublists' w).count_eq x

theorem nsub_nil_right (x : List α) : nsub x [] = if x = [] then 1 else 0 := by
  rw [nsub_eq_count_sublists', List.sublists'_nil, List.count_singleton]
  by_cases hx : x = [] <;> simp [hx]

theorem nsub_cons_right (x : List α) (c : α) (w : List α) :
    nsub x (c :: w) = nsub x w + (List.map (List.cons c) w.sublists').count x := by
  rw [nsub_eq_count_sublists', nsub_eq_count_sublists', List.sublists'_cons, List.count_append]

theorem nsub_nil_left (w : List α) : nsub [] w = 1 := by
  induction w with
  | nil => simp [nsub_nil_right]
  | cons c w ih =>
    rw [nsub_cons_right, ih, List.count_eq_zero.2]
    simp

/-- The recursion `N_{a x}(c w) = [c = a] N_x(w) + N_{a x}(w)`. -/
theorem nsub_cons_cons (a : α) (x : List α) (c : α) (w : List α) :
    nsub (a :: x) (c :: w) = (if c = a then nsub x w else 0) + nsub (a :: x) w := by
  rw [nsub_cons_right, Nat.add_comm]
  congr 1
  by_cases hca : c = a
  · subst hca
    rw [ite_eq_left rfl, List.count_map_of_injective _ _ List.cons_injective,
      nsub_eq_count_sublists']
  · rw [ite_eq_right hca, List.count_eq_zero]
    simp only [List.mem_map, List.cons.injEq, not_exists, not_and]
    exact fun _ _ h _ => hca h

theorem nsub_single (a : α) (w : List α) : nsub [a] w = w.count a := by
  induction w with
  | nil => simp [nsub_nil_right]
  | cons c w ih =>
    rw [nsub_cons_cons, ih, nsub_nil_left, List.count_cons]
    by_cases h : c = a
    · simp [h, Nat.add_comm]
    · simp [h]

/-- `N_{ab} = n2`. -/
theorem nsub_two (a b : α) (w : List α) : nsub [a, b] w = n2 w a b := by
  induction w with
  | nil => simp [nsub_nil_right, n2]
  | cons c w ih => rw [nsub_cons_cons, ih, nsub_single, n2]

/-- `N_{abc} = n3`. -/
theorem nsub_three (a b c : α) (w : List α) : nsub [a, b, c] w = n3 w a b c := by
  induction w with
  | nil => simp [nsub_nil_right]
  | cons x w ih => rw [nsub_cons_cons, ih, nsub_two, n3_cons]

/-- `N_{abcd} = Psc.Defect4.n4`. -/
theorem nsub_four (a b c d : α) (w : List α) : nsub [a, b, c, d] w = Psc.Defect4.n4 w a b c d := by
  induction w with
  | nil => simp [nsub_nil_right]
  | cons x w ih => rw [nsub_cons_cons, ih, nsub_three, Psc.Defect4.n4_cons]

theorem nsub_eq_zero_of_length_lt {x w : List α} (h : w.length < x.length) : nsub x w = 0 :=
  List.count_eq_zero.2 fun hm => absurd (List.mem_sublists.1 hm).length_le (by omega)

theorem nsub_eq_zero_of_ne {x w : List α} (hl : x.length = w.length) (hne : x ≠ w) :
    nsub x w = 0 :=
  List.count_eq_zero.2 fun hm => hne ((List.mem_sublists.1 hm).eq_of_length hl)

theorem nsub_self (w : List α) : nsub w w = 1 := by
  induction w with
  | nil => simp [nsub_nil_right]
  | cons c w ih =>
    rw [nsub_cons_cons, ite_eq_left rfl, ih, nsub_eq_zero_of_length_lt (by simp)]

/-- The defect `K(u, v)` at the word `x`: `N_x(u) − N_x(v)`.  `K_r(u, v)` is its
restriction to the words of length `r`. -/
def Kx (u v x : List α) : ℤ := (nsub x u : ℤ) - nsub x v

/-- `K_r(u, v) ≠ 0`. -/
def KNe (r : ℕ) (u v : List α) : Prop := ∃ x : List α, x.length = r ∧ Kx u v x ≠ 0

theorem kx_ne_zero {u v x : List α} : Kx u v x ≠ 0 ↔ nsub x u ≠ nsub x v := by
  simp [Kx, sub_eq_zero]

theorem kx_two (u v : List α) (a b : α) : Kx u v [a, b] = Psc.Intertwiner2.K2 u v a b := by
  simp [Kx, Psc.Intertwiner2.K2, nsub_two]

theorem kx_three (u v : List α) (a b c : α) :
    Kx u v [a, b, c] = Psc.Intertwiner3.K3 u v a b c := by
  simp [Kx, Psc.Intertwiner3.K3, nsub_three]

theorem kx_four (u v : List α) (a b c d : α) :
    Kx u v [a, b, c, d] = Psc.Defect4.K4 u v a b c d := by
  simp [Kx, Psc.Defect4.K4, nsub_four]

theorem not_kNe_zero (u v : List α) : ¬ KNe 0 u v := by
  rintro ⟨x, hx, hK⟩
  rw [List.length_eq_zero_iff.mp hx] at hK
  simp [Kx, nsub_nil_left] at hK

theorem kNe_one_iff {u v : List α} : KNe 1 u v ↔ ¬ Equiv1 u v := by
  constructor
  · rintro ⟨x, hx, hK⟩ hE
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hx
    exact kx_ne_zero.1 hK (by rw [nsub_single, nsub_single, hE a])
  · intro hE
    obtain ⟨a, ha⟩ : ∃ a, u.count a ≠ v.count a := by
      by_contra hc
      exact hE fun a => Classical.byContradiction fun h => hc ⟨a, h⟩
    exact ⟨[a], rfl, kx_ne_zero.2 (by rwa [nsub_single, nsub_single])⟩

theorem kNe_two_iff {u v : List α} :
    KNe 2 u v ↔ ∃ a b, Psc.Intertwiner2.K2 u v a b ≠ 0 := by
  constructor
  · rintro ⟨x, hx, hK⟩
    obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hx
    exact ⟨a, b, kx_two u v a b ▸ hK⟩
  · rintro ⟨a, b, hK⟩
    exact ⟨[a, b], rfl, (kx_two u v a b).symm ▸ hK⟩

theorem kNe_three_iff {u v : List α} :
    KNe 3 u v ↔ ∃ a b c, Psc.Intertwiner3.K3 u v a b c ≠ 0 := by
  constructor
  · rintro ⟨x, hx, hK⟩
    obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hx
    exact ⟨a, b, c, kx_three u v a b c ▸ hK⟩
  · rintro ⟨a, b, c, hK⟩
    exact ⟨[a, b, c], rfl, (kx_three u v a b c).symm ▸ hK⟩

theorem kNe_four_iff {u v : List α} :
    KNe 4 u v ↔ ∃ a b c d, Psc.Defect4.K4 u v a b c d ≠ 0 := by
  constructor
  · rintro ⟨x, hx, hK⟩
    match x, hx with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, kx_four u v a b c d ▸ hK⟩
  · rintro ⟨a, b, c, d, hK⟩
    exact ⟨[a, b, c, d], rfl, (kx_four u v a b c d).symm ▸ hK⟩

theorem equiv2_iff_not_kNe {u v : List α} : Equiv2 u v ↔ ¬ KNe 1 u v ∧ ¬ KNe 2 u v := by
  rw [kNe_one_iff, kNe_two_iff, not_not, not_exists]
  simp only [not_exists, not_not, Psc.Intertwiner2.K2, sub_eq_zero, Nat.cast_inj]
  exact Iff.rfl

theorem equiv3_iff_not_kNe {u v : List α} :
    Psc.Defect4.Equiv3 u v ↔ ¬ KNe 1 u v ∧ ¬ KNe 2 u v ∧ ¬ KNe 3 u v := by
  rw [Psc.Defect4.Equiv3, equiv2_iff_not_kNe, kNe_three_iff]
  simp only [not_exists, not_not, Psc.Intertwiner3.K3, sub_eq_zero, Nat.cast_inj, and_assoc]

/-- A noncoincident equal-length pair has a defect at degree `|u|` (the word `u`
itself embeds once in `u` and not in `v`). -/
theorem kNe_length {u v : List α} (hl : u.length = v.length) (hne : u ≠ v) :
    KNe u.length u v :=
  ⟨u, rfl, kx_ne_zero.2 (by rw [nsub_self, nsub_eq_zero_of_ne hl hne]; exact one_ne_zero)⟩

/-- `C` has a defect at degree `r`: `K_r ≠ 0` on some state. -/
def HasDefect (C : Finset (List α × List α)) (r : ℕ) : Prop := ∃ T ∈ C, KNe r T.1 T.2

/-- The **first defect degree** of `C`: the least `r` with `K_r ≠ 0` on some
state (`0` if there is none; see `hasDefect_defectDegree`). -/
noncomputable def defectDegree (C : Finset (List α × List α)) : ℕ := sInf {r | HasDefect C r}

section DefectDegree

variable {C : Finset (List α × List α)}

theorem not_hasDefect_zero (C : Finset (List α × List α)) : ¬ HasDefect C 0 :=
  fun ⟨T, _, hT⟩ => not_kNe_zero T.1 T.2 hT

theorem hasDefect_length {T : List α × List α} (hT : T ∈ C) (hl : T.1.length = T.2.length)
    (hne : T.1 ≠ T.2) : HasDefect C T.1.length := ⟨T, hT, kNe_length hl hne⟩

/-- The first defect degree exists once some state is a noncoincident
equal-length pair. -/
theorem hasDefect_defectDegree (h : ∃ T ∈ C, T.1.length = T.2.length ∧ T.1 ≠ T.2) :
    HasDefect C (defectDegree C) := by
  obtain ⟨T, hT, hl, hne⟩ := h
  exact Nat.sInf_mem (s := {r | HasDefect C r}) ⟨_, hasDefect_length hT hl hne⟩

/-- The first defect degree is at most the length of any noncoincident
equal-length state. -/
theorem defectDegree_le {T : List α × List α} (hT : T ∈ C) (hl : T.1.length = T.2.length)
    (hne : T.1 ≠ T.2) : defectDegree C ≤ T.1.length :=
  Nat.sInf_le (hasDefect_length hT hl hne)

theorem not_hasDefect_of_lt {k : ℕ} (hk : k < defectDegree C) : ¬ HasDefect C k :=
  Nat.notMem_of_lt_sInf hk

theorem defectDegree_eq_iff {r : ℕ} (hr : 0 < r) :
    defectDegree C = r ↔ HasDefect C r ∧ ∀ k < r, ¬ HasDefect C k := by
  constructor
  · rintro rfl
    refine ⟨?_, fun k hk => not_hasDefect_of_lt hk⟩
    by_contra hc
    have hempty : {r | HasDefect C r} = ∅ := by
      by_contra hne
      exact hc (Nat.sInf_mem (Set.nonempty_iff_ne_empty.2 hne))
    exact absurd (show defectDegree C = 0 by rw [defectDegree, hempty, Nat.sInf_empty]) hr.ne'
  · rintro ⟨hD, hlt⟩
    refine le_antisymm (Nat.sInf_le hD) (le_of_not_gt fun hlt' => hlt _ hlt' ?_)
    exact Nat.sInf_mem (s := {r | HasDefect C r}) ⟨r, hD⟩

/-- `defectDegree = 2` iff every state is balanced and `K₂ ≠ 0` on some state. -/
theorem defectDegree_eq_two_iff :
    defectDegree C = 2 ↔ (∀ T ∈ C, Equiv1 T.1 T.2) ∧
      ∃ T ∈ C, ∃ a b, Psc.Intertwiner2.K2 T.1 T.2 a b ≠ 0 := by
  rw [defectDegree_eq_iff (by norm_num)]
  constructor
  · rintro ⟨⟨T, hT, hK⟩, hlt⟩
    refine ⟨fun U hU => Classical.byContradiction fun hE =>
      hlt 1 (by norm_num) ⟨U, hU, kNe_one_iff.2 hE⟩, T, hT, kNe_two_iff.1 hK⟩
  · rintro ⟨hE, T, hT, hK⟩
    refine ⟨⟨T, hT, kNe_two_iff.2 hK⟩, fun k hk ⟨U, hU, hKU⟩ => ?_⟩
    interval_cases k
    · exact not_kNe_zero _ _ hKU
    · exact kNe_one_iff.1 hKU (hE U hU)

/-- `defectDegree = 3` iff every state is `∼₂` and `K₃ ≠ 0` on some state. -/
theorem defectDegree_eq_three_iff :
    defectDegree C = 3 ↔ (∀ T ∈ C, Equiv2 T.1 T.2) ∧
      ∃ T ∈ C, ∃ a b c, Psc.Intertwiner3.K3 T.1 T.2 a b c ≠ 0 := by
  rw [defectDegree_eq_iff (by norm_num)]
  constructor
  · rintro ⟨⟨T, hT, hK⟩, hlt⟩
    refine ⟨fun U hU => equiv2_iff_not_kNe.2 ⟨fun h => hlt 1 (by norm_num) ⟨U, hU, h⟩,
      fun h => hlt 2 (by norm_num) ⟨U, hU, h⟩⟩, T, hT, kNe_three_iff.1 hK⟩
  · rintro ⟨hE, T, hT, hK⟩
    refine ⟨⟨T, hT, kNe_three_iff.2 hK⟩, fun k hk ⟨U, hU, hKU⟩ => ?_⟩
    have h2 := equiv2_iff_not_kNe.1 (hE U hU)
    interval_cases k
    · exact not_kNe_zero _ _ hKU
    · exact h2.1 hKU
    · exact h2.2 hKU

/-- `defectDegree = 4` iff every state is `∼₃` and `K₄ ≠ 0` on some state. -/
theorem defectDegree_eq_four_iff :
    defectDegree C = 4 ↔ (∀ T ∈ C, Psc.Defect4.Equiv3 T.1 T.2) ∧
      ∃ T ∈ C, ∃ a b c d, Psc.Defect4.K4 T.1 T.2 a b c d ≠ 0 := by
  rw [defectDegree_eq_iff (by norm_num)]
  constructor
  · rintro ⟨⟨T, hT, hK⟩, hlt⟩
    refine ⟨fun U hU => equiv3_iff_not_kNe.2 ⟨fun h => hlt 1 (by norm_num) ⟨U, hU, h⟩,
      fun h => hlt 2 (by norm_num) ⟨U, hU, h⟩, fun h => hlt 3 (by norm_num) ⟨U, hU, h⟩⟩,
      T, hT, kNe_four_iff.1 hK⟩
  · rintro ⟨hE, T, hT, hK⟩
    refine ⟨⟨T, hT, kNe_four_iff.2 hK⟩, fun k hk ⟨U, hU, hKU⟩ => ?_⟩
    have h3 := equiv3_iff_not_kNe.1 (hE U hU)
    interval_cases k
    · exact not_kNe_zero _ _ hKU
    · exact h3.1 hKU
    · exact h3.2.1 hKU
    · exact h3.2.2 hKU

end DefectDegree

/-- For a strict system the first defect degree exists, is at least `2` (the
states are balanced) and at most the length of every state. -/
theorem StrictSystem.defectDegree_spec {s : α → List α} {C : Finset (List α × List α)}
    (h : StrictSystem s C) :
    HasDefect C (defectDegree C) ∧ 2 ≤ defectDegree C ∧
      ∀ T ∈ C, defectDegree C ≤ T.1.length := by
  obtain ⟨T, hT⟩ := h.nonempty
  have hex : ∃ T ∈ C, T.1.length = T.2.length ∧ T.1 ≠ T.2 :=
    ⟨T, hT, (h.equiv1 T hT).length_eq, h.noncoincident T hT⟩
  refine ⟨hasDefect_defectDegree hex, ?_, fun U hU =>
    defectDegree_le hU (h.equiv1 U hU).length_eq (h.noncoincident U hU)⟩
  by_contra hlt
  have hD := hasDefect_defectDegree hex
  obtain ⟨U, hU, hK⟩ := hD
  interval_cases hd : defectDegree C
  · exact not_kNe_zero _ _ hK
  · exact kNe_one_iff.1 hK (h.equiv1 U hU)

/-! #### The three-letter coordinates `kw`, `k3Vec`, `k4Vec` -/

section Fin3

theorem exists_k2_ne_iff_kw {u v : List (Fin 3)} (h : Equiv1 u v) :
    (∃ a b, Psc.Intertwiner2.K2 u v a b ≠ 0) ↔ Psc.Intertwiner2.kw u v ≠ 0 := by
  constructor
  · rintro ⟨a, b, hK⟩ hkw
    have h0 : ∀ I, Psc.Intertwiner2.K2 u v (Psc.Cyclicity.pairFst I)
        (Psc.Cyclicity.pairSnd I) = 0 := fun I => congrFun hkw I
    have h01 : Psc.Intertwiner2.K2 u v 0 1 = 0 := h0 0
    have h02 : Psc.Intertwiner2.K2 u v 0 2 = 0 := h0 1
    have h12 : Psc.Intertwiner2.K2 u v 1 2 = 0 := h0 2
    fin_cases a <;> fin_cases b <;> simp at hK <;>
      first
      | exact hK (Psc.Intertwiner2.k2_self h _)
      | exact hK h01 | exact hK h02 | exact hK h12
      | exact hK (by rw [Psc.Intertwiner2.k2_antisymm h (by decide)]; simp [h01, h02, h12])
  · intro hkw
    obtain ⟨I, hI⟩ := Function.ne_iff.1 hkw
    exact ⟨_, _, hI⟩

theorem k3Vec_ne_zero_iff {u v : List (Fin 3)} :
    Psc.Lie3.k3Vec u v ≠ 0 ↔ ∃ a b c, Psc.Intertwiner3.K3 u v a b c ≠ 0 := by
  constructor
  · intro hK
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hK (funext fun a => funext fun b => funext fun c => by
      simp [Psc.Lie3.k3Vec, hc a b c])
  · rintro ⟨a, b, c, hK⟩ h0
    have := congrFun (congrFun (congrFun h0 a) b) c
    simp only [Psc.Lie3.k3Vec, Pi.zero_apply, Int.cast_eq_zero] at this
    exact hK this

theorem k4Vec_ne_zero_iff {u v : List (Fin 3)} :
    Psc.Defect4Lie.k4Vec u v ≠ 0 ↔ ∃ a b c d, Psc.Defect4.K4 u v a b c d ≠ 0 := by
  constructor
  · intro hK
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hK (funext fun a => funext fun b => funext fun c => funext fun d => by
      simp [Psc.Defect4Lie.k4Vec, hc a b c d])
  · rintro ⟨a, b, c, d, hK⟩ h0
    have := congrFun (congrFun (congrFun (congrFun h0 a) b) c) d
    simp only [Psc.Defect4Lie.k4Vec, Pi.zero_apply, Int.cast_eq_zero] at this
    exact hK this

variable {C : Finset (List (Fin 3) × List (Fin 3))}

/-- **(f)** over `Fin 3`: `defectDegree = 2` iff all states are balanced and some
`kw ≠ 0` (the hypotheses of `Psc.Degree2Sector`). -/
theorem defectDegree_eq_two_iff_kw :
    defectDegree C = 2 ↔ (∀ T ∈ C, Equiv1 T.1 T.2) ∧ ∃ T ∈ C, Psc.Intertwiner2.kw T.1 T.2 ≠ 0 := by
  rw [defectDegree_eq_two_iff]
  constructor
  · rintro ⟨hE, T, hT, hK⟩
    exact ⟨hE, T, hT, (exists_k2_ne_iff_kw (hE T hT)).1 hK⟩
  · rintro ⟨hE, T, hT, hK⟩
    exact ⟨hE, T, hT, (exists_k2_ne_iff_kw (hE T hT)).2 hK⟩

/-- **(f)** over `Fin 3`: `defectDegree = 3` iff all states are `∼₂` and some
`k3Vec ≠ 0` (the hypotheses of `Psc.Degree3Sector`). -/
theorem defectDegree_eq_three_iff_k3Vec :
    defectDegree C = 3 ↔ (∀ T ∈ C, Equiv2 T.1 T.2) ∧ ∃ T ∈ C, Psc.Lie3.k3Vec T.1 T.2 ≠ 0 := by
  rw [defectDegree_eq_three_iff]
  simp only [k3Vec_ne_zero_iff]

/-- **(f)** over `Fin 3`: `defectDegree = 4` iff all states are `∼₃` and some
`k4Vec ≠ 0` (the hypotheses of `Psc.Degree4Floor`). -/
theorem defectDegree_eq_four_iff_k4Vec :
    defectDegree C = 4 ↔ (∀ T ∈ C, Psc.Defect4.Equiv3 T.1 T.2) ∧
      ∃ T ∈ C, Psc.Defect4Lie.k4Vec T.1 T.2 ≠ 0 := by
  rw [defectDegree_eq_four_iff]
  simp only [k4Vec_ne_zero_iff]

end Fin3

/-! ### The first-defect selection feeds the sector theorems

The sector theorems are stated for a normalisation `P` of a child system, with a
balance hypothesis on every state and a nonzero defect column `∃ j : P.Rep, …`.  For
every normalisation of the swap closure of a strict system these are supplied by
`defectDegree` (`defectDegree_eq_two_iff_kw`, `_three_iff_k3Vec`, `_four_iff_k4Vec`),
since the balance relations are symmetric and the defect vectors change sign under side
swap; the lemmas below are the selection steps, and Part 2 (g) composes them with the
sector theorems. -/

theorem equiv2_comm {u v : List α} (h : Equiv2 u v) : Equiv2 v u :=
  ⟨fun a => (h.1 a).symm, fun a b => (h.2 a b).symm⟩

theorem equiv3_comm {u v : List α} (h : Psc.Defect4.Equiv3 u v) : Psc.Defect4.Equiv3 v u :=
  ⟨equiv2_comm h.1, fun a b c => (h.2 a b c).symm⟩

/-- A property preserved by side swap holds on the swap closure once it holds on `C`. -/
theorem forall_swapClosureF {C : Finset (List α × List α)} {p : List α × List α → Prop}
    (hp : ∀ T, p T → p T.swap) (h : ∀ T ∈ C, p T) : ∀ T ∈ swapClosureF C, p T := by
  intro T hT
  rcases mem_swapClosureF.1 hT with hT | hT
  · exact h T hT
  · simpa using hp _ (h _ hT)

section Selection

theorem k3Vec_swap (u v : List (Fin 3)) : Psc.Lie3.k3Vec v u = - Psc.Lie3.k3Vec u v := by
  funext a b c
  simp only [Psc.Lie3.k3Vec, Pi.neg_apply]
  rw [Psc.Intertwiner3.k3_swap, Int.cast_neg]

theorem k4Vec_swap (u v : List (Fin 3)) :
    Psc.Defect4Lie.k4Vec v u = - Psc.Defect4Lie.k4Vec u v := by
  funext a b c d
  simp only [Psc.Defect4Lie.k4Vec, Pi.neg_apply]
  rw [Psc.Defect4.k4_swap, Int.cast_neg]

variable {S : ChildSystem (Fin 3)} (P : Normalisation S)

/-- A state with `kw ≠ 0` gives a representative with `kw ≠ 0`. -/
theorem exists_rep_kw {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ S.C)
    (hK : Psc.Intertwiner2.kw T.1 T.2 ≠ 0) :
    ∃ j : P.Rep, Psc.Intertwiner2.kw j.1.1 j.1.2 ≠ 0 := by
  refine ⟨repOf P hT, ?_⟩
  rcases repOf_spec P hT with e | e <;> rw [e]
  · exact hK
  · rw [Prod.fst_swap, Prod.snd_swap, Psc.Intertwiner2.kw_swap]; exact neg_ne_zero.2 hK

/-- A state with `k3Vec ≠ 0` gives a representative with `k3Vec ≠ 0`. -/
theorem exists_rep_k3Vec {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ S.C)
    (hK : Psc.Lie3.k3Vec T.1 T.2 ≠ 0) : ∃ j : P.Rep, Psc.Lie3.k3Vec j.1.1 j.1.2 ≠ 0 := by
  refine ⟨repOf P hT, ?_⟩
  rcases repOf_spec P hT with e | e <;> rw [e]
  · exact hK
  · rw [Prod.fst_swap, Prod.snd_swap, k3Vec_swap]; exact neg_ne_zero.2 hK

/-- A state with `k4Vec ≠ 0` gives a representative with `k4Vec ≠ 0`. -/
theorem exists_rep_k4Vec {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ S.C)
    (hK : Psc.Defect4Lie.k4Vec T.1 T.2 ≠ 0) :
    ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0 := by
  refine ⟨repOf P hT, ?_⟩
  rcases repOf_spec P hT with e | e <;> rw [e]
  · exact hK
  · rw [Prod.fst_swap, Prod.snd_swap, k4Vec_swap]; exact neg_ne_zero.2 hK

end Selection

/-! ### (c) Decide-checked strong-coincidence witnesses -/

/-- The index form of a witness, decidable over a finite alphabet: position `i`
of `σⁿ(c)` and position `j` of `σⁿ(c')` carry the same letter and have prefixes
with equal letter counts. -/
def IndexWitness (s : α → List α) (c c' : α) (n i j : ℕ) : Prop :=
  i < ((subst s)^[n] [c]).length ∧ ((subst s)^[n] [c])[i]? = ((subst s)^[n] [c'])[j]? ∧
    Equiv1 (((subst s)^[n] [c]).take i) (((subst s)^[n] [c']).take j)

instance [Fintype α] (s : α → List α) (c c' : α) (n i j : ℕ) :
    Decidable (IndexWitness s c c' n i j) := by
  unfold IndexWitness; infer_instance

/-- A witness at level `n`: `σⁿ(c) = P x Q`, `σⁿ(c') = P' x Q'`, `p(P) = p(P')`. -/
def WitnessAt (s : α → List α) (c c' : α) (n : ℕ) : Prop :=
  ∃ (P Q P' Q' : List α) (x : α), (subst s)^[n] [c] = P ++ x :: Q ∧
    (subst s)^[n] [c'] = P' ++ x :: Q' ∧ Equiv1 P P'

theorem strongCoincidenceWitness_iff_exists_witnessAt {s : α → List α} {c c' : α} :
    StrongCoincidenceWitness s c c' ↔ ∃ n, WitnessAt s c c' n :=
  ⟨fun ⟨n, P, Q, P', Q', x, h⟩ => ⟨n, P, Q, P', Q', x, h⟩,
    fun ⟨n, P, Q, P', Q', x, h⟩ => ⟨n, P, Q, P', Q', x, h⟩⟩

/-- A witness at level `n` in index form, and conversely. -/
theorem witnessAt_iff_index {s : α → List α} {c c' : α} {n : ℕ} :
    WitnessAt s c c' n ↔ ∃ i j, IndexWitness s c c' n i j := by
  constructor
  · rintro ⟨P, Q, P', Q', x, h1, h2, hP⟩
    refine ⟨P.length, P'.length, ?_, ?_, ?_⟩
    · rw [h1]; simp
    · rw [h1, h2, List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
      simp
    · rw [h1, h2, List.take_left' rfl, List.take_left' rfl]; exact hP
  · rintro ⟨i, j, hi, hx, hP⟩
    set u := (subst s)^[n] [c]
    set v := (subst s)^[n] [c']
    have hv : v[j]? = some u[i] := by rw [← hx]; exact List.getElem?_eq_getElem hi
    obtain ⟨hj, hvj⟩ := List.getElem?_eq_some_iff.1 hv
    refine ⟨u.take i, u.drop (i + 1), v.take j, v.drop (j + 1), u[i], ?_, ?_, hP⟩
    · rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
    · rw [← hvj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]

/-- A witness in index form is a left strong-coincidence witness, and conversely. -/
theorem strongCoincidenceWitness_iff_index {s : α → List α} {c c' : α} :
    StrongCoincidenceWitness s c c' ↔ ∃ n i j, IndexWitness s c c' n i j := by
  simp only [strongCoincidenceWitness_iff_exists_witnessAt, witnessAt_iff_index]

theorem witness_of_index {s : α → List α} {c c' : α} (n i j : ℕ)
    (h : IndexWitness s c c' n i j) : StrongCoincidenceWitness s c c' :=
  strongCoincidenceWitness_iff_index.2 ⟨n, i, j, h⟩

/-- An index witness is aligned: `p(P) = p(P')` forces `|P| = |P'|`. -/
theorem IndexWitness.aligned {s : α → List α} {c c' : α} {n i j : ℕ}
    (h : IndexWitness s c c' n i j) : i = j := by
  obtain ⟨hi, hx, hP⟩ := h
  have hj : j < ((subst s)^[n] [c']).length := by
    by_contra hj
    have hnone : ((subst s)^[n] [c'])[j]? = none := List.getElem?_eq_none (by omega)
    rw [hnone, List.getElem?_eq_getElem hi] at hx
    exact Option.some_ne_none _ hx
  have := hP.length_eq
  rw [List.length_take, List.length_take] at this
  omega

/-- **Least witness level `m`**, decidable over a finite alphabet: an aligned
witness at level `m`, and none at any level `n < m`. -/
def LeastWitnessLevel (s : α → List α) (c c' : α) (m : ℕ) : Prop :=
  (∃ i < ((subst s)^[m] [c]).length, IndexWitness s c c' m i i) ∧
    ∀ n < m, ∀ i < ((subst s)^[n] [c]).length, ¬ IndexWitness s c c' n i i

instance [Fintype α] (s : α → List α) (c c' : α) (m : ℕ) :
    Decidable (LeastWitnessLevel s c c' m) := by
  unfold LeastWitnessLevel; infer_instance

/-- `LeastWitnessLevel s c c' m` says what it says: `m` is the least level of a
left strong-coincidence witness for `(c, c')`. -/
theorem leastWitnessLevel_spec {s : α → List α} {c c' : α} {m : ℕ}
    (h : LeastWitnessLevel s c c' m) :
    WitnessAt s c c' m ∧ ∀ n < m, ¬ WitnessAt s c c' n := by
  refine ⟨witnessAt_iff_index.2 (let ⟨i, _, hi⟩ := h.1; ⟨i, i, hi⟩), fun n hn hw => ?_⟩
  obtain ⟨i, j, hij⟩ := witnessAt_iff_index.1 hw
  obtain rfl := hij.aligned
  exact h.2 n hn i hij.1 hij

/-- Over three letters, witnesses for the pairs `01`, `02`, `12` give one for
every pair of distinct letters. -/
theorem fin3_all_pairs {s : Fin 3 → List (Fin 3)} (h01 : StrongCoincidenceWitness s 0 1)
    (h02 : StrongCoincidenceWitness s 0 2) (h12 : StrongCoincidenceWitness s 1 2) :
    ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c' := by
  intro c c' hne
  fin_cases c <;> fin_cases c' <;> simp at hne
  · exact h01
  · exact h02
  · exact strongCoincidenceWitness_comm.1 h01
  · exact h12
  · exact strongCoincidenceWitness_comm.1 h02
  · exact strongCoincidenceWitness_comm.1 h12

/-- The reversal `1/2/10` of the plastic substitution (`0 ↦ 1`, `1 ↦ 2`, `2 ↦ 10`). -/
def plasticRevSubst : Fin 3 → List (Fin 3) := ![[1], [2], [1, 0]]

/-- The reversal `110/2/021` of `censusSubst = 011/2/120`. -/
def censusRevSubst : Fin 3 → List (Fin 3) := ![[1, 1, 0], [2], [0, 2, 1]]

/-- `1/210/002`, the relabelling of `censusRevSubst` by `π = (0 ↦ 2, 1 ↦ 0, 2 ↦ 1)`. -/
def censusRevNF : Fin 3 → List (Fin 3) := ![[1], [2, 1, 0], [0, 0, 2]]

/-- The relabelling `π = (0 ↦ 2, 1 ↦ 0, 2 ↦ 1)`. -/
def censusPi : Fin 3 → Fin 3 := ![2, 0, 1]

/-- Convention check: `censusRevSubst` is the image-wise reversal of `censusSubst`,
`plasticRevSubst` that of `plasticSubst`, and `censusRevNF ∘ π = π ∘ censusRevSubst`
letterwise. -/
theorem reversal_conventions :
    (∀ a, censusRevSubst a = (Psc.Degree3Sector.censusSubst a).reverse) ∧
    (∀ a, plasticRevSubst a = (Psc.Degree2Sector.plasticSubst a).reverse) ∧
    (∀ a, (censusRevSubst a).map censusPi = censusRevNF (censusPi a)) := by
  decide

/-- A least witness level gives a witness. -/
theorem witness_of_least {s : α → List α} {c c' : α} {m : ℕ}
    (h : LeastWitnessLevel s c c' m) : StrongCoincidenceWitness s c c' :=
  strongCoincidenceWitness_iff_exists_witnessAt.2 ⟨m, (leastWitnessLevel_spec h).1⟩

/-- **Least levels** for the plastic substitution `0 ↦ 1, 1 ↦ 2, 2 ↦ 01`: `13, 14, 12`
for the pairs `01, 02, 12` (`C4StandingCorpus` histogram entries `12, 13, 14`). -/
theorem plastic_least :
    LeastWitnessLevel Psc.Degree2Sector.plasticSubst 0 1 13 ∧
      LeastWitnessLevel Psc.Degree2Sector.plasticSubst 0 2 14 ∧
      LeastWitnessLevel Psc.Degree2Sector.plasticSubst 1 2 12 := by
  decide +kernel

/-- **Least levels** for the plastic reversal `1/2/10`: `15, 1, 14`.  Level `15` is the
deepest level of the `C4StandingCorpus` histogram; `{0, 2}` is merged by the first-letter
map (`σ(0)` and `σ(2)` both begin with `1`). -/
theorem plasticRev_least :
    LeastWitnessLevel plasticRevSubst 0 1 15 ∧ LeastWitnessLevel plasticRevSubst 0 2 1 ∧
      LeastWitnessLevel plasticRevSubst 1 2 14 := by
  decide +kernel

/-- **Least levels** for `censusSubst = 011/2/120`: `5, 5, 7`. -/
theorem census_least :
    LeastWitnessLevel Psc.Degree3Sector.censusSubst 0 1 5 ∧
      LeastWitnessLevel Psc.Degree3Sector.censusSubst 0 2 5 ∧
      LeastWitnessLevel Psc.Degree3Sector.censusSubst 1 2 7 := by
  decide +kernel

/-- **Least levels** for the image-wise reversal `110/2/021`: `6, 4, 5`. -/
theorem censusRev_least :
    LeastWitnessLevel censusRevSubst 0 1 6 ∧ LeastWitnessLevel censusRevSubst 0 2 4 ∧
      LeastWitnessLevel censusRevSubst 1 2 5 := by
  decide +kernel

/-- **Least levels** for `1/210/002`: `5, 6, 4` (the levels of `censusRev_least`, carried
by `π`: `{0,1} ↦ {0,2}`, `{0,2} ↦ {1,2}`, `{1,2} ↦ {0,1}`). -/
theorem censusRevNF_least :
    LeastWitnessLevel censusRevNF 0 1 5 ∧ LeastWitnessLevel censusRevNF 0 2 6 ∧
      LeastWitnessLevel censusRevNF 1 2 4 := by
  decide +kernel

/-- **Least levels** for Tribonacci `0 ↦ 01, 1 ↦ 02, 2 ↦ 0` (`Psc.Descendants.tribSubst`):
all `1`, the first-letter map is constant. -/
theorem trib_least :
    LeastWitnessLevel tribSubst 0 1 1 ∧ LeastWitnessLevel tribSubst 0 2 1 ∧
      LeastWitnessLevel tribSubst 1 2 1 := by
  decide

/-- **No strict system over the plastic substitution.** -/
theorem plastic_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem Psc.Degree2Sector.plasticSubst C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs (witness_of_least plastic_least.1)
    (witness_of_least plastic_least.2.1) (witness_of_least plastic_least.2.2)) C

/-- **No strict system over the plastic reversal `1/2/10`** (the deepest corpus
level, `15`). -/
theorem plasticRev_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem plasticRevSubst C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs
    (witness_of_least plasticRev_least.1)
    (witness_of_least plasticRev_least.2.1)
    (witness_of_least plasticRev_least.2.2)) C

/-- **No strict system over `011/2/120`.** -/
theorem census_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem Psc.Degree3Sector.censusSubst C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs (witness_of_least census_least.1)
    (witness_of_least census_least.2.1) (witness_of_least census_least.2.2)) C

/-- **No strict system over the reversal `110/2/021`.** -/
theorem censusRev_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem censusRevSubst C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs
    (witness_of_least censusRev_least.1)
    (witness_of_least censusRev_least.2.1)
    (witness_of_least censusRev_least.2.2)) C

/-- **No strict system over `1/210/002`.** -/
theorem censusRevNF_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem censusRevNF C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs
    (witness_of_least censusRevNF_least.1)
    (witness_of_least censusRevNF_least.2.1)
    (witness_of_least censusRevNF_least.2.2)) C

/-- **No strict system over Tribonacci.** -/
theorem trib_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem tribSubst C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs (witness_of_least trib_least.1)
    (witness_of_least trib_least.2.1) (witness_of_least trib_least.2.2)) C

/-- Fibonacci `0 ↦ 01, 1 ↦ 0` (`Psc.Descendants.fibSubst`): the least witness `σ(0) = 0·1`,
`σ(1) = 0` at level `1`, so no strict system. -/
theorem fib_no_strictSystem (C : Finset (List (Fin 2) × List (Fin 2))) :
    ¬ StrictSystem fibSubst C := by
  have h01 : StrongCoincidenceWitness fibSubst 0 1 :=
    witness_of_least (m := 1) (by decide)
  refine no_strictSystem_of_strongCoincidence (fun c c' hne => ?_) C
  fin_cases c <;> fin_cases c' <;> simp at hne
  · exact h01
  · exact strongCoincidenceWitness_comm.1 h01

/-! ### Controls -/

/-- **Non-vacuity**: Thue–Morse `0 ↦ 01, 1 ↦ 10` has the strict system
`{(01, 10), (10, 01)}` (Thue–Morse is not Pisot irreducible). -/
theorem tm_strictSystem : StrictSystem thueMorseSubst {tmPair, tmPair.swap} where
  nonempty := ⟨tmPair, by decide⟩
  isBlock := by decide
  noncoincident := by decide
  closed := by decide

theorem tm_child_all : ∀ T ∈ ({tmPair, tmPair.swap} : Finset (List (Fin 2) × List (Fin 2))),
    ∀ U ∈ ({tmPair, tmPair.swap} : Finset (List (Fin 2) × List (Fin 2))),
      U ∈ red (subst thueMorseSubst T.1) (subst thueMorseSubst T.2) := by
  decide

/-- The Thue–Morse strict system is a strict component. -/
theorem tm_strictComponent : StrictComponent thueMorseSubst {tmPair, tmPair.swap} :=
  ⟨tm_strictSystem, fun T hT U hU => Or.inl (.single (tm_child_all T hT U hU))⟩

/-- Theorem A(4) on the control: the cut pair `(0, 1)` of Thue–Morse has no left
strong-coincidence witness. -/
theorem tm_no_witness : ¬ StrongCoincidenceWitness thueMorseSubst 0 1 :=
  tm_strictSystem.not_witness ⟨tmPair, by decide, rfl, rfl⟩

/-- (d) on the control: the seed `(01, 10)` of Thue–Morse does not terminate with
coincidence. -/
theorem tm_not_terminates : ¬ TerminatesWithCoincidence thueMorseSubst tmPair :=
  tm_strictSystem.not_terminates (by decide) .refl

/-- The Thue–Morse strict component, read in `B_σ`. -/
theorem tm_bpaStrictComponent : BpaStrictComponent thueMorseSubst {tmPair, tmPair.swap} :=
  tm_strictComponent.toBpa (by decide) ⟨tmPair, by decide, ⟨tmPair, by rw [tm_seeds]; decide, .refl⟩⟩

/-- `N_C` of the lexicographic normalisation of the Thue–Morse component is strongly
connected. -/
theorem tm_stronglyConnected :
    Psc.PerronCore.StronglyConnected
      ((tm_strictSystem.lexNorm (by decide)).Nrep.map (Nat.cast : ℕ → ℝ)) :=
  tm_strictComponent.lexNorm_stronglyConnected (by decide)

/-- (e) on the control: `σ²(01) = 01101001` and `σ²(10) = 10010110` disagree at all
`8` positions (the bound `|σⁿ T.1| ≤ L · mismatch` with `L = 2` is not sharp here). -/
example : mismatch ((subst thueMorseSubst)^[2] tmPair.1) ((subst thueMorseSubst)^[2] tmPair.2) = 8 ∧
    ((subst thueMorseSubst)^[2] tmPair.1).length = 8 := by
  decide

/-- (f) on the control: the Thue–Morse strict system has first defect degree `2`. -/
theorem tm_defectDegree : defectDegree ({tmPair, tmPair.swap} :
    Finset (List (Fin 2) × List (Fin 2))) = 2 :=
  defectDegree_eq_two_iff.2 ⟨tm_strictSystem.equiv1, tmPair, by decide, 0, 1, by decide⟩

/-- Swap closure control: `D = {(01, 10)}` is a strict system for `0 ↦ 010, 1 ↦ 101`
that is not swap-closed; its lexicographic normalisation has `R = {(01, 10)}`. -/
theorem alt_strictSystem : StrictSystem altSubst {tmPair} where
  nonempty := ⟨tmPair, by decide⟩
  isBlock := by decide
  noncoincident := by decide
  closed := by decide

example : (alt_strictSystem.lexNorm (by decide)).R = {tmPair} := by decide

/-- The control for A(5): the Fibonacci seed `(01, 10)` has the coincidence
`(0, 0)` among its factors, so the hypothesis of `strictSystem_of_factorSet` fails. -/
example : (([0], [0]) : List (Fin 2) × List (Fin 2)) ∈ factorSet fibSubst tmPair :=
  ⟨1, by decide⟩

/-- The least levels of `plastic_least` are sharp: neither one level less nor one more. -/
example : ¬ LeastWitnessLevel Psc.Degree2Sector.plasticSubst 0 1 12 ∧
    ¬ LeastWitnessLevel Psc.Degree2Sector.plasticSubst 0 1 14 ∧
    ¬ LeastWitnessLevel plasticRevSubst 0 1 14 ∧ ¬ LeastWitnessLevel plasticRevSubst 0 1 16 := by
  decide +kernel

/-! #### Three-letter controls (cut-pair note §5) -/

/-- `012/120/201`: constant length `3`, incidence the all-ones matrix (`χ_M = X²(X − 3)`),
not Pisot. -/
def cycSubst : Fin 3 → List (Fin 3) := ![[0, 1, 2], [1, 2, 0], [2, 0, 1]]

/-- The ordered 3-cycle `(012, 120), (120, 201), (201, 012)` of the cut-pair note §5. -/
def cycC : Finset (List (Fin 3) × List (Fin 3)) :=
  {([0, 1, 2], [1, 2, 0]), ([1, 2, 0], [2, 0, 1]), ([2, 0, 1], [0, 1, 2])}

theorem cyc_strictSystem : StrictSystem cycSubst cycC where
  nonempty := ⟨([0, 1, 2], [1, 2, 0]), by decide⟩
  isBlock := by decide
  noncoincident := by decide
  closed := by decide

/-- Every state of `cycC` is a child of every state. -/
theorem cyc_child_all : ∀ T ∈ cycC, ∀ U ∈ cycC,
    U ∈ red (subst cycSubst T.1) (subst cycSubst T.2) := by
  decide

/-- `cycC` is a strict component over three letters. -/
theorem cyc_strictComponent : StrictComponent cycSubst cycC :=
  ⟨cyc_strictSystem, fun T hT U hU => Or.inl (.single (cyc_child_all T hT U hU))⟩

/-- **Theorem A(4) on `012/120/201`.**  Its cut pairs are `(0,1), (1,2), (2,0)`, so no pair
of distinct letters has a left strong-coincidence witness at **any** level (the note's
table records "none (level ≤ 6)", a budget). -/
theorem cyc_no_witness : ∀ c c' : Fin 3, c ≠ c' → ¬ StrongCoincidenceWitness cycSubst c c' := by
  have h01 : CutPair cycC 0 1 := ⟨([0, 1, 2], [1, 2, 0]), by decide, rfl, rfl⟩
  have h12 : CutPair cycC 1 2 := ⟨([1, 2, 0], [2, 0, 1]), by decide, rfl, rfl⟩
  have h20 : CutPair cycC 2 0 := ⟨([2, 0, 1], [0, 1, 2]), by decide, rfl, rfl⟩
  intro c c' hne
  fin_cases c <;> fin_cases c' <;> simp at hne
  · exact cyc_strictSystem.not_witness h01
  · exact cyc_strictSystem.not_witness_of_cutPair_swap h20
  · exact cyc_strictSystem.not_witness_of_cutPair_swap h01
  · exact cyc_strictSystem.not_witness h12
  · exact cyc_strictSystem.not_witness h20
  · exact cyc_strictSystem.not_witness_of_cutPair_swap h12

/-- (f) on a three-letter strict component: first defect degree `2`, `kw ≠ 0`. -/
theorem cyc_defectDegree : defectDegree cycC = 2 :=
  defectDegree_eq_two_iff_kw.2 ⟨cyc_strictSystem.equiv1, ([0, 1, 2], [1, 2, 0]), by decide,
    by decide⟩

/-- (a) on a three-letter strict component: `N_C` of the lexicographic normalisation of
the swap closure is strongly connected. -/
theorem cyc_stronglyConnected :
    Psc.PerronCore.StronglyConnected
      ((cyc_strictSystem.lexNorm (by decide)).Nrep.map (Nat.cast : ℕ → ℝ)) :=
  cyc_strictComponent.lexNorm_stronglyConnected (by decide)

/-- `10/102/211` (the strict carrier of #459: primitive, nonsingular, reducible `χ_M`). -/
def carrierSubst : Fin 3 → List (Fin 3) := ![[1, 0], [1, 0, 2], [2, 1, 1]]

/-- The seed `(02, 20)`. -/
def carrierSeed : List (Fin 3) × List (Fin 3) := ([0, 2], [2, 0])

/-- The four states of the sink: `(10210211, 21110210)`, `(102, 210)`, `(11102, 21110)` and
`(10210210210211, 21110210210210)`. -/
def carrierSink : Finset (List (Fin 3) × List (Fin 3)) :=
  {([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]), ([1, 0, 2], [2, 1, 0]),
    ([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]),
    ([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0])}

/-- The six-state transient system: the seed, `(10211, 21110)`, and the sink. -/
def carrierC : Finset (List (Fin 3) × List (Fin 3)) :=
  insert carrierSeed (insert ([1, 0, 2, 1, 1], [2, 1, 1, 1, 0]) carrierSink)

theorem carrier_strictSystem : StrictSystem carrierSubst carrierC where
  nonempty := ⟨carrierSeed, by decide⟩
  isBlock := by decide +kernel
  noncoincident := by decide
  closed := by decide +kernel

/-- **Theorem A(5) non-vacuity**: the factor set of `(02, 20)` over all inflations is
exactly `carrierC` (levels `0` to `4` reach every state). -/
theorem carrier_factorSet : factorSet carrierSubst carrierSeed = ↑carrierC := by
  have hreach : ∀ U ∈ carrierC, ∃ n < 5,
      U ∈ red ((subst carrierSubst)^[n] carrierSeed.1) ((subst carrierSubst)^[n] carrierSeed.2) := by
    decide +kernel
  ext U
  refine ⟨fun hU => carrier_strictSystem.factorSet_subset (by decide) hU, fun hU => ?_⟩
  obtain ⟨n, -, hn⟩ := hreach U hU
  exact ⟨n, hn⟩

/-- The hypotheses of `strictSystem_of_factorSet` hold at `(02, 20)`. -/
theorem carrier_A5 : ∃ hfin : (factorSet carrierSubst carrierSeed).Finite,
    StrictSystem carrierSubst hfin.toFinset := by
  have hfin : (factorSet carrierSubst carrierSeed).Finite := by
    rw [carrier_factorSet]; exact carrierC.finite_toSet
  refine ⟨hfin, strictSystem_of_factorSet (by decide) (by decide) hfin fun U hU => ?_⟩
  rw [carrier_factorSet] at hU
  exact carrier_strictSystem.noncoincident U hU

/-- **Theorem A(4) on `10/102/211`.**  The cut pairs of `carrierC` are `(0, 2)` (the seed)
and `(1, 2)`, so neither `{0, 2}` nor `{1, 2}` has a left strong-coincidence witness at any
level (the note records `{0, 2}` as "no witness within level 8", a budget), while `{0, 1}`
has one at level `1`: `σ(0) = 1·0`, `σ(1) = 1·02`. -/
theorem carrier_witnesses : ¬ StrongCoincidenceWitness carrierSubst 0 2 ∧
    ¬ StrongCoincidenceWitness carrierSubst 1 2 ∧ LeastWitnessLevel carrierSubst 0 1 1 :=
  ⟨carrier_strictSystem.not_witness ⟨carrierSeed, by decide, rfl, rfl⟩,
    carrier_strictSystem.not_witness ⟨([1, 0, 2], [2, 1, 0]), by decide, rfl, rfl⟩, by decide⟩

theorem carrierSink_strictSystem : StrictSystem carrierSubst carrierSink where
  nonempty := ⟨([1, 0, 2], [2, 1, 0]), by decide⟩
  isBlock := by decide +kernel
  noncoincident := by decide
  closed := by decide +kernel

/-- The cycle `(10210211, ·) → (11102, ·) → (10210210210211, ·) → (102, ·) → (10210211, ·)`
through the sink. -/
def carrierNext (T : List (Fin 3) × List (Fin 3)) : List (Fin 3) × List (Fin 3) :=
  if T = ([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0]) then ([1, 1, 1, 0, 2], [2, 1, 1, 1, 0])
  else if T = ([1, 1, 1, 0, 2], [2, 1, 1, 1, 0]) then
    ([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0])
  else if T = ([1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 1],
      [2, 1, 1, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 0]) then ([1, 0, 2], [2, 1, 0])
  else ([1, 0, 2, 1, 0, 2, 1, 1], [2, 1, 1, 1, 0, 2, 1, 0])

/-- The four-state sink of `10/102/211` is a strict component (primitive `σ`); its only cut
pair is `(1, 2)`. -/
theorem carrierSink_strictComponent : StrictComponent carrierSubst carrierSink :=
  StrictComponent.of_cycle carrierSink_strictSystem carrierNext (by decide +kernel)
    (by decide +kernel)

theorem carrierSink_cutPair {c c' : Fin 3} (h : CutPair carrierSink c c') : c = 1 ∧ c' = 2 := by
  obtain ⟨T, hT, h1, h2⟩ := h
  have hT' : ∀ T ∈ carrierSink, T.1.head? = some 1 ∧ T.2.head? = some 2 := by decide
  obtain ⟨e1, e2⟩ := hT' T hT
  exact ⟨Option.some_injective _ (h1.symm.trans e1), Option.some_injective _ (h2.symm.trans e2)⟩

theorem carrierSink_stronglyConnected :
    Psc.PerronCore.StronglyConnected
      ((carrierSink_strictSystem.lexNorm (by decide)).Nrep.map (Nat.cast : ℕ → ℝ)) :=
  carrierSink_strictComponent.lexNorm_stronglyConnected (by decide)

/-- `01/121/012` (PIP, `det M = 2`; cut-pair note §5): least levels `2, 1, 2`, so no strict
system. -/
def m121Subst : Fin 3 → List (Fin 3) := ![[0, 1], [1, 2, 1], [0, 1, 2]]

theorem m121_least : LeastWitnessLevel m121Subst 0 1 2 ∧ LeastWitnessLevel m121Subst 0 2 1 ∧
    LeastWitnessLevel m121Subst 1 2 2 := by
  decide +kernel

theorem m121_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem m121Subst C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs (witness_of_least m121_least.1)
    (witness_of_least m121_least.2.1) (witness_of_least m121_least.2.2)) C

/-- `01/12/021` (unit PIP, `det M = 1`; cut-pair note §5): least levels `4, 1, 4`, at the
indices `16, 0, 10` the note records, so no strict system. -/
def u021Subst : Fin 3 → List (Fin 3) := ![[0, 1], [1, 2], [0, 2, 1]]

theorem u021_least : LeastWitnessLevel u021Subst 0 1 4 ∧ LeastWitnessLevel u021Subst 0 2 1 ∧
    LeastWitnessLevel u021Subst 1 2 4 ∧ IndexWitness u021Subst 0 1 4 16 16 ∧
    IndexWitness u021Subst 0 2 1 0 0 ∧ IndexWitness u021Subst 1 2 4 10 10 := by
  decide +kernel

theorem u021_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem u021Subst C :=
  no_strictSystem_of_strongCoincidence (fin3_all_pairs (witness_of_least u021_least.1)
    (witness_of_least u021_least.2.1) (witness_of_least u021_least.2.2.1)) C

/-! ## Part 2, (g): the reductio lemmas on a strict component

The sector theorems restated on a strict system or strict component over `Fin 3`, with
only substitution-level hypotheses (`M` primitive, `χ_M` irreducible, a Pisot root where
needed) and the first defect degree; every structural hypothesis is discharged from
part 1.  Their conclusions hold for **every** normalisation `P` of the swap-closed
child system `swapSystem` (the lexicographic one, `lexNorm`, among them). -/

universe u

/-- An irreducible `χ_M` makes `σ` nonerasing: an empty image `σ(a)` is a zero column
of `M`, so `det M = 0` (`Psc.Cyclicity.det_ne_zero_of_irreducible`). -/
theorem nonerasing_of_irreducible {s : Fin 3 → List (Fin 3)}
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) : ∀ a, s a ≠ [] := by
  intro a ha
  refine Psc.Cyclicity.det_ne_zero_of_irreducible _ hM
    (Matrix.det_eq_zero_of_column_eq_zero a fun b => ?_)
  simp [inc, ha]

namespace StrictSystem

variable {s : α → List α} {C : Finset (List α × List α)} (h : StrictSystem s C)
  (hs : ∀ a, s a ≠ [])

/-- The **swap-closed child system** of a strict system: the zero-return child system
(`toChildSystem`) of its swap closure.  A normalisation of it is a choice of
representatives (`sec:orientation`); `lexNorm` is one. -/
abbrev swapSystem : ChildSystem α := h.swapClosure.toChildSystem hs

theorem swapSystem_equiv1 : ∀ T ∈ (h.swapSystem hs).C, Equiv1 T.1 T.2 := h.swapClosure.equiv1

theorem swapSystem_nonempty : (h.swapSystem hs).C.Nonempty := h.swapClosure.nonempty

theorem mem_swapSystem {T : List α × List α} (hT : T ∈ C) : T ∈ (h.swapSystem hs).C :=
  Finset.mem_union_left _ hT

/-- First defect degree `3`: every state of the swap closure is `∼₂`. -/
theorem swapSystem_equiv2 (hdeg : defectDegree C = 3) :
    ∀ T ∈ (h.swapSystem hs).C, Equiv2 T.1 T.2 :=
  forall_swapClosureF (p := fun T => Equiv2 T.1 T.2) (fun _ hU => equiv2_comm hU)
    (defectDegree_eq_three_iff.1 hdeg).1

/-- First defect degree `4`: every state of the swap closure is `∼₃`. -/
theorem swapSystem_equiv3 (hdeg : defectDegree C = 4) :
    ∀ T ∈ (h.swapSystem hs).C, Psc.Defect4.Equiv3 T.1 T.2 :=
  forall_swapClosureF (p := fun T => Psc.Defect4.Equiv3 T.1 T.2) (fun _ hU => equiv3_comm hU)
    (defectDegree_eq_four_iff.1 hdeg).1

/-- `|swap closure of C| = 2 |R|` for every normalisation
(`Psc.ParikhRank.card_state_eq_two_mul`). -/
theorem card_swapClosureF (P : Normalisation (h.swapSystem hs)) :
    (swapClosureF C).card = 2 * Fintype.card P.Rep := by
  have := Psc.ParikhRank.card_state_eq_two_mul P
  rw [Fintype.card_coe] at this
  rw [Fintype.card_coe]
  exact this

/-- `|R| ≤ |C|` for every normalisation: each state of the swap closure is a state of
`C` or the swap of one. -/
theorem card_rep_le (P : Normalisation (h.swapSystem hs)) : Fintype.card P.Rep ≤ C.card := by
  have h1 := h.card_swapClosureF hs P
  have h2 : (swapClosureF C).card ≤ C.card + C.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  omega

end StrictSystem

namespace StrictSystem

variable {s : Fin 3 → List (Fin 3)} {C : Finset (List (Fin 3) × List (Fin 3))}
  (h : StrictSystem s C) (hs : ∀ a, s a ≠ [])

/-- First defect degree `2`: every normalisation has a representative with `kw ≠ 0`. -/
theorem exists_rep_kw_of_two (hdeg : defectDegree C = 2) (P : Normalisation (h.swapSystem hs)) :
    ∃ j : P.Rep, Psc.Intertwiner2.kw j.1.1 j.1.2 ≠ 0 :=
  let ⟨_, _, hT, hK⟩ := defectDegree_eq_two_iff_kw.1 hdeg
  exists_rep_kw P (h.mem_swapSystem hs hT) hK

/-- First defect degree `3`: every normalisation has a representative with `K₃ ≠ 0`. -/
theorem exists_rep_k3_of_three (hdeg : defectDegree C = 3) (P : Normalisation (h.swapSystem hs)) :
    ∃ j : P.Rep, Psc.Lie3.k3Vec j.1.1 j.1.2 ≠ 0 :=
  let ⟨_, _, hT, hK⟩ := defectDegree_eq_three_iff_k3Vec.1 hdeg
  exists_rep_k3Vec P (h.mem_swapSystem hs hT) hK

/-- First defect degree `4`: every normalisation has a representative with `K₄ ≠ 0`. -/
theorem exists_rep_k4_of_four (hdeg : defectDegree C = 4) (P : Normalisation (h.swapSystem hs)) :
    ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0 :=
  let ⟨_, _, hT, hK⟩ := defectDegree_eq_four_iff_k4Vec.1 hdeg
  exists_rep_k4Vec P (h.mem_swapSystem hs hT) hK

end StrictSystem

/-! #### `Psc.Degree2Sector` on a strict system -/

/-- **`thm:deg23` (ii) on a strict system of first defect degree `2`** over three letters
with irreducible `χ_M` (`Psc.Degree2Sector`), for **every** normalisation `P` of the
swap-closed child system: `rank Q₂ = 3`; `χ_{Λ²M} ∣ χ_S` over `ℚ` and over `ℤ`;
`lcm(χ_M, χ_{Λ²M}) ∣ χ_{N_C}` mod `2`; `|R| ≥ deg lcm`; and `|R| ≥ 6` when `det M` is odd
and `tr M ≢ tr Λ²M (mod 2)`.  Nonerasure, balance and the nonzero `kw` column are
discharged (`nonerasing_of_irreducible`, `swapSystem_equiv1`, `exists_rep_kw_of_two`);
strong connectivity is not used.  A reductio lemma. -/
theorem StrictSystem.deg2_sector {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictSystem s C) (hdeg : defectDegree C = 2)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    (Psc.Degree2Sector.Q2Q P).rank = 3 ∧
      (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ℚ))).charpoly ∣
        (Psc.Degree2Sector.SsignQ P).charpoly ∧
      (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ℤ))).charpoly ∣ P.Ssign.charpoly ∧
      lcm ((inc s).map (Nat.cast : ℕ → ZMod 2)).charpoly
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ZMod 2))).charpoly ∣
        (Psc.Degree2Sector.nrepF2 P).charpoly ∧
      (lcm ((inc s).map (Nat.cast : ℕ → ZMod 2)).charpoly
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ZMod 2))).charpoly).natDegree ≤
        Fintype.card P.Rep ∧
      (Odd ((inc s).map (Nat.cast : ℕ → ℤ)).det →
        ¬ ((inc s).map (Nat.cast : ℕ → ℤ)).trace ≡
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ℤ))).trace [ZMOD 2] →
        6 ≤ Fintype.card P.Rep) := by
  have hbal := h.swapSystem_equiv1 (nonerasing_of_irreducible hM)
  have hK := h.exists_rep_kw_of_two _ hdeg P
  exact ⟨Psc.Degree2Sector.rank_q2 P hM hbal hK,
    Psc.Degree2Sector.charpoly_wedge2_dvd_ssign P hM hbal hK,
    Psc.Degree2Sector.charpoly_wedge2_dvd_ssign_int P hM hbal hK,
    Psc.Degree2Sector.lcm_dvd_nrep_mod_two P hM hbal hK,
    Psc.Degree2Sector.card_rep_ge_natDegree_lcm P hM hbal hK,
    fun hdet htr => Psc.Degree2Sector.card_rep_ge_six P hM hbal hK hdet htr⟩

/-! #### `Psc.KernelCofactor` on a strict component -/

open Matrix in
/-- **`thm:parikh` and Theorem A(iv) on a strict component** over three letters with
primitive `M` and irreducible `χ_M` (`Psc.KernelCofactor`, representative section), for
every normalisation `P` of the swap-closed child system: with `β` the Perron root of `M`
(`PerronData`, `Psc.PerronExistence.perron_inc`), `χ_{N_C} = χ_M · g` for the cofactor
`g = χ(N_C | ker P_R)`, `g` is the image of an integer polynomial, `gcd(χ_M, g) = 1`, `β` is
a simple root of `χ_{N_C}` and its spectral radius, and every `Q` intertwining `N_C` with an
`R` annihilated by `χ_M` factors through `P_R` (injectively unless `Q = 0`).  Strong
connectivity of `N_C` is `StrictComponent.nrep_stronglyConnected`; balance, `C ≠ ∅` and the
Perron vector are discharged.  A reductio lemma. -/
theorem StrictComponent.kernel_cofactor {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictComponent s C)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    ∃ (β : ℝ) (ℓ u : Fin 3 → ℝ),
      Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) β ℓ u ∧
      (Psc.ParikhRank.NrepQ P).charpoly = ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly *
        (Psc.KernelCofactor.kerRestrict (Psc.ParikhRank.prepQ_nrepQ P
          (h.swapSystem_equiv1 (nonerasing_of_irreducible hM)))).charpoly ∧
      (∃ g : Polynomial ℤ, (Psc.KernelCofactor.kerRestrict (Psc.ParikhRank.prepQ_nrepQ P
          (h.swapSystem_equiv1 (nonerasing_of_irreducible hM)))).charpoly =
        g.map (Int.castRingHom ℚ)) ∧
      IsCoprime ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly
        (Psc.KernelCofactor.kerRestrict (Psc.ParikhRank.prepQ_nrepQ P
          (h.swapSystem_equiv1 (nonerasing_of_irreducible hM)))).charpoly ∧
      Polynomial.rootMultiplicity β
          ((Psc.ParikhRank.NrepQ P).charpoly.map (algebraMap ℚ ℝ)) = 1 ∧
      (∃ v : P.Rep → ℝ, v ≠ 0 ∧ P.Nrep.map (Nat.cast : ℕ → ℝ) *ᵥ v = β • v) ∧
      (∀ x : P.Rep → ℂ, x ≠ 0 → ∀ μ : ℂ,
        P.Nrep.map (Nat.cast : ℕ → ℂ) *ᵥ x = μ • x → ‖μ‖ ≤ β) ∧
      ∀ (Y : Type u) [AddCommGroup Y] [Module ℚ Y] (Q : (P.Rep → ℚ) →ₗ[ℚ] Y) (R : Y →ₗ[ℚ] Y),
        Q ∘ₗ Matrix.toLin' (Psc.ParikhRank.NrepQ P) = R ∘ₗ Q →
        Polynomial.aeval R ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
        ∃ L' : (Fin 3 → ℚ) →ₗ[ℚ] Y, Q = L' ∘ₗ Matrix.mulVecLin (Psc.ParikhRank.PrepQ P) ∧
          L' ∘ₗ Matrix.toLin' ((inc s).map (Nat.cast : ℕ → ℚ)) = R ∘ₗ L' ∧
          (Q ≠ 0 → Function.Injective L') := by
  have hs := nonerasing_of_irreducible hM
  have hbal := h.swapSystem_equiv1 hs
  have hC := h.swapSystem_nonempty hs
  have hSC := h.swapClosure.nrep_stronglyConnected hs P
  obtain ⟨β, ℓ, u, hP, -, -⟩ := Psc.PerronExistence.perron_inc s hprim
  obtain ⟨hmul, hv, hle⟩ :=
    Psc.KernelCofactor.simple_perron_root_rep P hM hbal hSC ℓ hP.left_pos β hP.left hC
  exact ⟨β, ℓ, u, hP, Psc.KernelCofactor.charpoly_nrep_eq_mul P hM hbal hC,
    Psc.KernelCofactor.cofactor_int P hM hbal hC,
    Psc.KernelCofactor.isCoprime_rep P hM hbal hSC ℓ hP.left_pos β hP.left, hmul, hv, hle,
    fun Y _ _ Q R hQ hR => Psc.KernelCofactor.factor_through_rep P hM hbal hSC ℓ hP.left_pos β
      hP.left hC Q R hQ hR⟩

/-! #### `Psc.Degree3Sector` on a strict system -/

/-- `M^{⊗3}` is odd: `Φ₃(-f) = -Φ₃(f)`. -/
theorem phi3_neg {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) (f : Psc.Lie3.Vec3 R) :
    Psc.Lie3.phi3 M (-f) = -Psc.Lie3.phi3 M f := by
  funext a b c
  simp [Psc.Lie3.phi3, Finset.sum_neg_distrib]

/-- **`thm:deg23` (iii) on a strict system of first defect degree `3`** over three letters
with primitive `M`, irreducible `χ_M` and a root `β` of `χ_M` whose other complex roots have
modulus `< 1` (`Psc.Degree3Sector.deg23_iii_of_primitive`, `deg23_iii_of_ne`), for every
normalisation `P` of the swap-closed child system: `β` is the Perron root `r` of `M`; every
root of `q₃ = χ(Φ₃|_{im Q₃})` is `det M`; `q₃ = (X - det M)^{rank Q₃}`;
`im Q₃ ⊆ ker (Φ₃ - det M)`; `1 ≤ rank Q₃ ≤ 2`; `det M` is a root of `χ_S`; and
`M^{⊗3} K₃(T) = det M · K₃(T)` for **every state** `T ∈ C`.  The other two roots and their
distinctness come from `Psc.Degree4Floor.exists_other_roots`, the bound `ρ(S) ≤ β` from
`Psc.Degree3Sector.roots_ssign_le`; strong connectivity is not used.  A reductio lemma. -/
theorem StrictSystem.deg23_iii {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictSystem s C) (hdeg : defectDegree C = 3)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    (∃ (r : ℝ) (ℓ u : Fin 3 → ℝ),
        Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧ (r : ℂ) = β) ∧
      (∀ z : ℂ, Polynomial.aeval z (Psc.SectorBridge.q3 P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg)) = 0 →
        z = (((inc s).map (Nat.cast : ℕ → ℚ)).det : ℂ)) ∧
      Psc.SectorBridge.q3 P (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg) =
        (Polynomial.X - Polynomial.C ((inc s).map (Nat.cast : ℕ → ℚ)).det) ^
          Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P
            (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg))) ∧
      LinearMap.range (Psc.SectorBridge.Q3m P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg)) ≤
        LinearMap.ker (Psc.LieWeights.phi3Lie ((inc s).map (Nat.cast : ℕ → ℚ)) -
          ((inc s).map (Nat.cast : ℕ → ℚ)).det • 1) ∧
      1 ≤ Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg))) ∧
      Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg))) ≤ 2 ∧
      (Psc.Degree2Sector.SsignQ P).charpoly.IsRoot ((inc s).map (Nat.cast : ℕ → ℚ)).det ∧
      ∀ T ∈ C, Psc.Lie3.phi3 ((inc s).map (Nat.cast : ℕ → ℚ)) (Psc.Lie3.k3Vec T.1 T.2) =
        ((inc s).map (Nat.cast : ℕ → ℚ)).det • Psc.Lie3.k3Vec T.1 T.2 := by
  have hs := nonerasing_of_irreducible hM
  have hbal := h.swapSystem_equiv2 hs hdeg
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ := Psc.Degree4Floor.exists_other_roots _ hM hβ
  have hα1 := hpisot α hα (Ne.symm hβα)
  have hγ1 := hpisot γ hγ (Ne.symm hβγ)
  obtain ⟨⟨r, ℓ, u, hP, hr⟩, hroot, hpow, hker, hle⟩ :=
    Psc.Degree3Sector.deg23_iii_of_primitive P hbal hprim hM hβ hα hγ hβα hβγ hαγ hα1 hγ1
  have hbound : ∀ μ : ℂ, Polynomial.aeval μ (Psc.Degree2Sector.SsignQ P).charpoly = 0 →
      ‖μ‖ ≤ ‖β‖ := by
    intro μ hμ
    rw [← hr, Complex.norm_real, Real.norm_eq_abs]
    exact (Psc.Degree3Sector.roots_ssign_le P ℓ hP.left_pos r hP.left (h.swapSystem_equiv1 hs)
      μ hμ).trans (le_abs_self r)
  obtain ⟨hpos, -, hS⟩ := Psc.Degree3Sector.deg23_iii_of_ne P hbal hM hβ hα hγ hβα hβγ hαγ hα1
    hγ1 hbound (h.exists_rep_k3_of_three hs hdeg P)
  refine ⟨⟨r, ℓ, u, hP, hr⟩, hroot, hpow, hker, hpos, hle, hS, fun T hT => ?_⟩
  have hT' := h.mem_swapSystem hs hT
  have hj := Psc.Degree3Sector.phi3_k3Vec_eq_det P hbal hM hβ hα hγ hβα hβγ hαγ hα1 hγ1 hbound
    (repOf P hT')
  rcases repOf_spec P hT' with e | e <;> rw [e] at hj
  · exact hj
  · rw [Prod.fst_swap, Prod.snd_swap, k3Vec_swap, phi3_neg, smul_neg] at hj
    exact neg_injective hj

/-! #### `Psc.Degree4Floor` on a strict system and on a strict component -/

/-- **`thm:sieve` at `r = 4` on a strict system of first defect degree `4`** over three
letters with primitive `M`, irreducible `χ_M` and a Pisot root `β`
(`Psc.Degree4Floor.sieve4_of_primitive`), for every normalisation `P` of the swap-closed
child system: `β` is the Perron root `r > 1` of `M`; `|det M| = 1`; every root of `χ_S` has
modulus `≤ ‖β‖`; and `q₄` and `χ_S` share a root of modulus `‖β‖`, so `ρ(S) = β`.  Strong
connectivity is not used.  A reductio lemma. -/
theorem StrictSystem.sieve4 {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictSystem s C) (hdeg : defectDegree C = 4)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    (∃ (r : ℝ) (ℓ u : Fin 3 → ℝ),
        Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧ 1 < r ∧
          (r : ℂ) = β) ∧
      |((inc s).map (Nat.cast : ℕ → ℤ)).det| = 1 ∧
      (∀ μ : ℂ, Polynomial.aeval μ (Psc.Degree2Sector.SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖) ∧
      ∃ μ : ℂ, Polynomial.aeval μ (Psc.SectorBridge.q4 P
          (h.swapSystem_equiv3 (nonerasing_of_irreducible hM) hdeg)) = 0 ∧
        Polynomial.aeval μ (Psc.Degree2Sector.SsignQ P).charpoly = 0 ∧ ‖μ‖ = ‖β‖ :=
  Psc.Degree4Floor.sieve4_of_primitive P (h.swapSystem_equiv3 _ hdeg) hM
    (h.exists_rep_k4_of_four _ hdeg P) hprim hβ hβ1 hpisot

/-- **Theorem A(i), (iii) and the eigenvalue form of (ii) on a strict component of first
defect degree `4`** over three letters with primitive `M`, irreducible `χ_M` and a Pisot
root `β` (`Psc.Degree4Floor.theoremA_of_primitive`, with `hSC` from
`StrictComponent.nrep_stronglyConnected`), for every normalisation `P` of the swap-closed
child system: `β` is the Perron root `r > 1` of `M`; `|det M| = 1`; `d r` (`d = det M`) is a
root of `q₄` and of `χ_S`; every root of `q₄` is `d x` for a root `x` of `χ_M` (Theorem
A(ii) in eigenvalue form only: the subspace form `im Q₄ ⊆ ker χ_{dM}(Φ₄)` is not proved);
`S = d · D N_C D` for an integer sign vector `D`; and so
(`Psc.CocycleSpectrum.isGauge_iff`, `isAntiGauge_iff`) `d = 1` with a gauge or `d = -1`
with an anti-gauge.  Theorem A(iv) is `StrictComponent.kernel_cofactor`, in its abstract
form only.  A reductio lemma. -/
theorem StrictComponent.theoremA {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictComponent s C)
    (hdeg : defectDegree C = 4) (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    ∃ r : ℝ, (∃ ℓ u : Fin 3 → ℝ,
        Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) r ℓ u) ∧
      1 < r ∧ (r : ℂ) = β ∧ |((inc s).map (Nat.cast : ℕ → ℤ)).det| = 1 ∧
      Polynomial.aeval ((((inc s).map (Nat.cast : ℕ → ℤ)).det : ℂ) * r)
        (Psc.SectorBridge.q4 P (h.swapSystem_equiv3 (nonerasing_of_irreducible hM) hdeg)) = 0 ∧
      Polynomial.aeval ((((inc s).map (Nat.cast : ℕ → ℤ)).det : ℂ) * r)
        (Psc.Degree2Sector.SsignQ P).charpoly = 0 ∧
      (∀ z : ℂ, Polynomial.aeval z
          (Psc.SectorBridge.q4 P (h.swapSystem_equiv3 (nonerasing_of_irreducible hM) hdeg)) = 0 →
        ∃ x : ℂ, Polynomial.aeval x ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
          z = ((inc s).map (Nat.cast : ℕ → ℤ)).det * x) ∧
      (∃ D : P.Rep → ℤ, (∀ i, D i = 1 ∨ D i = -1) ∧
        ∀ i j, P.Ssign i j = ((inc s).map (Nat.cast : ℕ → ℤ)).det * D i * P.Nrep i j * D j) ∧
      ((((inc s).map (Nat.cast : ℕ → ℤ)).det = 1 ∧ ∃ g, Psc.CocycleSpectrum.IsGauge P g) ∨
        (((inc s).map (Nat.cast : ℕ → ℤ)).det = -1 ∧
          ∃ g, Psc.CocycleSpectrum.IsAntiGauge P g)) := by
  obtain ⟨r, hP, hr1, hr, hunit, h1, h2, h3, D, hD, hSD⟩ :=
    Psc.Degree4Floor.theoremA_of_primitive P (h.swapSystem_equiv3 _ hdeg) hM
      (h.exists_rep_k4_of_four _ hdeg P) hprim hβ hβ1 hpisot
      (h.swapClosure.nrep_stronglyConnected _ P)
  refine ⟨r, hP, hr1, hr, hunit, h1, h2, h3, ⟨D, hD, hSD⟩, ?_⟩
  rcases (abs_eq zero_le_one).1 hunit with e | e
  · exact Or.inl ⟨e, D, (Psc.CocycleSpectrum.isGauge_iff P D).2
      ⟨hD, fun i j => by rw [hSD, e]; ring⟩⟩
  · exact Or.inr ⟨e, D, (Psc.CocycleSpectrum.isAntiGauge_iff P D).2
      ⟨hD, fun i j => by rw [hSD, e]; ring⟩⟩

/-- **Theorem A(iii) in the vocabulary of `Psc.CocycleSpectrum`**, the last clause of
`StrictComponent.theoremA`: `det M = 1` and the cocycle has a gauge (`IsGauge`), or
`det M = -1` and it has an anti-gauge (`IsAntiGauge`), for every normalisation. -/
theorem StrictComponent.gauge_or_antiGauge {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictComponent s C)
    (hdeg : defectDegree C = 4) (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    (((inc s).map (Nat.cast : ℕ → ℤ)).det = 1 ∧ ∃ g, Psc.CocycleSpectrum.IsGauge P g) ∨
      (((inc s).map (Nat.cast : ℕ → ℤ)).det = -1 ∧ ∃ g, Psc.CocycleSpectrum.IsAntiGauge P g) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hg⟩ := h.theoremA hdeg hprim hM hβ hβ1 hpisot P
  exact hg

/-! #### The restatements on `StrictComponent`

`deg2_sector`, `deg23_iii` and `sieve4` use no strong connectivity, so they are proved on
`StrictSystem` above; these are their instances on a strict component (also reachable as
`h.deg2_sector` through the parent structure). -/

/-- `StrictSystem.deg2_sector` on a strict component. -/
theorem StrictComponent.deg2_sector {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictComponent s C) (hdeg : defectDegree C = 2)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    (Psc.Degree2Sector.Q2Q P).rank = 3 ∧
      (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ℚ))).charpoly ∣
        (Psc.Degree2Sector.SsignQ P).charpoly ∧
      (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ℤ))).charpoly ∣ P.Ssign.charpoly ∧
      lcm ((inc s).map (Nat.cast : ℕ → ZMod 2)).charpoly
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ZMod 2))).charpoly ∣
        (Psc.Degree2Sector.nrepF2 P).charpoly ∧
      (lcm ((inc s).map (Nat.cast : ℕ → ZMod 2)).charpoly
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ZMod 2))).charpoly).natDegree ≤
        Fintype.card P.Rep ∧
      (Odd ((inc s).map (Nat.cast : ℕ → ℤ)).det →
        ¬ ((inc s).map (Nat.cast : ℕ → ℤ)).trace ≡
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ℤ))).trace [ZMOD 2] →
        6 ≤ Fintype.card P.Rep) :=
  h.toStrictSystem.deg2_sector hdeg hM P

/-- `StrictSystem.deg23_iii` on a strict component. -/
theorem StrictComponent.deg23_iii {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictComponent s C) (hdeg : defectDegree C = 3)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    (∃ (r : ℝ) (ℓ u : Fin 3 → ℝ),
        Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧ (r : ℂ) = β) ∧
      (∀ z : ℂ, Polynomial.aeval z (Psc.SectorBridge.q3 P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg)) = 0 →
        z = (((inc s).map (Nat.cast : ℕ → ℚ)).det : ℂ)) ∧
      Psc.SectorBridge.q3 P (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg) =
        (Polynomial.X - Polynomial.C ((inc s).map (Nat.cast : ℕ → ℚ)).det) ^
          Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P
            (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg))) ∧
      LinearMap.range (Psc.SectorBridge.Q3m P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg)) ≤
        LinearMap.ker (Psc.LieWeights.phi3Lie ((inc s).map (Nat.cast : ℕ → ℚ)) -
          ((inc s).map (Nat.cast : ℕ → ℚ)).det • 1) ∧
      1 ≤ Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg))) ∧
      Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P
          (h.swapSystem_equiv2 (nonerasing_of_irreducible hM) hdeg))) ≤ 2 ∧
      (Psc.Degree2Sector.SsignQ P).charpoly.IsRoot ((inc s).map (Nat.cast : ℕ → ℚ)).det ∧
      ∀ T ∈ C, Psc.Lie3.phi3 ((inc s).map (Nat.cast : ℕ → ℚ)) (Psc.Lie3.k3Vec T.1 T.2) =
        ((inc s).map (Nat.cast : ℕ → ℚ)).det • Psc.Lie3.k3Vec T.1 T.2 :=
  h.toStrictSystem.deg23_iii hdeg hprim hM hβ hpisot P

/-- `StrictSystem.sieve4` on a strict component. -/
theorem StrictComponent.sieve4 {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictComponent s C) (hdeg : defectDegree C = 4)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    (∃ (r : ℝ) (ℓ u : Fin 3 → ℝ),
        Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) r ℓ u ∧ 1 < r ∧
          (r : ℂ) = β) ∧
      |((inc s).map (Nat.cast : ℕ → ℤ)).det| = 1 ∧
      (∀ μ : ℂ, Polynomial.aeval μ (Psc.Degree2Sector.SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖) ∧
      ∃ μ : ℂ, Polynomial.aeval μ (Psc.SectorBridge.q4 P
          (h.swapSystem_equiv3 (nonerasing_of_irreducible hM) hdeg)) = 0 ∧
        Polynomial.aeval μ (Psc.Degree2Sector.SsignQ P).charpoly = 0 ∧ ‖μ‖ = ‖β‖ :=
  h.toStrictSystem.sieve4 hdeg hprim hM hβ hβ1 hpisot P

/-! #### Theorem A(iii) on walks: closed walks carry the sign `(det M)ⁿ` -/

/-- An anti-gauge reverses the sign of each step: `g b = s · (-1)ⁿ · g a` along a walk
`a → b` of length `n` and sign `s` (the anti-gauge analogue of
`Psc.CocycleSpectrum.IsGauge.walk`).  This is only the forward direction; the converse,
the anti-gauge walk criterion that `Psc.CocycleSpectrum` lists as not proved (closed walks
of length `n` with sign `(-1)ⁿ` give an anti-gauge), is not proved here either.  The
lemma is generic over any `ChildSystem` and belongs in `Psc.CocycleSpectrum`. -/
theorem isAntiGauge_walk {S : ChildSystem α} {P : Normalisation S}
    {g : P.Rep → ℤ} (hg : Psc.CocycleSpectrum.IsAntiGauge P g) {a b : P.Rep} {n : ℕ} {s : ℤ}
    (h : Psc.CocycleSpectrum.SignedWalk P a n b s) : g b = s * (-1) ^ n * g a := by
  induction h with
  | nil => ring
  | plus _ hA ih => rw [(hg.2 _ _).1 hA, ih]; ring
  | minus _ hB ih => rw [(hg.2 _ _).2 hB, ih]; ring

/-- **Closed walks on a strict component of first defect degree `4`** (hypotheses of
`StrictComponent.theoremA`): for every normalisation, every closed walk of the child
graph on the representatives of length `n` has sign product `(det M)ⁿ` — `+1` in the
gauge case `det M = 1` (`Psc.CocycleSpectrum.IsGauge.closed_walk`), `(-1)ⁿ` in the
anti-gauge case `det M = -1` (`isAntiGauge_walk`). -/
theorem StrictComponent.closed_walk_sign {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictComponent s C)
    (hdeg : defectDegree C = 4) (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) {a : P.Rep} {n : ℕ}
    {t : ℤ} (hw : Psc.CocycleSpectrum.SignedWalk P a n a t) :
    t = ((inc s).map (Nat.cast : ℕ → ℤ)).det ^ n := by
  rcases h.gauge_or_antiGauge hdeg hprim hM hβ hβ1 hpisot P with ⟨e, g, hg⟩ | ⟨e, g, hg⟩
  · rw [e, one_pow]; exact hg.closed_walk hw
  · rw [e]
    have hga := isAntiGauge_walk hg hw
    rcases hg.1 a with h1 | h1 <;> rw [h1] at hga <;>
      rcases neg_one_pow_eq_or ℤ n with h2 | h2 <;> rw [h2] at hga ⊢ <;> linarith

/-! ### (h) Exclusion forms -/

/-- `thm:parikh`'s `|R| ≥ d` on a strict system over an irreducible `χ_M`
(`Psc.ParikhRank.card_rep_ge`, any first defect degree), for every normalisation of the
swap-closed child system. -/
theorem StrictSystem.three_le_card_rep {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictSystem s C)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (P : Normalisation (h.swapSystem (nonerasing_of_irreducible hM))) :
    3 ≤ Fintype.card P.Rep :=
  Psc.ParikhRank.card_rep_ge P hM (h.swapSystem_equiv1 _) (h.swapSystem_nonempty _)

/-- **Every strict system over an irreducible `χ_M` has at least three states**, and at
least three up to side swap (`three_le_card_rep`, any first defect degree). -/
theorem StrictSystem.three_le_card {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictSystem s C)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) :
    6 ≤ (swapClosureF C).card ∧ 3 ≤ C.card := by
  have hs := nonerasing_of_irreducible hM
  have h3 := h.three_le_card_rep hM (h.lexNorm hs)
  exact ⟨by rw [h.card_swapClosureF hs (h.lexNorm hs)]; omega,
    h3.trans (h.card_rep_le hs (h.lexNorm hs))⟩

/-- **First defect degree `2`: at least `deg lcm` states** (`deg2_sector` with `|R| ≤ |C|`,
`|swap closure| = 2|R|`). -/
theorem StrictSystem.lcm_le_card {s : Fin 3 → List (Fin 3)}
    {C : Finset (List (Fin 3) × List (Fin 3))} (h : StrictSystem s C) (hdeg : defectDegree C = 2)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) :
    2 * (lcm ((inc s).map (Nat.cast : ℕ → ZMod 2)).charpoly
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ZMod 2))).charpoly).natDegree ≤
        (swapClosureF C).card ∧
      (lcm ((inc s).map (Nat.cast : ℕ → ZMod 2)).charpoly
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ZMod 2))).charpoly).natDegree ≤
        C.card := by
  have hs := nonerasing_of_irreducible hM
  have hle := (h.deg2_sector hdeg hM (h.lexNorm hs)).2.2.2.2.1
  exact ⟨by rw [h.card_swapClosureF hs (h.lexNorm hs)]; omega,
    hle.trans (h.card_rep_le hs (h.lexNorm hs))⟩

/-- **No strict system of first defect degree `2` with fewer than `deg lcm` states up to
side swap** (`|R| < deg lcm(χ_M mod 2, χ_{Λ²M} mod 2)`), over an irreducible `χ_M`. -/
theorem no_strictSystem_deg2_of_card_lt {s : Fin 3 → List (Fin 3)}
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    {C : Finset (List (Fin 3) × List (Fin 3))}
    (hlt : (swapClosureF C).card < 2 * (lcm ((inc s).map (Nat.cast : ℕ → ZMod 2)).charpoly
          (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ZMod 2))).charpoly).natDegree) :
    ¬ (StrictSystem s C ∧ defectDegree C = 2) :=
  fun ⟨h, hdeg⟩ => absurd (h.lcm_le_card hdeg hM).1 (not_le.2 hlt)

/-- **The odd case: no strict system of first defect degree `2` with fewer than `6` states
up to side swap** when `det M` is odd and `tr M ≢ tr Λ²M (mod 2)`. -/
theorem no_strictSystem_deg2_odd {s : Fin 3 → List (Fin 3)}
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdet : Odd ((inc s).map (Nat.cast : ℕ → ℤ)).det)
    (htr : ¬ ((inc s).map (Nat.cast : ℕ → ℤ)).trace ≡
      (Psc.Cyclicity.wedge2 ((inc s).map (Nat.cast : ℕ → ℤ))).trace [ZMOD 2])
    {C : Finset (List (Fin 3) × List (Fin 3))} (hlt : (swapClosureF C).card < 12) :
    ¬ (StrictSystem s C ∧ defectDegree C = 2) := by
  rintro ⟨h, hdeg⟩
  have hs := nonerasing_of_irreducible hM
  have h6 := (h.deg2_sector hdeg hM (h.lexNorm hs)).2.2.2.2.2 hdet htr
  rw [h.card_swapClosureF hs (h.lexNorm hs)] at hlt
  omega

/-- **No strict system of first defect degree `3` containing a state `T` with
`M^{⊗3} K₃(T) ≠ det M · K₃(T)`**, over a primitive `σ` with irreducible `χ_M` and a root `β`
whose other roots have modulus `< 1` (`StrictSystem.deg23_iii`). -/
theorem no_strictSystem_deg3_of_not_eigen {s : Fin 3 → List (Fin 3)}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    {C : Finset (List (Fin 3) × List (Fin 3))} {T : List (Fin 3) × List (Fin 3)} (hT : T ∈ C)
    (hne : Psc.Lie3.phi3 ((inc s).map (Nat.cast : ℕ → ℚ)) (Psc.Lie3.k3Vec T.1 T.2) ≠
      ((inc s).map (Nat.cast : ℕ → ℚ)).det • Psc.Lie3.k3Vec T.1 T.2) :
    ¬ (StrictSystem s C ∧ defectDegree C = 3) := fun ⟨h, hdeg⟩ =>
  hne ((h.deg23_iii hdeg hprim hM hβ hpisot (h.lexNorm _)).2.2.2.2.2.2.2 T hT)

/-- **No strict system of first defect degree `4` when `|det M| ≠ 1`**, over a primitive
`σ` with irreducible `χ_M` and a Pisot root (`StrictSystem.sieve4`). -/
theorem no_strictSystem_deg4_of_abs_det_ne_one {s : Fin 3 → List (Fin 3)}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    (hdet : |((inc s).map (Nat.cast : ℕ → ℤ)).det| ≠ 1) (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ (StrictSystem s C ∧ defectDegree C = 4) := fun ⟨h, hdeg⟩ =>
  hdet (h.sieve4 hdeg hprim hM hβ hβ1 hpisot (h.lexNorm _)).2.1

/-- `prop:cocycle`'s hypothesis "a parent–child pair occurs with both signs", on states:
some state `T ∈ C` has a block `U` of `red (σ T.1) (σ T.2)` whose swap `U.swap` is also a
block of it.  Decidable over a finite alphabet. -/
def HasBothSigns (s : α → List α) (C : Finset (List α × List α)) : Prop :=
  ∃ T ∈ C, ∃ U ∈ red (subst s T.1) (subst s T.2), U.swap ∈ red (subst s T.1) (subst s T.2)

instance (s : α → List α) (C : Finset (List α × List α)) : Decidable (HasBothSigns s C) := by
  unfold HasBothSigns; infer_instance

/-- `HasBothSigns` gives, for every normalisation of the swap-closed system, a pair of
representatives with `A i j > 0` and `B i j > 0`. -/
theorem StrictSystem.exists_both_of_hasBothSigns {s : α → List α}
    {C : Finset (List α × List α)} (h : StrictSystem s C) (hs : ∀ a, s a ≠ [])
    (hb : HasBothSigns s C) (P : Normalisation (h.swapSystem hs)) :
    ∃ i j : P.Rep, 0 < P.A i j ∧ 0 < P.B i j := by
  obtain ⟨T, hT, ⟨u, v⟩, hU, hU'⟩ := hb
  have hT' := h.mem_swapSystem hs hT
  have hUC' := h.mem_swapSystem hs (h.closed T hT _ hU)
  have key : (u, v) ∈ (h.swapSystem hs).children (repOf P hT').1 ∧
      (u, v).swap ∈ (h.swapSystem hs).children (repOf P hT').1 := by
    rcases repOf_spec P hT' with e | e <;> rw [e]
    · exact ⟨hU, hU'⟩
    · rw [P.children_swap T hT', Prod.swap_prod_mk, List.mem_map_swap, List.mem_map_swap]
      exact ⟨hU', hU⟩
  refine ⟨repOf P hUC', repOf P hT', ?_, ?_⟩ <;>
    simp only [Normalisation.A, Normalisation.B, Matrix.of_apply, List.count_pos_iff] <;>
    rcases repOf_spec P hUC' with e | e <;> rw [e]
  · exact key.1
  · exact key.2
  · exact key.2
  · rw [Prod.swap_swap]; exact key.1

/-- **No strict component of first defect degree `4` in which some state has a child in
both orientations** (`HasBothSigns`), over a primitive `σ` with irreducible `χ_M` and a
Pisot root: `StrictComponent.gauge_or_antiGauge` and
`Psc.CocycleSpectrum.not_gauge_of_both` (equivalently `cocycle_spectral_strict` against
`ρ(S) = β`). -/
theorem no_strictComponent_deg4_of_hasBothSigns {s : Fin 3 → List (Fin 3)}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hM : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : Polynomial.aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, Polynomial.aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1)
    {C : Finset (List (Fin 3) × List (Fin 3))} (hb : HasBothSigns s C) :
    ¬ (StrictComponent s C ∧ defectDegree C = 4) := by
  rintro ⟨h, hdeg⟩
  have hs := nonerasing_of_irreducible hM
  obtain ⟨i, j, hA, hB⟩ := h.exists_both_of_hasBothSigns hs hb (h.lexNorm hs)
  rcases h.gauge_or_antiGauge hdeg hprim hM hβ hβ1 hpisot (h.lexNorm hs) with
    ⟨-, g, hg⟩ | ⟨-, g, hg⟩
  · exact (Psc.CocycleSpectrum.not_gauge_of_both _ hA hB g).1 hg
  · exact (Psc.CocycleSpectrum.not_gauge_of_both _ hA hB g).2 hg

/-! ### (i) What the reductio lemmas are about -/

/-- **What a strict system refutes.**  Every state is nonproductive, no run of the
balanced pair algorithm whose `B_σ`-path reaches a state of `C` terminates with
coincidence (part (d)), and some cut pair `(c, c')`, `c ≠ c'`, has no left
strong-coincidence witness (Theorem A(1), (4)).  So every hypothesis set of the reductio
lemmas above, which contains a strict system, describes a substitution with a set of
balanced pairs on which the balanced pair algorithm, started at any state of `C` (or at
any seed whose `B_σ`-path reaches `C`, `exists_seed_not_terminates`, which needs
`C ∩ bpaStatesNC ≠ ∅`), does not terminate with coincidence, and some letter pair has no
left strong-coincidence witness.

This is the direction strict system ⇒ failure only.  Conversely, a seed whose `B_σ`-reachable
set is finite and whose run does not terminate with coincidence yields a strict system
(`exists_strictSystem_of_not_terminates`) and, for nonerasing `σ`, a strict component of
`B_σ` (`exists_bpaStrictComponent_of_not_terminates`), to which the component-level
lemmas apply; a failure of strong coincidence is **not** known to yield a strict system
(that is C4, `prob:C4`).  So the lemmas are necessary conditions on a strict system (resp.
component), hence, for nonerasing `σ` (automatic over `Fin 3` when `χ_M` is irreducible,
`nonerasing_of_irreducible`), on every finite counterexample to seeded termination, and
they are not established as necessary conditions on every failure of strong coincidence.
Nothing is claimed about PSC itself. -/
theorem StrictSystem.counterexample {s : α → List α}
    {C : Finset (List α × List α)} (h : StrictSystem s C) :
    (∀ T ∈ C, ¬ Productive s T ∧
      ∀ T₀, Relation.ReflTransGen (ChildNC s) T₀ T → ¬ TerminatesWithCoincidence s T₀) ∧
      ∃ c c', c ≠ c' ∧ CutPair C c c' ∧ ¬ StrongCoincidenceWitness s c c' := by
  obtain ⟨c, c', hcp⟩ := h.exists_cutPair
  exact ⟨fun T hT => ⟨h.not_productive hT, fun _ hp => h.not_terminates hT hp⟩,
    c, c', h.cutPair_ne hcp, hcp, h.not_witness hcp⟩

/-! #### From a strict system to a strict component (`thm:sink`)

`thm:sink`, and the last sentence of the cut-pair note's Theorem A(5) in existence form
(SCCs of the child graph are not defined here, so "every sink SCC is strict" is not
stated): a finite strict system of a nonerasing `σ` contains a strict component, namely a
minimal strict subsystem, which is closed and strongly connected, i.e. a sink SCC of the
child graph (nonerasure is needed, `erase_control`); and a seed whose `B_σ`-reachable set
is finite and whose run does not terminate with coincidence gives a strict component of
`B_σ` (`BpaStrictComponent`).  So the component-level lemmas of (g), (h)
(`kernel_cofactor`, `theoremA`, `gauge_or_antiGauge`, `closed_walk_sign`,
`no_strictComponent_deg4_of_hasBothSigns`) apply to every finite counterexample to
seeded termination of a nonerasing `σ` (over `Fin 3`, `χ_M` irreducible suffices), at the
first defect degree of the component found, which is at least that of the system
(`defectDegree_le_of_subset`). -/

namespace StrictSystem

variable {s : α → List α} {C : Finset (List α × List α)}

/-- Under nonerasure every state of a strict system has a child: `red` of a nonempty
balanced pair is nonempty (`Psc.Reduction.red_ne_nil`). -/
theorem exists_child (h : StrictSystem s C) (hs : ∀ a, s a ≠ []) {T : List α × List α}
    (hT : T ∈ C) : ∃ U, Child s T U :=
  List.exists_mem_of_ne_nil _ (red_ne_nil
    (Psc.FixedPointLimit.subst_ne_nil s hs (h.isBlock T hT).1)
    (equiv1_subst s (h.equiv1 T hT)).length_eq)

/-- The states of a strict system satisfying a predicate that is inherited by children
form a strict system, once one state satisfies it. -/
theorem filter_childClosed (h : StrictSystem s C) (p : List α × List α → Prop)
    [DecidablePred p] (hp : ∀ U ∈ C, p U → ∀ V, Child s U V → p V) (hne : ∃ U ∈ C, p U) :
    StrictSystem s (C.filter p) where
  nonempty := let ⟨U, hU, hpU⟩ := hne; ⟨U, Finset.mem_filter.2 ⟨hU, hpU⟩⟩
  isBlock U hU := h.isBlock U (Finset.mem_filter.1 hU).1
  noncoincident U hU := h.noncoincident U (Finset.mem_filter.1 hU).1
  closed U hU V hV := Finset.mem_filter.2 ⟨h.closed U (Finset.mem_filter.1 hU).1 V hV,
    hp U (Finset.mem_filter.1 hU).1 (Finset.mem_filter.1 hU).2 V hV⟩

/-- A strict subsystem has first defect degree at least that of the system. -/
theorem defectDegree_le_of_subset {C' : Finset (List α × List α)} (h' : StrictSystem s C')
    (hsub : C' ⊆ C) : defectDegree C ≤ defectDegree C' :=
  let ⟨T, hT, hK⟩ := h'.defectDegree_spec.1
  Nat.sInf_le ⟨T, hsub hT, hK⟩

/-- **The sink step** (`thm:sink`; cut-pair note, Theorem A(5), last sentence).  For
nonerasing `σ`, every state `T` of a strict system reaches a strict component `C' ⊆ C`
in which every state reaches every state (itself included) by a nonempty child path: a
strict subsystem of least cardinality among those reachable from `T`.  Its states form a
sink SCC of the child graph. -/
theorem exists_strictComponent_reachable (h : StrictSystem s C) (hs : ∀ a, s a ≠ [])
    {T : List α × List α} (hT : T ∈ C) :
    ∃ C' ⊆ C, StrictComponent s C' ∧ (∀ U ∈ C', Relation.ReflTransGen (Child s) T U) ∧
      ∀ U ∈ C', ∀ V ∈ C', Relation.TransGen (Child s) U V := by
  classical
  have hD := h.filter_childClosed (fun U => Relation.ReflTransGen (Child s) T U)
    (fun _ _ hpU _ hV => hpU.tail hV) ⟨T, hT, .refl⟩
  obtain ⟨E, hEF, hmin⟩ :=
    (((C.filter fun U => Relation.ReflTransGen (Child s) T U).powerset).filter
      fun E => StrictSystem s E).exists_min_image Finset.card
    ⟨_, Finset.mem_filter.2 ⟨Finset.mem_powerset_self _, hD⟩⟩
  obtain ⟨hED, hE⟩ := Finset.mem_filter.1 hEF
  have hED := Finset.mem_powerset.1 hED
  have conn : ∀ U ∈ E, ∀ V ∈ E, Relation.TransGen (Child s) U V := by
    intro U hU
    obtain ⟨W, hW⟩ := hE.exists_child hs hU
    have hF := hE.filter_childClosed (fun V => Relation.TransGen (Child s) U V)
      (fun _ _ hpV _ hW => hpV.tail hW) ⟨W, hE.closed U hU W hW, .single hW⟩
    have hFE : E.filter (fun V => Relation.TransGen (Child s) U V) ⊆ E := Finset.filter_subset _ _
    have hEq := Finset.eq_of_subset_of_card_le hFE
      (hmin _ (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (hFE.trans hED), hF⟩))
    intro V hV
    rw [← hEq] at hV
    exact (Finset.mem_filter.1 hV).2
  exact ⟨E, hED.trans (Finset.filter_subset _ _), ⟨hE, fun U hU V hV => Or.inl (conn U hU V hV)⟩,
    fun U hU => (Finset.mem_filter.1 (hED hU)).2, conn⟩

/-- **Every strict system of a nonerasing `σ` contains a strict component**, of first
defect degree at least that of the system. -/
theorem exists_strictComponent_subset (h : StrictSystem s C) (hs : ∀ a, s a ≠ []) :
    ∃ C' ⊆ C, StrictComponent s C' ∧ defectDegree C ≤ defectDegree C' := by
  obtain ⟨T, hT⟩ := h.nonempty
  obtain ⟨C', hsub, hC', -, -⟩ := h.exists_strictComponent_reachable hs hT
  exact ⟨C', hsub, hC', defectDegree_le_of_subset hC'.toStrictSystem hsub⟩

end StrictSystem

/-- **`thm:sink`, per seed.**  For nonerasing `σ`, a seed whose `B_σ`-reachable set is
finite and whose balanced pair algorithm does not terminate with coincidence gives a
strict component of `B_σ` (`def:bpa`, `BpaStrictComponent`): the swap closure of a sink
component (`exists_strictComponent_reachable`) of the strict system of
`exists_strictSystem_of_not_terminates`. -/
theorem exists_bpaStrictComponent_of_not_terminates [Fintype α] {s : α → List α}
    (hs : ∀ a, s a ≠ []) {T₀ : List α × List α} (h₀ : T₀ ∈ (seeds : Finset (List α × List α)))
    (hfin : {U | Relation.ReflTransGen (ChildNC s) T₀ U}.Finite)
    (hnt : ¬ TerminatesWithCoincidence s T₀) :
    ∃ C : Finset (List α × List α), BpaStrictComponent s C := by
  obtain ⟨C, hC, T, hTC, ⟨T₁, h₁, hp⟩⟩ := exists_strictSystem_of_not_terminates h₀ hfin hnt
  obtain ⟨C', -, hC', hreach, -⟩ := hC.exists_strictComponent_reachable hs hTC
  obtain ⟨U, hU⟩ := hC'.nonempty
  exact ⟨_, hC'.swapClosure.toBpa StrictSystem.swapClosure_swap_mem
    ⟨U, Finset.mem_union_left _ hU,
      T₁, h₁, hp.trans (reflTransGen_childNC (hreach U hU) (hC'.noncoincident U hU))⟩⟩

/-- **`thm:sink`** (`def:bpa`; G1 enters as the hypothesis that `B_σ` is finite): for
nonerasing `σ`, if `B_σ` is finite and has a nonproductive state, it has a strict
component. -/
theorem exists_bpaStrictComponent_of_finite [Fintype α] {s : α → List α} (hs : ∀ a, s a ≠ [])
    (hfin : (bpaStatesNC s).Finite) (hnp : ∃ U ∈ bpaStatesNC s, ¬ Productive s U) :
    ∃ C : Finset (List α × List α), BpaStrictComponent s C := by
  obtain ⟨U, ⟨T₀, h₀, hp⟩, hU⟩ := hnp
  exact exists_bpaStrictComponent_of_not_terminates hs h₀
    (hfin.subset fun V hV => ⟨T₀, h₀, hV⟩) fun ht => hU (ht.2 U hp)

/-- The erasing substitution `0, 1 ↦ ε` on two letters. -/
def eraseSubst : Fin 2 → List (Fin 2) := fun _ => []

/-- **Negative control: nonerasure cannot be dropped from the sink step**
(`exists_strictComponent_reachable`, `exists_strictComponent_subset`).  Over the erasing
`eraseSubst`, `{(01, 10)}` is a strict system (its state has no children, so closure is
vacuous), but no subset of it is a strict component (a nonempty child path from the state
would need a child). -/
theorem erase_control : StrictSystem eraseSubst {tmPair} ∧
    ∀ C' ⊆ ({tmPair} : Finset (List (Fin 2) × List (Fin 2))), ¬ StrictComponent eraseSubst C' := by
  refine ⟨⟨⟨tmPair, by decide⟩, by decide, by decide, by decide⟩, fun C' hC' h => ?_⟩
  obtain ⟨T, hT⟩ := h.nonempty
  have hnc : ∀ U, ¬ Child eraseSubst T U := by
    rw [Finset.mem_singleton.1 (hC' hT)]
    intro U hU
    have he : red (subst eraseSubst tmPair.1) (subst eraseSubst tmPair.2) = [] := by decide
    rw [Child, he] at hU
    simp at hU
  rcases h.connected T hT T hT with p | p <;>
    obtain ⟨U, hU, -⟩ := Relation.TransGen.head'_iff.1 p <;> exact hnc U hU

/-- **The reductio lemmas are vacuous over a strongly coincident substitution**: if every
pair of distinct letters has a left strong-coincidence witness, no strict component (no
strict system) exists, so no hypothesis set above is met
(`no_strictSystem_of_strongCoincidence`). -/
theorem no_strictComponent_of_strongCoincidence {s : α → List α}
    (hw : ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') (C : Finset (List α × List α)) :
    ¬ StrictComponent s C :=
  fun h => no_strictSystem_of_strongCoincidence hw C h.toStrictSystem

/-- **The specimens of part 1 (c)**: over the plastic substitution, its reversal, the census
substitution `011/2/120`, its reversal and relabelling, Tribonacci, `01/121/012` and
`01/12/021`, no strict system exists, so every reductio lemma above is vacuous there. -/
theorem specimens_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem Psc.Degree2Sector.plasticSubst C ∧ ¬ StrictSystem plasticRevSubst C ∧
      ¬ StrictSystem Psc.Degree3Sector.censusSubst C ∧ ¬ StrictSystem censusRevSubst C ∧
      ¬ StrictSystem censusRevNF C ∧ ¬ StrictSystem tribSubst C ∧
      ¬ StrictSystem m121Subst C ∧ ¬ StrictSystem u021Subst C :=
  ⟨plastic_no_strictSystem C, plasticRev_no_strictSystem C, census_no_strictSystem C,
    censusRev_no_strictSystem C, censusRevNF_no_strictSystem C, trib_no_strictSystem C,
    m121_no_strictSystem C, u021_no_strictSystem C⟩

/-- **The plastic substitution meets every substitution-level hypothesis** of the reductio
lemmas (irreducible `χ_M`, primitive, a Pisot root; `det M = 1`, so even the conclusion
`|det M| = 1` of `sieve4` holds), **and carries no strict system**: the lemmas are vacuous
over it because their strict-system hypothesis fails, not because of the matrix. -/
theorem plastic_vacuous :
    Irreducible ((inc Psc.Degree2Sector.plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (∃ k ≥ 1, ∀ a c, 0 < (inc Psc.Degree2Sector.plasticSubst ^ k) a c) ∧
      (∃ β : ℂ, Polynomial.aeval β
          ((inc Psc.Degree2Sector.plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
        1 < ‖β‖ ∧ ∀ z : ℂ, Polynomial.aeval z
          ((inc Psc.Degree2Sector.plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
            z ≠ β → ‖z‖ < 1) ∧
      ∀ C, ¬ StrictSystem Psc.Degree2Sector.plasticSubst C := by
  obtain ⟨hM, hprim, ⟨b, hb1, hb, hbp⟩, -⟩ := Psc.Degree4Floor.plastic_matrix_controls
  refine ⟨hM, hprim, ⟨b, hb, ?_, hbp⟩, plastic_no_strictSystem⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hb1

/-- **The same for the census substitution `011/2/120`** (`χ_M = X³ − 2X² − 1`). -/
theorem census_vacuous :
    Irreducible ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (∃ k ≥ 1, ∀ a c, 0 < (inc Psc.Degree3Sector.censusSubst ^ k) a c) ∧
      (∃ β : ℂ, Polynomial.aeval β
          ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
        1 < ‖β‖ ∧ ∀ z : ℂ, Polynomial.aeval z
          ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
            z ≠ β → ‖z‖ < 1) ∧
      ∀ C, ¬ StrictSystem Psc.Degree3Sector.censusSubst C := by
  obtain ⟨b, hb2, hb3, hb⟩ := Psc.Degree3Sector.census_real_root
  refine ⟨Psc.Degree3Sector.census_irreducible, Psc.Degree3Sector.censusSubst_primitive,
    ⟨b, by rw [Psc.Degree3Sector.census_aeval]; exact_mod_cast hb, ?_, fun z hz hzb =>
      (Psc.Degree3Sector.census_other hb2 hb3 hb
        (by rw [← Psc.Degree3Sector.census_aeval]; exact hz) hzb).2.2⟩,
    census_no_strictSystem⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith

/-- **`m0Subst` carries no strict system**, an instance of `thm:global-sync`: every image
of the `Psc.Degree4Floor` control `m0Subst` (`M = M0`, `det M = −2`) begins with `0`, so
`σ_+` is constant and every letter pair has a left strong-coincidence witness at level `1`
(least witness level `1` for `01`, `02`, `12`, by `decide`); Theorem A(4) then excludes
every strict system.  So `Psc.Degree4Floor.m0_no_degree4`, which excludes first defect
degree `4` for every normalised child system over `m0Subst`, is not needed for strict
systems. -/
theorem m0_no_strictSystem (C : Finset (List (Fin 3) × List (Fin 3))) :
    ¬ StrictSystem Psc.Degree4Floor.m0Subst C := by
  have h : LeastWitnessLevel Psc.Degree4Floor.m0Subst 0 1 1 ∧
      LeastWitnessLevel Psc.Degree4Floor.m0Subst 0 2 1 ∧
      LeastWitnessLevel Psc.Degree4Floor.m0Subst 1 2 1 := by decide +kernel
  exact no_strictSystem_of_strongCoincidence (fin3_all_pairs (witness_of_least h.1)
    (witness_of_least h.2.1) (witness_of_least h.2.2)) C

/-! #### The hypotheses of the exclusion forms can hold

For each exclusion form of (h) with a matrix- or state-level hypothesis beyond the
substitution-level ones, a specimen meets all its hypotheses except the strict system
itself.  Over each specimen no strict system exists at all (Theorem A(4), by the least
witness levels of (c)), so there the exclusion is redundant: these controls show only
that the hypotheses are jointly satisfiable, not that an exclusion form ever does work
that Theorem A(4) does not. -/

/-- **`no_strictSystem_deg2_odd`**: the plastic substitution has irreducible `χ_M`, odd
`det M` and `tr M ≢ tr Λ²M (mod 2)` (`Psc.Degree2Sector.plastic_irreducible`,
`plastic_odd`, `plastic_trace`), and carries no strict system. -/
theorem no_strictSystem_deg2_odd_control :
    Irreducible ((inc Psc.Degree2Sector.plasticSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      Odd ((inc Psc.Degree2Sector.plasticSubst).map (Nat.cast : ℕ → ℤ)).det ∧
      ¬ ((inc Psc.Degree2Sector.plasticSubst).map (Nat.cast : ℕ → ℤ)).trace ≡
        (Psc.Cyclicity.wedge2
          ((inc Psc.Degree2Sector.plasticSubst).map (Nat.cast : ℕ → ℤ))).trace [ZMOD 2] ∧
      ∀ C, ¬ StrictSystem Psc.Degree2Sector.plasticSubst C := by
  rw [Psc.Degree2Sector.plastic_inc]
  exact ⟨Psc.Degree2Sector.plastic_irreducible, Psc.Degree2Sector.plastic_odd,
    Psc.Degree2Sector.plastic_trace, plastic_no_strictSystem⟩

/-- **`no_strictSystem_deg3_of_not_eigen`**: `011/2/120` is primitive with irreducible
`χ_M` and a Pisot root (`census_vacuous`), and the census state
`(011212001, 120011120)` (`Psc.Degree3Sector.censusPair`) is `∼₂` with `K₃ ≠ 0` and
`M^{⊗3} K₃ ≠ det M · K₃` (`Psc.Degree3Sector.census_state`, through
`phi3_ne_smul_of_coord`); there is no strict system over `011/2/120`. -/
theorem no_strictSystem_deg3_control :
    (∃ k ≥ 1, ∀ a c, 0 < (inc Psc.Degree3Sector.censusSubst ^ k) a c) ∧
      Irreducible ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (∃ β : ℂ, Polynomial.aeval β
          ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
        ∀ z : ℂ, Polynomial.aeval z
          ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
            z ≠ β → ‖z‖ < 1) ∧
      Equiv2 Psc.Degree3Sector.censusPair.1 Psc.Degree3Sector.censusPair.2 ∧
      Psc.Lie3.k3Vec Psc.Degree3Sector.censusPair.1 Psc.Degree3Sector.censusPair.2 ≠ 0 ∧
      Psc.Lie3.phi3 ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ))
          (Psc.Lie3.k3Vec Psc.Degree3Sector.censusPair.1 Psc.Degree3Sector.censusPair.2) ≠
        ((inc Psc.Degree3Sector.censusSubst).map (Nat.cast : ℕ → ℚ)).det •
          Psc.Lie3.k3Vec Psc.Degree3Sector.censusPair.1 Psc.Degree3Sector.censusPair.2 ∧
      ∀ C, ¬ StrictSystem Psc.Degree3Sector.censusSubst C := by
  obtain ⟨hM, hprim, ⟨β, hβ, -, hpisot⟩, hno⟩ := census_vacuous
  obtain ⟨h2, hK, hne⟩ := Psc.Degree3Sector.census_state
  exact ⟨hprim, hM, ⟨β, hβ, hpisot⟩, h2, hK, hne Psc.Degree3Sector.censusEmpty rfl _, hno⟩

/-- **`no_strictSystem_deg4_of_abs_det_ne_one`**: the `Psc.Degree4Floor` control
`m0Subst` (`M = M0`) is primitive with irreducible `χ_M = X³ − 32X² + 5X + 2` and a Pisot
root (`Psc.Degree4Floor.m0Subst_primitive`, `Psc.KernelCofactor.ctrl_irreducible`,
`Psc.Degree4Floor.m0_perron_control`), and `det M = −2` (`Psc.SectorBridge.M0_det`); there
is no strict system over it (`m0_no_strictSystem`). -/
theorem no_strictSystem_deg4_control :
    (∃ k ≥ 1, ∀ a c, 0 < (inc Psc.Degree4Floor.m0Subst ^ k) a c) ∧
      Irreducible ((inc Psc.Degree4Floor.m0Subst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (∃ β : ℂ, Polynomial.aeval β
          ((inc Psc.Degree4Floor.m0Subst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧ 1 < ‖β‖ ∧
        ∀ z : ℂ, Polynomial.aeval z
          ((inc Psc.Degree4Floor.m0Subst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
            z ≠ β → ‖z‖ < 1) ∧
      ((inc Psc.Degree4Floor.m0Subst).map (Nat.cast : ℕ → ℤ)).det = -2 ∧
      ∀ C, ¬ StrictSystem Psc.Degree4Floor.m0Subst C := by
  obtain ⟨-, -, -, -, β, hβ, hβ1, hpisot, -⟩ := Psc.Degree4Floor.m0_perron_control
  rw [Psc.Degree4Floor.incQ_m0Subst]
  refine ⟨Psc.Degree4Floor.m0Subst_primitive, Psc.KernelCofactor.ctrl_irreducible,
    ⟨β, hβ, hβ1, hpisot⟩, ?_, m0_no_strictSystem⟩
  rw [Psc.Degree4Floor.inc_m0Subst, Matrix.det_fin_three]
  simp

/-! #### Controls: the known three-letter strict components fail `χ_M` irreducible -/

/-- `012/120/201` is primitive (`M = J > 0`). -/
theorem cyc_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc cycSubst ^ k) a c :=
  ⟨1, le_rfl, by rw [pow_one]; show ∀ a c : Fin 3, 0 < (cycSubst c).count a; decide⟩

/-- `χ_M` of `012/120/201` is reducible: `det M = 0`. -/
theorem cyc_not_irreducible : ¬ Irreducible ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly :=
  fun hM => Psc.Cyclicity.det_ne_zero_of_irreducible _ hM (by
    rw [Matrix.det_fin_three]; simp [inc, cycSubst])

/-- `10/102/211` is primitive (`M² > 0`). -/
theorem carrier_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc carrierSubst ^ k) a c :=
  ⟨2, by norm_num, fun a c => by fin_cases a <;> fin_cases c <;> decide +kernel⟩

/-- `χ_M` of `10/102/211` is reducible: `1` is a root (`χ_M = (X − 1)(X² − 2X − 2)`). -/
theorem carrier_not_irreducible :
    ¬ Irreducible ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly :=
  fun hM => Psc.Cyclicity.not_isRoot_of_irreducible _ hM 1 (by
    rw [Matrix.eval_charpoly, Matrix.det_fin_three]; simp [inc, carrierSubst])

open Polynomial in
/-- `χ_M = X³ − 3X²` for `012/120/201` (`M = J`: `tr M = 3`, `tr Λ²M = 0`, `det M = 0`). -/
theorem cyc_charpoly_Q :
    ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly = X ^ 3 - C 3 * X ^ 2 := by
  rw [Psc.Cyclicity.charpoly_fin_three]
  have h1 : ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).trace = 3 := by
    rw [Matrix.trace_fin_three]; simp [inc, cycSubst]; norm_num
  have h2 : (Psc.Cyclicity.wedge2 ((inc cycSubst).map (Nat.cast : ℕ → ℚ))).trace = 0 := by
    rw [Matrix.trace_fin_three]
    simp [Psc.Cyclicity.wedge2, Psc.Cyclicity.pairFst, Psc.Cyclicity.pairSnd, inc, cycSubst]
  have h3 : ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).det = 0 := by
    rw [Matrix.det_fin_three]; simp [inc, cycSubst]
  rw [h1, h2, h3]; simp

open Polynomial in
/-- `012/120/201` meets the Pisot-root hypothesis in the form the reductio lemmas use:
`β = 3`, and the other root `0` has modulus `< 1`. -/
theorem cyc_pisot_root : ∃ β : ℂ, aeval β ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
    1 < ‖β‖ ∧ ∀ z : ℂ, aeval z ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ β → ‖z‖ < 1 := by
  refine ⟨3, ?_, ?_, fun z hz hzb => ?_⟩
  · rw [cyc_charpoly_Q]; simp; norm_num
  · norm_num
  · rw [cyc_charpoly_Q] at hz
    simp at hz
    have : z ^ 2 * (z - 3) = 0 := by linear_combination hz
    rcases mul_eq_zero.1 this with h | h
    · have : z = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      subst this; simp
    · exact absurd (sub_eq_zero.1 h) hzb

/-- `10/102/211` fails the Pisot-root hypothesis: `1` is a root of `χ_M`, of modulus `1`. -/
theorem carrier_not_pisot : ¬ ∃ β : ℂ,
    Polynomial.aeval β ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧ 1 < ‖β‖ ∧
      ∀ z : ℂ, Polynomial.aeval z ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
        z ≠ β → ‖z‖ < 1 := by
  rintro ⟨β, -, hβ1, hz⟩
  have h1 : Polynomial.aeval (1 : ℂ) ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 := by
    have h : ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly.eval 1 = 0 := by
      rw [Matrix.eval_charpoly, Matrix.det_fin_three]; simp [inc, carrierSubst]
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_one, h, map_zero]
  rcases eq_or_ne (1 : ℂ) β with e | e
  · rw [← e, norm_one] at hβ1; exact lt_irrefl _ hβ1
  · have h2 := hz 1 h1 e
    rw [norm_one] at h2; exact lt_irrefl _ h2

/-- **Leave-one-out at the strict-component level.**  `cycC` over `012/120/201` and the
sink of `10/102/211` are strict components over primitive substitutions, `cycC` with first
defect degree `2`.  `cycC` fails only `χ_M` irreducible among the substitution-level
hypotheses: `σ` is primitive and meets the Pisot-root hypothesis (`β = 3`,
`cyc_pisot_root`).  The sink of `10/102/211` fails both `χ_M` irreducible and the Pisot
root (the root `1` has modulus `1`, `carrier_not_pisot`).  No strict component meeting
all of them is known. -/
theorem strictComponent_controls :
    (StrictComponent cycSubst cycC ∧ defectDegree cycC = 2 ∧
        (∃ k ≥ 1, ∀ a c, 0 < (inc cycSubst ^ k) a c) ∧
        (∃ β : ℂ, Polynomial.aeval β ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
          1 < ‖β‖ ∧ ∀ z : ℂ,
            Polynomial.aeval z ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
              z ≠ β → ‖z‖ < 1) ∧
        ¬ Irreducible ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly) ∧
      StrictComponent carrierSubst carrierSink ∧
        (∃ k ≥ 1, ∀ a c, 0 < (inc carrierSubst ^ k) a c) ∧
        ¬ Irreducible ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
        ¬ ∃ β : ℂ,
          Polynomial.aeval β ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 ∧
            1 < ‖β‖ ∧ ∀ z : ℂ,
              Polynomial.aeval z ((inc carrierSubst).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
                z ≠ β → ‖z‖ < 1 :=
  ⟨⟨cyc_strictComponent, cyc_defectDegree, cyc_primitive, cyc_pisot_root, cyc_not_irreducible⟩,
    carrierSink_strictComponent, carrier_primitive, carrier_not_irreducible, carrier_not_pisot⟩

/-- `M` of `012/120/201` modulo `2` is the all-ones matrix. -/
theorem cyc_inc_two : (inc cycSubst).map (Nat.cast : ℕ → ZMod 2) = Matrix.of fun _ _ => 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- `Λ²M ≡ 0 (mod 2)` for `012/120/201` (all `2 × 2` minors of the all-ones matrix vanish). -/
theorem cyc_wedge2_two : Psc.Cyclicity.wedge2 ((inc cycSubst).map (Nat.cast : ℕ → ZMod 2)) = 0 := by
  rw [cyc_inc_two]; ext I J; fin_cases I <;> fin_cases J <;> decide

/-- `χ_M ≡ X²(X − 1) (mod 2)` for `012/120/201`. -/
theorem cyc_charpoly_two : ((inc cycSubst).map (Nat.cast : ℕ → ZMod 2)).charpoly =
    Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C 1) := by
  rw [Psc.Cyclicity.charpoly_fin_three, cyc_inc_two]
  have htr : (Matrix.of fun _ _ => (1 : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2)).trace = 1 := by
    rw [Matrix.trace_fin_three]; decide
  have hw : (Psc.Cyclicity.wedge2 (Matrix.of fun _ _ => (1 : ZMod 2))).trace = 0 := by
    rw [← cyc_inc_two, cyc_wedge2_two, Matrix.trace_zero]
  have hdet : (Matrix.of fun _ _ => (1 : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 0 := by
    rw [Matrix.det_fin_three]; decide
  rw [htr, hw, hdet]
  simp only [map_one, map_zero, one_mul, zero_mul, add_zero, sub_zero]
  ring

/-- `deg lcm(χ_M mod 2, χ_{Λ²M} mod 2) ≥ 4` for `012/120/201`: `X³` and `X − 1` divide it. -/
theorem cyc_lcm_natDegree : 4 ≤ (lcm ((inc cycSubst).map (Nat.cast : ℕ → ZMod 2)).charpoly
    (Psc.Cyclicity.wedge2 ((inc cycSubst).map (Nat.cast : ℕ → ZMod 2))).charpoly).natDegree := by
  rw [cyc_wedge2_two, Matrix.charpoly_zero, Fintype.card_fin, cyc_charpoly_two]
  have hcop : IsCoprime (Polynomial.X ^ 3 : Polynomial (ZMod 2)) (Polynomial.X - Polynomial.C 1) :=
    IsCoprime.pow_left ⟨1, -1, by rw [map_one]; ring⟩
  have hd : Polynomial.X ^ 3 * (Polynomial.X - Polynomial.C 1) ∣
      lcm (Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C (1 : ZMod 2))) (Polynomial.X ^ 3) :=
    hcop.mul_dvd (dvd_lcm_right _ _) ((dvd_mul_left _ _).trans (dvd_lcm_left _ _))
  have hne : lcm (Polynomial.X ^ 2 * (Polynomial.X - Polynomial.C (1 : ZMod 2)))
      (Polynomial.X ^ 3) ≠ 0 := by
    rw [Ne, lcm_eq_zero_iff]
    push Not
    exact ⟨mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Polynomial.X_sub_C_ne_zero 1),
      pow_ne_zero _ Polynomial.X_ne_zero⟩
  have h4 : (Polynomial.X ^ 3 * (Polynomial.X - Polynomial.C (1 : ZMod 2))).natDegree = 4 := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (Polynomial.X_sub_C_ne_zero 1), Polynomial.natDegree_X_pow, Polynomial.natDegree_X_sub_C]
  exact h4 ▸ Polynomial.natDegree_le_of_dvd hd hne

/-- `cycC` has three states up to side swap. -/
theorem cyc_card_rep : Fintype.card (cyc_strictSystem.lexNorm (by decide)).Rep = 3 := by
  rw [Fintype.card_coe, StrictSystem.lexNorm_R]; decide

/-- **Negative control: `χ_M` irreducible cannot be dropped from the bound
`|R| ≥ deg lcm` of `deg2_sector`, even on a strict component of a primitive substitution.**
`cycC` over `012/120/201` is a strict component with first defect degree `2`, `σ` is
primitive, and every other hypothesis of `StrictComponent.deg2_sector` holds, but `|R| = 3`
while `deg lcm(χ_M mod 2, χ_{Λ²M} mod 2) ≥ 4` (so also `|C| = 3 < deg lcm`, against
`StrictSystem.lcm_le_card`). -/
theorem cyc_lcm_control : StrictComponent cycSubst cycC ∧ defectDegree cycC = 2 ∧
    (∃ k ≥ 1, ∀ a c, 0 < (inc cycSubst ^ k) a c) ∧
    ¬ Irreducible ((inc cycSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
    Fintype.card (cyc_strictSystem.lexNorm (by decide)).Rep = 3 ∧ cycC.card = 3 ∧
    3 < (lcm ((inc cycSubst).map (Nat.cast : ℕ → ZMod 2)).charpoly
      (Psc.Cyclicity.wedge2 ((inc cycSubst).map (Nat.cast : ℕ → ZMod 2))).charpoly).natDegree :=
  ⟨cyc_strictComponent, cyc_defectDegree, cyc_primitive, cyc_not_irreducible, cyc_card_rep,
    by decide, cyc_lcm_natDegree⟩

/-- `HasBothSigns` is met by a strict component (Thue–Morse, where `(01,10)` and `(10,01)`
are both children of `(01,10)`) and fails on `cycC` and on the sink of `10/102/211`. -/
theorem hasBothSigns_controls : HasBothSigns thueMorseSubst {tmPair, tmPair.swap} ∧
    ¬ HasBothSigns cycSubst cycC ∧ ¬ HasBothSigns carrierSubst carrierSink := by
  decide +kernel

end Psc.StrictSystem
