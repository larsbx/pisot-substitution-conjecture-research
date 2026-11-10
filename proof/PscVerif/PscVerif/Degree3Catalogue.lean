import PscVerif.Degree3Sector
import PscVerif.Descendants

/-!
# `comp:defect`: the 24 degree-three catalogue occurrences, checked

`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, `comp:defect` (line 1200: "The `24`
degree-three states occur in `12` substitutions, two per substitution, [...] with lengths `9`
and `19`; [...] all with `χ_M = x³ - 2x² - 1` and `det M = 1`; [...] every one of the `24`
states reaches a coincidence block within two inflations") and its "Meaning" paragraph
(line 1204: none of the `24` "satisfies the necessary condition
`im Q₃ ⊆ ker (Φ₃ - det M)` of Theorem `thm:deg23`(iii) for membership in a strict
component"); `def:balanced` (line 279), `def:bpa` (line 290), `lem:descendants` (line 294),
`thm:deg23` (iii) (line 733).  `docs/c4-defect-degree-census.md` §§2–5 (the catalogue, its
normal forms, its spectral data, its leakage pattern) and §7 (the finite-corpus
degree-three exclusion); `docs/c4-concentration-attack-2026-11-06.md` §8 (Lean coverage).
This module extends `Psc.Degree3Sector.census_not_mem` (one state over one substitution) to
all `24` occurrences and replaces the scratch inflation checks its docstring cites.

**Source of the 24.**  The occurrences are the `24` `D3_STATE_JSON` lines of the canonical
Mojo catalogue, `cd kernel && pixi run --locked mojo run -I . degree3_catalog.mojo`
(`DEGREE3_OCCURRENCES 24`, `strict first-degree3 components: 0`), transcribed with their
image indices `(i, j, k)` and their state words in the printed orientation `u|v`;
`Occ.Check` decodes `(i, j, k)` against `imageWords`, the image order of
`kernel/psc/corpus.mojo`.  The other fields of `Occ` (a seed path, two coordinates, a
return path) are witnesses from an untrusted scratch search; nothing rests on that search,
because `catalogue_check` and `catalogue_ret_check` re-check every witness by kernel
evaluation (`decide +kernel`).

Words are over `Fin 3`, the Mojo letters `0, 1, 2`.  `toSubst σ` is the substitution with
images `σ = (σ 0, σ 1, σ 2)`, and `incOf σ` is its rational incidence matrix `M`.  States are
ordered pairs, as in `Psc.Descendants`, and `bpaStatesNC` is closed under side swap on
noncoincident states (`swap_mem_bpaStatesNC`).

## Proved here, in full

* **Generic path and leak tools** (any alphabet with decidable equality): `chainTo` (a
  `Bool` path check) with `chainTo_sound` (a checked path is a `ChildNC` path) and
  `mem_bpaStatesNC_of_chainTo` (a checked path from a seed `(ab, ba)` ends in `B_σ`);
  `transGen_of_chainTo` (a checked nonempty path is a `TransGen` path);
  `swap_mem_bpaStatesNC`; `mem_of_mem_descR` (a child-closed set contains every descendant
  of its states); `not_mem_of_descR_coincidence` (a state with a coincidence block among its
  depth-`n` descendants is in no child-closed coincidence-free set, finite or not);
  `mem_descR_one`, `mem_descR_two`, `mem_red_iterate_of_descR`.
* **Generic spectral tools** (three letters): `phi3_ne_smul_of_coord_nat` and
  `phi3_ne_smul_of_coord_nat_swap` (a coordinate with `K₃ = 0` and `(M^{⊗3} K₃) ≠ 0` rules out
  `M^{⊗3} K₃ = c K₃` for every rational `c`, in both orientations; the
  substitution-independent form of `Psc.Degree3Sector.phi3_ne_smul_of_coord`);
  `k3Vec_ne_of_coord`, `k3Vec_swap_ne`.
  **`cubic_certificate`**: every rational `3 × 3` matrix with `χ = X³ - 2X² - 1` meets the
  matrix hypotheses of `thm:deg23` (iii): `χ` is irreducible and has a real root `b > 2`
  and two further roots of modulus `< 1`, all three pairwise distinct.  The proof
  transports `census_irreducible` and `census_pisot` along the characteristic polynomial,
  since the certificates depend only on it.
  `charpoly_of_nat` gives `χ_M = X³ - 2X² - 1` and `det M = 1` from three natural identities
  with no subtraction, via `Psc.Cyclicity.charpoly_fin_three`.
  **`not_mem_of_coord`**: over a primitive `σ` with this `χ_M`, a pair with a coordinate
  certificate is a state of no child system that has `∼₂` states and a normalisation.  The
  proof applies `deg23_iii_of_primitive`, step (c), to the representative `T` or `T.swap`.
* **Relabelling equivariance** (any alphabets, an injective `f`, a conjugacy
  `σ' ∘ f = map f ∘ σ`): `subst_map`, `redAux_map` / `red_map` (`red` commutes with
  `relabel f`), `child_map`, **`relabel_mem_bpaStatesNC`** (`B_σ` relabels into `B_σ'`);
  `n2_map`, `equiv2_map`, `equiv2_map_iff` (`∼₂` is invariant under a bijection);
  `relabel_swap`, `relabel_relabel`, `relabel_injective`.  **`bpaStatesNC_conj`**: along an
  equivalence, `B_σ'` is exactly the relabelling of `B_σ`.  Counting: `ncard_sep_image`,
  `ncard_of_list`, `ncard_sep_of_list`.
* **The catalogue** (`catalogue`, `occurrences`; `catalogue_check` by kernel evaluation)
  and **`catalogue_spec`** / **`occurrences_spec`**.  Every one of the `24` occurrences
  `(σ, T)` satisfies `OccSpec σ T`:
  - (a) `T` and `T.swap` are vertices of `B_σ`, reached from a seed by an explicit checked
    `ChildNC` path (`reachable`), and `T` is recurrent: it lies on a cycle of `B_σ`, by a
    checked return path of seven steps (`recurrent`).
  - (b) `T` is noncoincident and `∼₂` (`K₁ = K₂ = 0`), with `K₃(T) ≠ 0` (`equiv2`, `k3_ne`).
  - (c) The leak pattern (`leak`).  A length-`9` state has exactly one child, the length-`19`
    catalogue state over the same `σ` up to side swap.  A length-`19` state has exactly five
    pairwise distinct children, exactly one of them a coincidence block.
  - (d) A coincidence block is a block of `red (σⁿ T.1) (σⁿ T.2)` for some `n ∈ {1, 2}`
    (`leak_two`), so no child-closed coincidence-free set contains `T` (`not_closed`).
  - (e) `σ` is primitive (`M² > 0`), with `χ_M = X³ - 2X² - 1` and `det M = 1`
    (`primitive`, `charpoly`, `det`).  `M^{⊗3} K₃(T) ≠ c K₃(T)` for every rational `c`, in
    particular for `c = det M` (`phi3_ne`).  `T` is a state of no `∼₂` child system over `σ`
    that has a normalisation (`not_mem`).
  `catalogue_pisot` gives the matrix hypotheses of `thm:deg23` (iii) for all twelve
  substitutions.  `catalogue_counts`: there are `24` distinct occurrences over `12` distinct
  substitutions, exactly one of length `9` and one of length `19` per substitution.
* **The twelve automata, exactly.**  `closureO` is a fuelled closure under the children of
  noncoincident states; it fails closed, returning `none` when the fuel is exhausted.  It is
  sound in both directions: `closureO_sound` (worklist invariant) with
  `bpaStatesNC_subset_of_closed` gives `B_σ ⊆ F`, and `closureO_subset` with
  `bpaStatesNC_closed` gives `F ⊆ B_σ`; `closureO_nodup` (via `addNew_nodup`) shows `F`
  has no repetition.  `completeCheck fuel σ stats` packages this with pinned statistics
  (`closureStats`: states, noncoincident states, noncoincident `∼₂` states);
  `exact_of_check`, `complete_of_check` and `card_of_check` read off what it certifies.
  `complete_sigmaA` and `complete_sigmaB` are the two kernel evaluations, one per class
  representative; `transfer_table` relabels the base occurrences.
  **`catalogue_complete`**: for each catalogue `σ`, `B_σ` is finite (G1 for `σ`) and every
  noncoincident `∼₂` vertex of `B_σ` is a catalogue state over `σ`, up to side swap.
  **`catalogue_exact`**: over each of the twelve automata, the noncoincident `∼₂` vertices
  are exactly the two catalogue states and their swaps.
  **`catalogue_card`**: each of the twelve `B_σ` has exactly `226` vertices (ordered
  pairs), `224` of them noncoincident, and exactly `4` of those `∼₂`.
  **`catalogue_degree_two`**: every other noncoincident vertex has `K₁ = 0` and `K₂ ≠ 0`
  (first defect degree two); **`catalogue_k3_ne`**: every noncoincident `∼₂` vertex has
  `K₃ ≠ 0` (no first defect degree `≥ 4`).
  **`no_closed_equiv2`** (§7 over the twelve automata): no nonempty child-closed,
  coincidence-free set of vertices of `B_σ` has only `∼₂` states, so `B_σ` has no strict
  component of first defect degree `≥ 3`.  It is proved by leakage alone (`not_closed`),
  without the spectral exclusion (`not_mem`).
* **The normal forms of `docs/c4-defect-degree-census.md` §3.**
  - `catalogue_orbit`: the catalogue is the relabelling orbit of the four occurrences
    (`basePairs`, `basePairs_sub`) over `sigmaA = 011/2/120` (`= censusSubst`, `sigmaA_eq`)
    and `sigmaB = 1/210/002`.  Each occurrence is `(π τ π⁻¹, π R)`, up to side swap, for one
    permutation `π`.
  - `catalogue_state_classes`: every state is a relabelling of one of §3's four state
    classes, up to side swap.  `state_classes_exact`: each class is attained and no two
    are equivalent under relabelling and side swap; with `perms3_complete` (`perms3` is all
    of `Sym {0,1,2}`) the catalogue meets exactly four classes.
  - `catalogue_sigma_classes`: every substitution is conjugate to `sigmaA` or `sigmaB`;
    `sigma_classes_exact`: both occur and they are not conjugate, so there are exactly two.
  - `reversal_exchanges`: §3's reversal statements.
  - `class9b_eq`: `class9b` is `Psc.Degree3Sector.censusPair`.
* **Controls.**
  - Negative: `class9a_sigmaA_control`.  The pair `class9a` is `∼₂` with `K₃ ≠ 0`, and
    `sigmaA` is a catalogue substitution, but the catalogue does not pair them.  Over
    `sigmaA`, `class9a` inflates to a single `∼₂` block of length `21` that is no catalogue
    state, and none of its depth-one or depth-two descendants is a coincidence block.  So
    (c) and (d) are facts about the catalogue pairs, not about every `∼₂` length-`9` pair
    over these substitutions.  `class9a_not_mem_sigmaA`: `class9a` is not a vertex of
    `B_σ` for `σ = sigmaA`.
  - Non-vacuity of (d): `tm_closed_control`.  For Thue–Morse the seed lies in a
    child-closed coincidence-free set.
  - Fail-closed: `budget_control`.  With a budget of `10` steps the closure over `sigmaA`
    returns `none` and `completeCheck` returns `false`.  `stats_control`: any vertex count
    other than `226` is refused by the full check over `sigmaA`.

## Not proved here

* **The corpus census.**  That these `24` are *all* the reachable degree-three states of the
  `4,554`-member corpus is the finite computation `kernel/degree3_catalog.mojo`.  It
  includes that the other `4,542` substitutions have none, and that the corpus is the PIP
  screen of `kernel/psc/corpus.mojo`.  Nothing here enumerates the corpus.  Completeness is
  proved only inside the twelve automata `B_σ` of the catalogue substitutions
  (`catalogue_complete`).
* **The sink SCC.**  "All `24` in the unique noncoincident sink SCC" (§2) is not
  formalized.  Recurrence (each state lies on a cycle, `OccSpec.recurrent`) and the exact
  vertex set of each of the twelve `B_σ` (`exact_of_check`, `catalogue_card`) are proved;
  the strongly connected components of `B_σ`, and which of them are sinks, are not
  computed here.
* **The `Θ(K₃)` invariants** of §4 are not formalized: `|det Θ(K₃)| = 2`,
  `tr Θ(K₃)² = 6`, and `Θ(K₃)` not commuting with `M`.  `phi3_ne` (`K₃(T)` is no
  eigenvector of `M^{⊗3}`) is proved instead, which is what `thm:deg23` (iii) (c) needs.
* **The finite-corpus exclusion of `docs/c4-defect-degree-census.md` §7 beyond the twelve
  automata.**  `no_closed_equiv2` is §7 for the twelve catalogue substitutions.  For the
  other `4,542` substitutions of the corpus, §7 rests on the Mojo census, which reports that
  their automata have no noncoincident `∼₂` vertex at all; that is not formalized.  The
  spectral exclusion (`not_mem`) is proved per state.  That a strict component carries a
  normalised child system with `∼₂` states (via `Psc.Descendants.lexNormalisation`) is not
  restated here.
* Degree `≥ 4` outside the twelve automata, the length-`12` first-degree-four pair in the
  "Limitation" of `comp:defect`, and alphabets other than three letters.
-/

namespace Psc.Degree3Catalogue

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants
  Psc.SignedCocycle Psc.ParikhRank Psc.Degree3Sector

/-! ### Seed paths in `B_σ`, checked by evaluation -/

section Chain

variable {α : Type*} [DecidableEq α]

/-- `chainTo s X [Y₁, …, Yₙ] T`: `X → Y₁ → ⋯ → Yₙ` is a path of `ChildNC s` (each
predecessor noncoincident, each successor a block of the reduction of its inflation) and
`Yₙ = T` (`X = T` when `n = 0`).  A `Bool`, so that a concrete path is checked by evaluation. -/
def chainTo (s : α → List α) :
    List α × List α → List (List α × List α) → List α × List α → Bool
  | X, [], T => decide (X = T)
  | X, Y :: ys, T =>
    (decide (X.1 ≠ X.2) && decide (Y ∈ red (subst s X.1) (subst s X.2))) && chainTo s Y ys T

/-- A checked path is a `ChildNC` path. -/
theorem chainTo_sound {s : α → List α} :
    ∀ {X : List α × List α} {ys : List (List α × List α)} {T : List α × List α},
      chainTo s X ys T = true → Relation.ReflTransGen (ChildNC s) X T
  | X, [], T, h => by
    have e : X = T := by simpa [chainTo] using h
    exact e ▸ .refl
  | X, Y :: ys, T, h => by
    simp only [chainTo, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .head ⟨h.1.1, h.1.2⟩ (chainTo_sound h.2)

/-- A checked path with at least one step is a `TransGen` path; with `T = X` it is a cycle
through `X`. -/
theorem transGen_of_chainTo {s : α → List α} {X Y T : List α × List α}
    {ys : List (List α × List α)} (h : chainTo s X (Y :: ys) T = true) :
    Relation.TransGen (ChildNC s) X T := by
  simp only [chainTo, Bool.and_eq_true, decide_eq_true_eq] at h
  exact .head' ⟨h.1.1, h.1.2⟩ (chainTo_sound h.2)

/-- **Reachability from a seed**: a checked path from the seed `(ab, ba)`, `a ≠ b`, ends in
a vertex of `B_σ`. -/
theorem mem_bpaStatesNC_of_chainTo [Fintype α] {s : α → List α} {a b : α} (hab : a ≠ b)
    {ys : List (List α × List α)} {T : List α × List α}
    (h : chainTo s ([a, b], [b, a]) ys T = true) : T ∈ bpaStatesNC s :=
  ⟨_, mem_seeds.2 ⟨a, b, hab, rfl⟩, chainTo_sound h⟩

/-- `B_σ` is swap-closed on noncoincident states (`bpaStates_swapClosed`,
`mem_bpaStatesNC_iff`). -/
theorem swap_mem_bpaStatesNC [Fintype α] {s : α → List α} {T : List α × List α}
    (hT : T ∈ bpaStatesNC s) (hne : T.1 ≠ T.2) : T.swap ∈ bpaStatesNC s :=
  (mem_bpaStatesNC_iff s (show T.swap.1 ≠ T.swap.2 from fun h => hne h.symm)).2
    (bpaStates_swapClosed s T ((mem_bpaStatesNC_iff s hne).1 hT))

/-- A child-closed set contains every descendant of each of its states. -/
theorem mem_of_mem_descR {s : α → List α} {D : Set (List α × List α)} (hD : ChildClosed s D) :
    ∀ (n : ℕ) {T U : List α × List α}, T ∈ D → U ∈ descR s n T → U ∈ D
  | 0, T, U, hT, hU => by
    rw [descR, List.mem_singleton] at hU
    exact hU ▸ hT
  | n + 1, T, U, hT, hU => by
    obtain ⟨V, hTV, hVU⟩ := (mem_descR_succ s).1 hU
    exact mem_of_mem_descR hD n (hD T hT V hTV) hVU

/-- **Leaking**: a state with a coincidence block among its depth-`n` descendants lies in no
child-closed, coincidence-free set (finite or not). -/
theorem not_mem_of_descR_coincidence {s : α → List α} {T U : List α × List α} {n : ℕ}
    (hU : U ∈ descR s n T) (hc : U.1 = U.2) {D : Set (List α × List α)}
    (hD : ChildClosed s D) (hfree : CoincidenceFree D) : T ∉ D :=
  fun hT => hfree U (mem_of_mem_descR hD n hT hU) hc

/-- A child is a depth-one descendant. -/
theorem mem_descR_one {s : α → List α} {T U : List α × List α} (h : Child s T U) :
    U ∈ descR s 1 T :=
  (mem_descR_succ s).2 ⟨U, h, List.mem_singleton_self U⟩

/-- A grandchild is a depth-two descendant. -/
theorem mem_descR_two {s : α → List α} {T U V : List α × List α} (h : Child s T U)
    (h' : Child s U V) : V ∈ descR s 2 T :=
  (mem_descR_succ s).2 ⟨U, h, mem_descR_one h'⟩

end Chain

/-! ### Spectral exclusion, generic in the substitution -/

section Spectral

/-- A coordinate certificate that `K₃(u, v)` is no eigenvector of `M^{⊗3}`: if
`K₃(u,v)(a,b,c) = 0` while `(M^{⊗3} K₃(u,v))(a,b,c) ≠ 0` (an integer computation), then
`M^{⊗3} K₃(u,v) ≠ c' K₃(u,v)` for every rational `c'`.  The substitution-independent form of
`Psc.Degree3Sector.phi3_ne_smul_of_coord`. -/
theorem phi3_ne_smul_of_coord_nat (M : Matrix (Fin 3) (Fin 3) ℕ) {u v : List (Fin 3)}
    {a b c : Fin 3} (h0 : Intertwiner3.K3 u v a b c = 0)
    (hsum : (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
      ((M a x : ℤ) * M b y * M c z) * Intertwiner3.K3 u v x y z) ≠ 0) (c' : ℚ) :
    Lie3.phi3 (M.map (Nat.cast : ℕ → ℚ)) (Lie3.k3Vec u v) ≠ c' • Lie3.k3Vec u v := by
  intro h
  have h1 := congrFun (congrFun (congrFun h a) b) c
  simp only [Lie3.phi3, Lie3.k3Vec, Pi.smul_apply, smul_eq_mul, h0, Int.cast_zero, mul_zero,
    Matrix.map_apply] at h1
  apply hsum
  exact_mod_cast h1

/-- The same certificate for the side swap `(v, u)` (`Psc.Intertwiner3.k3_swap`). -/
theorem phi3_ne_smul_of_coord_nat_swap (M : Matrix (Fin 3) (Fin 3) ℕ) {u v : List (Fin 3)}
    {a b c : Fin 3} (h0 : Intertwiner3.K3 u v a b c = 0)
    (hsum : (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
      ((M a x : ℤ) * M b y * M c z) * Intertwiner3.K3 u v x y z) ≠ 0) (c' : ℚ) :
    Lie3.phi3 (M.map (Nat.cast : ℕ → ℚ)) (Lie3.k3Vec v u) ≠ c' • Lie3.k3Vec v u := by
  refine phi3_ne_smul_of_coord_nat M (by rw [Intertwiner3.k3_swap u v, h0, neg_zero]) ?_ c'
  simpa only [Intertwiner3.k3_swap u v, mul_neg, Finset.sum_neg_distrib, neg_ne_zero] using hsum

/-- `K₃ ≠ 0` from one nonzero coordinate. -/
theorem k3Vec_ne_of_coord {u v : List (Fin 3)} {a b c : Fin 3}
    (h : Intertwiner3.K3 u v a b c ≠ 0) : Lie3.k3Vec u v ≠ 0 := by
  intro h'
  have h1 := congrFun (congrFun (congrFun h' a) b) c
  simp only [Lie3.k3Vec, Pi.zero_apply, Int.cast_eq_zero] at h1
  exact h h1

/-- `K₃ ≠ 0` is invariant under the side swap (`Psc.Intertwiner3.k3_swap`). -/
theorem k3Vec_swap_ne {u v : List (Fin 3)} (h : Lie3.k3Vec u v ≠ 0) : Lie3.k3Vec v u ≠ 0 := by
  intro h'
  apply h
  funext a b c
  have h1 := congrFun (congrFun (congrFun h' a) b) c
  simp only [Lie3.k3Vec, Pi.zero_apply] at h1 ⊢
  rw [Intertwiner3.k3_swap u v, Int.cast_neg, neg_eq_zero] at h1
  exact h1

/-- **The certificate of `χ = X³ - 2X² - 1`, reusable.**  Every rational `3 × 3` matrix with
this characteristic polynomial meets the matrix hypotheses of
`Psc.Degree3Sector.deg23_iii`: `χ` is irreducible and has a real root `b > 2` and two
further roots `α ≠ γ` of modulus `< 1`, pairwise distinct.  The certificates are those of
`censusSubst` (`census_irreducible`, `census_pisot`), transported along `χ_M = χ_{censusQ}`;
they depend only on the polynomial. -/
theorem cubic_certificate {M : Matrix (Fin 3) (Fin 3) ℚ}
    (hχ : M.charpoly = X ^ 3 - C 2 * X ^ 2 - 1) :
    Irreducible M.charpoly ∧ ∃ b : ℝ, 2 < b ∧ ∃ α γ : ℂ, aeval (b : ℂ) M.charpoly = 0 ∧
      aeval α M.charpoly = 0 ∧ aeval γ M.charpoly = 0 ∧ (b : ℂ) ≠ α ∧ (b : ℂ) ≠ γ ∧ α ≠ γ ∧
        ‖α‖ < 1 ∧ ‖γ‖ < 1 := by
  rw [hχ, ← census_charpoly]
  exact ⟨census_irreducible, census_pisot⟩

/-- `χ_M = X³ - 2X² - 1` and `det M = 1` for a natural `3 × 3` matrix, from three natural
identities (`tr M = 2`, `tr Λ²M = 0`, `det M = 1`, each cleared of subtraction), via
`Psc.Cyclicity.charpoly_fin_three`. -/
theorem charpoly_of_nat (M : Matrix (Fin 3) (Fin 3) ℕ) (htr : M 0 0 + M 1 1 + M 2 2 = 2)
    (hw : M 0 0 * M 1 1 + M 0 0 * M 2 2 + M 1 1 * M 2 2 =
      M 0 1 * M 1 0 + M 0 2 * M 2 0 + M 1 2 * M 2 1)
    (hdet : M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 =
      1 + (M 0 0 * M 1 2 * M 2 1 + M 0 1 * M 1 0 * M 2 2 + M 0 2 * M 1 1 * M 2 0)) :
    (M.map (Nat.cast : ℕ → ℚ)).charpoly = X ^ 3 - C 2 * X ^ 2 - 1 ∧
      (M.map (Nat.cast : ℕ → ℚ)).det = 1 := by
  have ht : (M.map (Nat.cast : ℕ → ℚ)).trace = 2 := by
    rw [trace_fin_three]; simp only [map_apply]; exact_mod_cast htr
  have hw' : (Psc.Cyclicity.wedge2 (M.map (Nat.cast : ℕ → ℚ))).trace = 0 := by
    have e := congrArg (Nat.cast : ℕ → ℚ) hw
    push_cast at e
    simp only [Psc.Cyclicity.wedge2, Psc.Cyclicity.pairFst, Psc.Cyclicity.pairSnd, Fin.isValue,
      of_apply, trace_fin_three, map_apply, cons_val_zero, cons_val_one, cons_val]
    linarith
  have hd : (M.map (Nat.cast : ℕ → ℚ)).det = 1 := by
    have e := congrArg (Nat.cast : ℕ → ℚ) hdet
    push_cast at e
    rw [det_fin_three]; simp only [map_apply]
    linarith
  refine ⟨?_, hd⟩
  rw [Psc.Cyclicity.charpoly_fin_three, ht, hw', hd]
  simp

/-- **Spectral exclusion, generic form.**  Let `S` be a child system with `∼₂` states and a
normalisation `P`, over a primitive `σ = S.s` with `χ_M = X³ - 2X² - 1`.  A pair `T` with a
coordinate certificate (`K₃(T)(a,b,c) = 0`, `(M^{⊗3} K₃(T))(a,b,c) ≠ 0`) is not a state of
`S`: by `Psc.Degree3Sector.deg23_iii_of_primitive`, step (c), the representative `T` or
`T.swap` (`Normalisation.cover`) would satisfy `M^{⊗3} K₃ = det M · K₃`. -/
theorem not_mem_of_coord (S : ChildSystem (Fin 3)) (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv2 T.1 T.2) (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c)
    (hχ : (incQ S).charpoly = X ^ 3 - C 2 * X ^ 2 - 1) {T : List (Fin 3) × List (Fin 3)}
    {a b c : Fin 3} (h0 : Intertwiner3.K3 T.1 T.2 a b c = 0)
    (hsum : (∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
      ((inc S.s a x : ℤ) * inc S.s b y * inc S.s c z) * Intertwiner3.K3 T.1 T.2 x y z) ≠ 0) :
    T ∉ S.C := by
  intro hT
  obtain ⟨hM, β, -, α, γ, hβ, hα, hγ, hβα, hβγ, hαγ, hα1, hγ1⟩ := cubic_certificate hχ
  have hle := (deg23_iii_of_primitive P hbal hprim hM hβ hα hγ hβα hβγ hαγ hα1 hγ1).2.2.2.1
  rcases P.cover _ hT with hR | hR
  · exact phi3_ne_smul_of_coord_nat (inc S.s) h0 hsum _
      (phi3_k3Vec_of_le_ker P hbal _ hle ⟨_, hR⟩)
  · exact phi3_ne_smul_of_coord_nat_swap (inc S.s) h0 hsum _
      (phi3_k3Vec_of_le_ker P hbal _ hle ⟨_, hR⟩)

end Spectral

/-! ### Relabelling equivariance -/

section Relabel

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Relabel both sides of a pair along `f`. -/
def relabel (f : α → β) (T : List α × List α) : List β × List β := (T.1.map f, T.2.map f)

omit [DecidableEq α] [DecidableEq β] in
theorem relabel_swap (f : α → β) (T : List α × List α) :
    relabel f T.swap = (relabel f T).swap := rfl

omit [DecidableEq α] [DecidableEq β] in
theorem relabel_relabel {γ : Type*} (f : α → β) (g : β → γ) (T : List α × List α) :
    relabel g (relabel f T) = relabel (g ∘ f) T := by
  simp [relabel, List.map_map]

omit [DecidableEq α] [DecidableEq β] in
/-- Inflation commutes with relabelling along a conjugacy `σ' ∘ f = map f ∘ σ`. -/
theorem subst_map {s : α → List α} {s' : β → List β} {f : α → β}
    (hc : ∀ a, s' (f a) = (s a).map f) (w : List α) : subst s' (w.map f) = (subst s w).map f := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [List.map_cons, subst_cons, subst_cons, ih, hc, List.map_append]

/-- The zero-return reduction commutes with an injective relabelling. -/
theorem redAux_map {f : α → β} (hf : f.Injective) :
    ∀ (pu pv u v : List α), redAux (pu.map f) (pv.map f) (u.map f) (v.map f) =
      (redAux pu pv u v).map (relabel f)
  | pu, pv, a :: u, b :: v => by
    rw [List.map_cons, List.map_cons, redAux_cons_cons, redAux_cons_cons]
    have e1 : pu.map f ++ [f a] = (pu ++ [a]).map f := by simp
    have e2 : pv.map f ++ [f b] = (pv ++ [b]).map f := by simp
    rw [e1, e2]
    by_cases h : (pu ++ [a]).Perm (pv ++ [b])
    · rw [ite_eq_left ((List.map_perm_map_iff hf).2 h), ite_eq_left h, List.map_cons]
      have ih := redAux_map hf [] [] u v
      simp only [List.map_nil] at ih
      rw [ih]
      rfl
    · rw [ite_eq_right (fun h' => h ((List.map_perm_map_iff hf).1 h')), ite_eq_right h]
      exact redAux_map hf _ _ u v
  | pu, pv, [], v => by
    rw [List.map_nil, redAux_of_nil _ _ (Or.inl rfl), redAux_of_nil _ _ (Or.inl rfl)]
    by_cases h : pu = [] ∧ pv = []
    · rw [ite_eq_left (by simp [h]), ite_eq_left h]; rfl
    · rw [ite_eq_right (by simpa using h), ite_eq_right h]; rfl
  | pu, pv, a :: u, [] => by
    rw [List.map_nil, redAux_of_nil _ _ (Or.inr rfl), redAux_of_nil _ _ (Or.inr rfl)]
    by_cases h : pu = [] ∧ pv = []
    · rw [ite_eq_left (by simp [h]), ite_eq_left h]; rfl
    · rw [ite_eq_right (by simpa using h), ite_eq_right h]; rfl

theorem red_map {f : α → β} (hf : f.Injective) (u v : List α) :
    red (u.map f) (v.map f) = (red u v).map (relabel f) :=
  redAux_map hf [] [] u v

/-- A relabelled child is a child of the relabelled state. -/
theorem child_map {s : α → List α} {s' : β → List β} {f : α → β} (hf : f.Injective)
    (hc : ∀ a, s' (f a) = (s a).map f) {T U : List α × List α} (h : Child s T U) :
    Child s' (relabel f T) (relabel f U) := by
  unfold Child at *
  rw [show (relabel f T).1 = T.1.map f from rfl, show (relabel f T).2 = T.2.map f from rfl,
    subst_map hc, subst_map hc, red_map hf]
  exact List.mem_map_of_mem h

/-- **`B_σ` is relabelling-equivariant**: along an injective `f` with
`σ' ∘ f = map f ∘ σ`, vertices of `B_σ` relabel to vertices of `B_σ'`. -/
theorem relabel_mem_bpaStatesNC [Fintype α] [Fintype β] {s : α → List α} {s' : β → List β}
    {f : α → β} (hf : f.Injective) (hc : ∀ a, s' (f a) = (s a).map f)
    {T : List α × List α} (hT : T ∈ bpaStatesNC s) : relabel f T ∈ bpaStatesNC s' := by
  obtain ⟨X, hX, hXT⟩ := hT
  obtain ⟨a, b, hab, rfl⟩ := mem_seeds.1 hX
  exact ⟨_, mem_seeds.2 ⟨f a, f b, hf.ne hab, rfl⟩,
    hXT.lift (relabel f) fun X Y h =>
      ⟨fun e => h.1 (List.map_injective_iff.2 hf e), child_map hf hc h.2⟩⟩

omit [DecidableEq β] in
theorem n2_map {f : α → β} (hf : f.Injective) [DecidableEq β] (w : List α) (a b : α) :
    n2 (w.map f) (f a) (f b) = n2 w a b := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [List.map_cons, n2, hf.eq_iff, List.count_map_of_injective _ _ hf, ih]

/-- `∼₂` is invariant under a bijective relabelling. -/
theorem equiv2_map {f : α → β} (hf : f.Bijective) {u v : List α} (h : Equiv2 u v) :
    Equiv2 (u.map f) (v.map f) := by
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · obtain ⟨a, rfl⟩ := hf.2 x
    rw [List.count_map_of_injective _ _ hf.1, List.count_map_of_injective _ _ hf.1]
    exact h.1 a
  · obtain ⟨a, rfl⟩ := hf.2 x
    obtain ⟨b, rfl⟩ := hf.2 y
    rw [n2_map hf.1, n2_map hf.1]
    exact h.2 a b

/-- `∼₂` is invariant under a relabelling by an equivalence, in both directions. -/
theorem equiv2_map_iff (e : α ≃ β) {u v : List α} :
    Equiv2 (u.map e) (v.map e) ↔ Equiv2 u v := by
  refine ⟨fun h => ?_, equiv2_map e.bijective⟩
  have h' := equiv2_map e.symm.bijective h
  simpa [List.map_map] using h'

omit [DecidableEq α] [DecidableEq β] in
theorem relabel_injective {f : α → β} (hf : f.Injective) : (relabel f).Injective := by
  intro T T' h
  simp only [relabel, Prod.mk.injEq] at h
  exact Prod.ext (List.map_injective_iff.2 hf h.1) (List.map_injective_iff.2 hf h.2)

/-- **`B_σ` is the relabelling of `B_τ`** along an equivalence `e` with `σ ∘ e = map e ∘ τ`
(both inclusions of `relabel_mem_bpaStatesNC`). -/
theorem bpaStatesNC_conj [Fintype α] [Fintype β] {s : α → List α} {s' : β → List β}
    (e : α ≃ β) (hc : ∀ a, s' (e a) = (s a).map e) :
    bpaStatesNC s' = relabel e '' bpaStatesNC s := by
  have hc' : ∀ b, s (e.symm b) = (s' b).map e.symm := by
    intro b
    conv_rhs => rw [← e.apply_symm_apply b, hc]
    simp [List.map_map]
  ext T
  constructor
  · intro hT
    exact ⟨relabel e.symm T, relabel_mem_bpaStatesNC e.symm.injective hc' hT, by
      simp [relabel, List.map_map]⟩
  · rintro ⟨T, hT, rfl⟩
    exact relabel_mem_bpaStatesNC e.injective hc hT

end Relabel

/-! ### Counting with `Set.ncard` -/

section Count

/-- Counting the members of a relabelled set that satisfy a relabelling-invariant
predicate. -/
theorem ncard_sep_image {X Y : Type*} {f : X → Y} (hf : f.Injective) (S : Set X)
    {p : Y → Prop} {q : X → Prop} (hpq : ∀ x, p (f x) ↔ q x) :
    {y ∈ f '' S | p y}.ncard = {x ∈ S | q x}.ncard := by
  have e : {y ∈ f '' S | p y} = f '' {x ∈ S | q x} := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hp⟩
      exact ⟨x, ⟨hx, (hpq x).1 hp⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hq⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (hpq x).2 hq⟩
  rw [e, Set.ncard_image_of_injective _ hf]

/-- A set listed without repetition by `F` has `F.length` members. -/
theorem ncard_of_list {X : Type*} [DecidableEq X] {F : List X} (hF : F.Nodup) {B : Set X}
    (hB : ∀ x, x ∈ B ↔ x ∈ F) : B.ncard = F.length := by
  have e : B = ↑F.toFinset := by
    ext x
    simp [hB]
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hF]

/-- The members of such a set satisfying `q` are counted by a filter of `F`. -/
theorem ncard_sep_of_list {X : Type*} [DecidableEq X] {F : List X} (hF : F.Nodup)
    {B : Set X} (hB : ∀ x, x ∈ B ↔ x ∈ F) (p : X → Bool) {q : X → Prop}
    (hpq : ∀ x, p x = true ↔ q x) : {x ∈ B | q x}.ncard = (F.filter p).length := by
  have e : {x ∈ B | q x} = ↑(F.filter p).toFinset := by
    ext x
    simp [hB, hpq]
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hF.filter p)]

end Count

/-! ### The catalogue -/

/-- A substitution on `{0,1,2}` by its three images `(σ 0, σ 1, σ 2)`. -/
abbrev Img := List (Fin 3) × List (Fin 3) × List (Fin 3)

/-- The substitution `0 ↦ σ.1`, `1 ↦ σ.2.1`, `2 ↦ σ.2.2`. -/
def toSubst (σ : Img) : Fin 3 → List (Fin 3) := ![σ.1, σ.2.1, σ.2.2]

/-- Its rational incidence matrix. -/
abbrev incOf (σ : Img) : Matrix (Fin 3) (Fin 3) ℚ := (inc (toSubst σ)).map (Nat.cast : ℕ → ℚ)

/-- The `39` candidate images of `kernel/psc/corpus.mojo` (`image_words`): every word of
length `1`, `2`, `3` over `{0,1,2}`, by length, then lexicographically. -/
def imageWords : List (List (Fin 3)) :=
  (List.finRange 3).map (fun a => [a]) ++
    ((List.finRange 3).flatMap fun a => (List.finRange 3).map fun b => [a, b]) ++
    ((List.finRange 3).flatMap fun a => (List.finRange 3).flatMap fun b =>
      (List.finRange 3).map fun c => [a, b, c])

/-- One occurrence of the catalogue, with its witnesses.  `idx = (i, j, k)` and the state
`T = (u, v)` are the fields `"i"`, `"j"`, `"k"`, `"state": "u|v"` of a `D3_STATE_JSON` line
of `kernel/degree3_catalog.mojo`, in its orientation; `img` is `σ = (w_i, w_j, w_k)`.  The
other fields are witnesses, re-checked by `Occ.Check`: `seed = (a, b)` and `path` are a
`ChildNC` path `(ab, ba) → ⋯ → T`; `nz` is a coordinate with `K₃(T) ≠ 0`; `wit` a
coordinate with `K₃(T) = 0` and `(M^{⊗3} K₃(T)) ≠ 0`; `ret` is a nonempty `ChildNC` path
`T → ⋯ → T` (re-checked by `catalogue_ret_check`). -/
structure Occ where
  idx : ℕ × ℕ × ℕ
  img : Img
  T : List (Fin 3) × List (Fin 3)
  seed : Fin 3 × Fin 3
  nz : Fin 3 × Fin 3 × Fin 3
  wit : Fin 3 × Fin 3 × Fin 3
  path : List (List (Fin 3) × List (Fin 3))
  ret : List (List (Fin 3) × List (Fin 3))

/-- **The 24 degree-three occurrences** (`comp:defect`; `docs/c4-defect-degree-census.md`
§2), in the order and orientation of `kernel/degree3_catalog.mojo`.  The witnesses (`seed`,
`path`, `nz`, `wit`) were found by an untrusted scratch search; `catalogue_check`
re-checks every one by evaluation. -/
def catalogue : List Occ := [
  { idx := (1, 17, 30), img := ([1], [0, 1, 2], [2, 0, 0]),
    T := ([0, 1, 2, 2, 0, 0, 0, 1, 2], [2, 0, 0, 1, 0, 1, 2, 2, 0]),
    seed := (0, 2), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([1, 2, 0, 0], [2, 0, 0, 1]),
      ([0, 1, 2, 2, 0, 0, 1, 1], [2, 0, 0, 1, 1, 0, 1, 2]),
      ([1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 0, 1, 2, 0, 1, 2],
       [2, 0, 0, 1, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0]),
      ([1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 2, 0, 0, 1, 1],
       [0, 1, 2, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0, 1, 0]),
      ([0, 1, 2], [2, 1, 0]),
      ([1, 0, 1, 2, 2, 0, 0], [2, 0, 0, 0, 1, 2, 1]),
      ([2, 2, 0, 0, 2, 0, 0, 1, 1], [0, 1, 2, 2, 0, 0, 0, 1, 2]),
      ([0, 1, 1, 0, 1, 2, 0, 1, 2], [1, 1, 1, 0, 1, 2, 2, 0, 0]),
      ([1, 2, 1, 0, 1, 2, 2, 0], [2, 0, 1, 2, 1, 0, 1, 2]),
      ([0, 1, 2, 2, 0, 0, 0, 1, 2], [2, 0, 0, 1, 0, 1, 2, 2, 0])],
    ret := [([1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 1, 0, 1, 2, 2, 0, 0],
             [2, 0, 0, 1, 1, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1]),
      ([0, 1, 2], [2, 1, 0]),
      ([1, 0, 1, 2, 2, 0, 0], [2, 0, 0, 0, 1, 2, 1]),
      ([2, 2, 0, 0, 2, 0, 0, 1, 1], [0, 1, 2, 2, 0, 0, 0, 1, 2]),
      ([0, 1, 1, 0, 1, 2, 0, 1, 2], [1, 1, 1, 0, 1, 2, 2, 0, 0]),
      ([1, 2, 1, 0, 1, 2, 2, 0], [2, 0, 1, 2, 1, 0, 1, 2]),
      ([0, 1, 2, 2, 0, 0, 0, 1, 2], [2, 0, 0, 1, 0, 1, 2, 2, 0])] },
  { idx := (1, 17, 30), img := ([1], [0, 1, 2], [2, 0, 0]),
    T := ([1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 1, 0, 1, 2, 2, 0, 0],
          [2, 0, 0, 1, 1, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1]),
    seed := (0, 2), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([1, 2, 0, 0], [2, 0, 0, 1]),
      ([0, 1, 2, 2, 0, 0, 1, 1], [2, 0, 0, 1, 1, 0, 1, 2]),
      ([1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 0, 1, 2, 0, 1, 2],
       [2, 0, 0, 1, 1, 0, 1, 2, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0]),
      ([1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 2, 0, 0, 1, 1],
       [0, 1, 2, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0, 1, 0]),
      ([0, 1, 2], [2, 1, 0]),
      ([1, 0, 1, 2, 2, 0, 0], [2, 0, 0, 0, 1, 2, 1]),
      ([2, 2, 0, 0, 2, 0, 0, 1, 1], [0, 1, 2, 2, 0, 0, 0, 1, 2]),
      ([0, 1, 1, 0, 1, 2, 0, 1, 2], [1, 1, 1, 0, 1, 2, 2, 0, 0]),
      ([1, 2, 1, 0, 1, 2, 2, 0], [2, 0, 1, 2, 1, 0, 1, 2]),
      ([0, 1, 2, 2, 0, 0, 0, 1, 2], [2, 0, 0, 1, 0, 1, 2, 2, 0]),
      ([1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 1, 0, 1, 2, 2, 0, 0],
       [2, 0, 0, 1, 1, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1])],
    ret := [([0, 1, 2], [2, 1, 0]),
      ([1, 0, 1, 2, 2, 0, 0], [2, 0, 0, 0, 1, 2, 1]),
      ([2, 2, 0, 0, 2, 0, 0, 1, 1], [0, 1, 2, 2, 0, 0, 0, 1, 2]),
      ([0, 1, 1, 0, 1, 2, 0, 1, 2], [1, 1, 1, 0, 1, 2, 2, 0, 0]),
      ([1, 2, 1, 0, 1, 2, 2, 0], [2, 0, 1, 2, 1, 0, 1, 2]),
      ([0, 1, 2, 2, 0, 0, 0, 1, 2], [2, 0, 0, 1, 0, 1, 2, 2, 0]),
      ([1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1, 1, 1, 0, 1, 2, 2, 0, 0],
       [2, 0, 0, 1, 1, 0, 1, 2, 1, 0, 1, 2, 2, 0, 0, 2, 0, 0, 1])] },
  { idx := (1, 33, 14), img := ([1], [2, 1, 0], [0, 0, 2]),
    T := ([0, 2, 2, 1, 0, 1, 0, 0, 2], [2, 1, 0, 0, 0, 2, 2, 1, 0]),
    seed := (0, 2), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([1, 0, 0, 2], [0, 0, 2, 1]),
      ([2, 1, 0, 1, 1, 0, 0, 2], [1, 1, 0, 0, 2, 2, 1, 0]),
      ([0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 2, 1, 0, 1, 1, 0, 0, 2],
       [2, 1, 0, 2, 1, 0, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1]),
      ([0, 1, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 2, 1, 0],
       [1, 1, 0, 0, 2, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1]),
      ([0, 1, 2], [2, 1, 0]),
      ([1, 2, 1, 0, 0, 0, 2], [0, 0, 2, 2, 1, 0, 1]),
      ([2, 1, 0, 0, 0, 2, 2, 1, 0], [1, 1, 0, 0, 2, 0, 0, 2, 2]),
      ([0, 0, 2, 2, 1, 0, 1, 1, 1], [2, 1, 0, 2, 1, 0, 1, 1, 0]),
      ([2, 1, 0, 1, 2, 1, 0, 2], [0, 2, 2, 1, 0, 1, 2, 1]),
      ([0, 2, 2, 1, 0, 1, 0, 0, 2], [2, 1, 0, 0, 0, 2, 2, 1, 0])],
    ret := [([1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 1, 1, 0, 0, 2],
             [0, 0, 2, 2, 1, 0, 1, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1]),
      ([0, 1, 2], [2, 1, 0]),
      ([1, 2, 1, 0, 0, 0, 2], [0, 0, 2, 2, 1, 0, 1]),
      ([2, 1, 0, 0, 0, 2, 2, 1, 0], [1, 1, 0, 0, 2, 0, 0, 2, 2]),
      ([0, 0, 2, 2, 1, 0, 1, 1, 1], [2, 1, 0, 2, 1, 0, 1, 1, 0]),
      ([2, 1, 0, 1, 2, 1, 0, 2], [0, 2, 2, 1, 0, 1, 2, 1]),
      ([0, 2, 2, 1, 0, 1, 0, 0, 2], [2, 1, 0, 0, 0, 2, 2, 1, 0])] },
  { idx := (1, 33, 14), img := ([1], [2, 1, 0], [0, 0, 2]),
    T := ([0, 0, 2, 2, 1, 0, 1, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1],
          [1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 1, 1, 0, 0, 2]),
    seed := (1, 2), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([2, 1, 0, 0, 0, 2], [0, 0, 2, 2, 1, 0]),
      ([0, 0, 2, 2, 1, 0, 1, 1, 1, 0, 0, 2], [1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1]),
      ([1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 2, 1, 0, 2, 1, 0],
       [2, 1, 0, 2, 1, 0, 1, 1, 0, 0, 2, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1]),
      ([2, 1, 0, 2, 1, 0, 1, 1, 0, 0, 2, 1, 1, 0, 0, 2, 0, 0, 2, 2],
       [0, 0, 2, 2, 1, 0, 1, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 2, 1, 0]),
      ([2, 1, 0], [0, 1, 2]),
      ([0, 0, 2, 2, 1, 0, 1], [1, 2, 1, 0, 0, 0, 2]),
      ([1, 1, 0, 0, 2, 0, 0, 2, 2], [2, 1, 0, 0, 0, 2, 2, 1, 0]),
      ([2, 1, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 2, 1, 0, 1, 1, 1]),
      ([0, 2, 2, 1, 0, 1, 2, 1], [2, 1, 0, 1, 2, 1, 0, 2]),
      ([2, 1, 0, 0, 0, 2, 2, 1, 0], [0, 2, 2, 1, 0, 1, 0, 0, 2]),
      ([0, 0, 2, 2, 1, 0, 1, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1],
       [1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 1, 1, 0, 0, 2])],
    ret := [([2, 1, 0], [0, 1, 2]),
      ([0, 0, 2, 2, 1, 0, 1], [1, 2, 1, 0, 0, 0, 2]),
      ([1, 1, 0, 0, 2, 0, 0, 2, 2], [2, 1, 0, 0, 0, 2, 2, 1, 0]),
      ([2, 1, 0, 2, 1, 0, 1, 1, 0], [0, 0, 2, 2, 1, 0, 1, 1, 1]),
      ([0, 2, 2, 1, 0, 1, 2, 1], [2, 1, 0, 1, 2, 1, 0, 2]),
      ([2, 1, 0, 0, 0, 2, 2, 1, 0], [0, 2, 2, 1, 0, 1, 0, 0, 2]),
      ([0, 0, 2, 2, 1, 0, 1, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1],
       [1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 1, 1, 0, 0, 2])] },
  { idx := (2, 13, 27), img := ([2], [0, 0, 1], [1, 2, 0]),
    T := ([0, 1, 1, 2, 0, 2, 0, 0, 1], [1, 2, 0, 0, 0, 1, 1, 2, 0]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([2, 0, 0, 1], [0, 0, 1, 2]),
      ([1, 2, 0, 2, 2, 0, 0, 1], [2, 2, 0, 0, 1, 1, 2, 0]),
      ([0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 1, 2, 0, 2, 2, 0, 0, 1],
       [1, 2, 0, 1, 2, 0, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2]),
      ([0, 2, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 1, 2, 0],
       [2, 2, 0, 0, 1, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2]),
      ([0, 2, 1], [1, 2, 0]),
      ([2, 1, 2, 0, 0, 0, 1], [0, 0, 1, 1, 2, 0, 2]),
      ([1, 2, 0, 0, 0, 1, 1, 2, 0], [2, 2, 0, 0, 1, 0, 0, 1, 1]),
      ([0, 0, 1, 1, 2, 0, 2, 2, 2], [1, 2, 0, 1, 2, 0, 2, 2, 0]),
      ([1, 2, 0, 2, 1, 2, 0, 1], [0, 1, 1, 2, 0, 2, 1, 2]),
      ([0, 1, 1, 2, 0, 2, 0, 0, 1], [1, 2, 0, 0, 0, 1, 1, 2, 0])],
    ret := [([2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 2, 2, 0, 0, 1],
             [0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2]),
      ([0, 2, 1], [1, 2, 0]),
      ([2, 1, 2, 0, 0, 0, 1], [0, 0, 1, 1, 2, 0, 2]),
      ([1, 2, 0, 0, 0, 1, 1, 2, 0], [2, 2, 0, 0, 1, 0, 0, 1, 1]),
      ([0, 0, 1, 1, 2, 0, 2, 2, 2], [1, 2, 0, 1, 2, 0, 2, 2, 0]),
      ([1, 2, 0, 2, 1, 2, 0, 1], [0, 1, 1, 2, 0, 2, 1, 2]),
      ([0, 1, 1, 2, 0, 2, 0, 0, 1], [1, 2, 0, 0, 0, 1, 1, 2, 0])] },
  { idx := (2, 13, 27), img := ([2], [0, 0, 1], [1, 2, 0]),
    T := ([0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2],
          [2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 2, 2, 0, 0, 1]),
    seed := (1, 0), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([0, 0, 1, 2], [2, 0, 0, 1]),
      ([2, 2, 0, 0, 1, 1, 2, 0], [1, 2, 0, 2, 2, 0, 0, 1]),
      ([1, 2, 0, 1, 2, 0, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2],
       [0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 1, 2, 0, 2, 2, 0, 0, 1]),
      ([2, 2, 0, 0, 1, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2],
       [0, 2, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 1, 2, 0]),
      ([1, 2, 0], [0, 2, 1]),
      ([0, 0, 1, 1, 2, 0, 2], [2, 1, 2, 0, 0, 0, 1]),
      ([2, 2, 0, 0, 1, 0, 0, 1, 1], [1, 2, 0, 0, 0, 1, 1, 2, 0]),
      ([1, 2, 0, 1, 2, 0, 2, 2, 0], [0, 0, 1, 1, 2, 0, 2, 2, 2]),
      ([0, 1, 1, 2, 0, 2, 1, 2], [1, 2, 0, 2, 1, 2, 0, 1]),
      ([1, 2, 0, 0, 0, 1, 1, 2, 0], [0, 1, 1, 2, 0, 2, 0, 0, 1]),
      ([0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2],
       [2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 2, 2, 0, 0, 1])],
    ret := [([1, 2, 0], [0, 2, 1]),
      ([0, 0, 1, 1, 2, 0, 2], [2, 1, 2, 0, 0, 0, 1]),
      ([2, 2, 0, 0, 1, 0, 0, 1, 1], [1, 2, 0, 0, 0, 1, 1, 2, 0]),
      ([1, 2, 0, 1, 2, 0, 2, 2, 0], [0, 0, 1, 1, 2, 0, 2, 2, 2]),
      ([0, 1, 1, 2, 0, 2, 1, 2], [1, 2, 0, 2, 1, 2, 0, 1]),
      ([1, 2, 0, 0, 0, 1, 1, 2, 0], [0, 1, 1, 2, 0, 2, 0, 0, 1]),
      ([0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2],
       [2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 2, 2, 0, 0, 1])] },
  { idx := (2, 21, 19), img := ([2], [1, 0, 0], [0, 2, 1]),
    T := ([0, 2, 1, 1, 0, 0, 0, 2, 1], [1, 0, 0, 2, 0, 2, 1, 1, 0]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([2, 1, 0, 0], [1, 0, 0, 2]),
      ([0, 2, 1, 1, 0, 0, 2, 2], [1, 0, 0, 2, 2, 0, 2, 1]),
      ([2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 0, 2, 1, 0, 2, 1],
       [1, 0, 0, 2, 2, 0, 2, 1, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0]),
      ([2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 2, 2],
       [0, 2, 1, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0, 2, 0]),
      ([0, 2, 1], [1, 2, 0]),
      ([2, 0, 2, 1, 1, 0, 0], [1, 0, 0, 0, 2, 1, 2]),
      ([1, 1, 0, 0, 1, 0, 0, 2, 2], [0, 2, 1, 1, 0, 0, 0, 2, 1]),
      ([0, 2, 2, 0, 2, 1, 0, 2, 1], [2, 2, 2, 0, 2, 1, 1, 0, 0]),
      ([2, 1, 2, 0, 2, 1, 1, 0], [1, 0, 2, 1, 2, 0, 2, 1]),
      ([0, 2, 1, 1, 0, 0, 0, 2, 1], [1, 0, 0, 2, 0, 2, 1, 1, 0])],
    ret := [([2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 0, 2, 1, 1, 0, 0],
             [1, 0, 0, 2, 2, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2]),
      ([0, 2, 1], [1, 2, 0]),
      ([2, 0, 2, 1, 1, 0, 0], [1, 0, 0, 0, 2, 1, 2]),
      ([1, 1, 0, 0, 1, 0, 0, 2, 2], [0, 2, 1, 1, 0, 0, 0, 2, 1]),
      ([0, 2, 2, 0, 2, 1, 0, 2, 1], [2, 2, 2, 0, 2, 1, 1, 0, 0]),
      ([2, 1, 2, 0, 2, 1, 1, 0], [1, 0, 2, 1, 2, 0, 2, 1]),
      ([0, 2, 1, 1, 0, 0, 0, 2, 1], [1, 0, 0, 2, 0, 2, 1, 1, 0])] },
  { idx := (2, 21, 19), img := ([2], [1, 0, 0], [0, 2, 1]),
    T := ([1, 0, 0, 2, 2, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2],
          [2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 0, 2, 1, 1, 0, 0]),
    seed := (1, 0), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([1, 0, 0, 2], [2, 1, 0, 0]),
      ([1, 0, 0, 2, 2, 0, 2, 1], [0, 2, 1, 1, 0, 0, 2, 2]),
      ([1, 0, 0, 2, 2, 0, 2, 1, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0],
       [2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 0, 2, 1, 0, 2, 1]),
      ([0, 2, 1, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0, 2, 0],
       [2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 1, 0, 0, 2, 2]),
      ([1, 2, 0], [0, 2, 1]),
      ([1, 0, 0, 0, 2, 1, 2], [2, 0, 2, 1, 1, 0, 0]),
      ([0, 2, 1, 1, 0, 0, 0, 2, 1], [1, 1, 0, 0, 1, 0, 0, 2, 2]),
      ([2, 2, 2, 0, 2, 1, 1, 0, 0], [0, 2, 2, 0, 2, 1, 0, 2, 1]),
      ([1, 0, 2, 1, 2, 0, 2, 1], [2, 1, 2, 0, 2, 1, 1, 0]),
      ([1, 0, 0, 2, 0, 2, 1, 1, 0], [0, 2, 1, 1, 0, 0, 0, 2, 1]),
      ([1, 0, 0, 2, 2, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2],
       [2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 0, 2, 1, 1, 0, 0])],
    ret := [([1, 2, 0], [0, 2, 1]),
      ([1, 0, 0, 0, 2, 1, 2], [2, 0, 2, 1, 1, 0, 0]),
      ([0, 2, 1, 1, 0, 0, 0, 2, 1], [1, 1, 0, 0, 1, 0, 0, 2, 2]),
      ([2, 2, 2, 0, 2, 1, 1, 0, 0], [0, 2, 2, 0, 2, 1, 0, 2, 1]),
      ([1, 0, 2, 1, 2, 0, 2, 1], [2, 1, 2, 0, 2, 1, 1, 0]),
      ([1, 0, 0, 2, 0, 2, 1, 1, 0], [0, 2, 1, 1, 0, 0, 0, 2, 1]),
      ([1, 0, 0, 2, 2, 0, 2, 1, 2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2],
       [2, 0, 2, 1, 1, 0, 0, 1, 0, 0, 2, 2, 2, 0, 2, 1, 1, 0, 0])] },
  { idx := (16, 2, 27), img := ([0, 1, 1], [2], [1, 2, 0]),
    T := ([0, 1, 1, 2, 1, 2, 0, 0, 1], [1, 2, 0, 0, 1, 1, 1, 2, 0]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([0, 1, 1, 2], [2, 0, 1, 1]),
      ([0, 1, 1, 2, 2, 1, 2, 0], [1, 2, 0, 0, 1, 1, 2, 2]),
      ([0, 1, 1, 2, 2, 1, 2, 0, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1],
       [2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 1, 2, 0, 1, 2, 0]),
      ([1, 2, 0, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1, 2, 1],
       [2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2]),
      ([0, 2, 1], [1, 2, 0]),
      ([0, 1, 1, 1, 2, 0, 2], [2, 1, 2, 0, 0, 1, 1]),
      ([1, 2, 0, 0, 1, 1, 1, 2, 0], [0, 0, 1, 1, 0, 1, 1, 2, 2]),
      ([2, 2, 2, 1, 2, 0, 0, 1, 1], [1, 2, 2, 1, 2, 0, 1, 2, 0]),
      ([0, 1, 2, 0, 2, 1, 2, 0], [2, 0, 2, 1, 2, 0, 0, 1]),
      ([0, 1, 1, 2, 1, 2, 0, 0, 1], [1, 2, 0, 0, 1, 1, 1, 2, 0])],
    ret := [([0, 1, 1, 2, 2, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2],
             [2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 1, 2, 0, 0, 1, 1]),
      ([0, 2, 1], [1, 2, 0]),
      ([0, 1, 1, 1, 2, 0, 2], [2, 1, 2, 0, 0, 1, 1]),
      ([1, 2, 0, 0, 1, 1, 1, 2, 0], [0, 0, 1, 1, 0, 1, 1, 2, 2]),
      ([2, 2, 2, 1, 2, 0, 0, 1, 1], [1, 2, 2, 1, 2, 0, 1, 2, 0]),
      ([0, 1, 2, 0, 2, 1, 2, 0], [2, 0, 2, 1, 2, 0, 0, 1]),
      ([0, 1, 1, 2, 1, 2, 0, 0, 1], [1, 2, 0, 0, 1, 1, 1, 2, 0])] },
  { idx := (16, 2, 27), img := ([0, 1, 1], [2], [1, 2, 0]),
    T := ([0, 1, 1, 2, 2, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2],
          [2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 1, 2, 0, 0, 1, 1]),
    seed := (0, 1), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([0, 1, 1, 2], [2, 0, 1, 1]),
      ([0, 1, 1, 2, 2, 1, 2, 0], [1, 2, 0, 0, 1, 1, 2, 2]),
      ([0, 1, 1, 2, 2, 1, 2, 0, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1],
       [2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 1, 2, 0, 1, 2, 0]),
      ([1, 2, 0, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1, 2, 1],
       [2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 0, 1, 1, 2, 2]),
      ([0, 2, 1], [1, 2, 0]),
      ([0, 1, 1, 1, 2, 0, 2], [2, 1, 2, 0, 0, 1, 1]),
      ([1, 2, 0, 0, 1, 1, 1, 2, 0], [0, 0, 1, 1, 0, 1, 1, 2, 2]),
      ([2, 2, 2, 1, 2, 0, 0, 1, 1], [1, 2, 2, 1, 2, 0, 1, 2, 0]),
      ([0, 1, 2, 0, 2, 1, 2, 0], [2, 0, 2, 1, 2, 0, 0, 1]),
      ([0, 1, 1, 2, 1, 2, 0, 0, 1], [1, 2, 0, 0, 1, 1, 1, 2, 0]),
      ([0, 1, 1, 2, 2, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2],
       [2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 1, 2, 0, 0, 1, 1])],
    ret := [([0, 2, 1], [1, 2, 0]),
      ([0, 1, 1, 1, 2, 0, 2], [2, 1, 2, 0, 0, 1, 1]),
      ([1, 2, 0, 0, 1, 1, 1, 2, 0], [0, 0, 1, 1, 0, 1, 1, 2, 2]),
      ([2, 2, 2, 1, 2, 0, 0, 1, 1], [1, 2, 2, 1, 2, 0, 1, 2, 0]),
      ([0, 1, 2, 0, 2, 1, 2, 0], [2, 0, 2, 1, 2, 0, 0, 1]),
      ([0, 1, 1, 2, 1, 2, 0, 0, 1], [1, 2, 0, 0, 1, 1, 1, 2, 0]),
      ([0, 1, 1, 2, 2, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2],
       [2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 1, 2, 0, 0, 1, 1])] },
  { idx := (20, 33, 1), img := ([0, 2, 2], [2, 1, 0], [1]),
    T := ([0, 2, 2, 1, 2, 1, 0, 0, 2], [2, 1, 0, 0, 2, 2, 2, 1, 0]),
    seed := (0, 1), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([0, 2, 2, 2, 1, 0], [2, 1, 0, 0, 2, 2]),
      ([0, 2, 2, 1, 1, 1, 2, 1, 0, 0, 2, 2], [1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1]),
      ([2, 1, 0, 2, 1, 0, 2, 1, 0, 1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1],
       [1, 0, 0, 2, 2, 0, 2, 2, 1, 1, 0, 2, 2, 1, 1, 2, 1, 0, 2, 1, 0]),
      ([1, 0, 0, 2, 2, 1, 2, 1, 0, 0, 2, 2, 1, 2], [0, 0, 2, 2, 0, 2, 2, 1, 1, 0, 2, 2, 1, 1]),
      ([0, 1, 2], [2, 1, 0]),
      ([0, 2, 2, 2, 1, 0, 1], [1, 2, 1, 0, 0, 2, 2]),
      ([2, 1, 0, 0, 2, 2, 2, 1, 0], [0, 0, 2, 2, 0, 2, 2, 1, 1]),
      ([1, 1, 1, 2, 1, 0, 0, 2, 2], [2, 1, 1, 2, 1, 0, 2, 1, 0]),
      ([0, 2, 1, 0, 1, 2, 1, 0], [1, 0, 1, 2, 1, 0, 0, 2]),
      ([0, 2, 2, 1, 2, 1, 0, 0, 2], [2, 1, 0, 0, 2, 2, 2, 1, 0])],
    ret := [([0, 2, 2, 1, 1, 2, 1, 0, 1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1],
             [1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1, 1, 2, 1, 0, 0, 2, 2]),
      ([0, 1, 2], [2, 1, 0]),
      ([0, 2, 2, 2, 1, 0, 1], [1, 2, 1, 0, 0, 2, 2]),
      ([2, 1, 0, 0, 2, 2, 2, 1, 0], [0, 0, 2, 2, 0, 2, 2, 1, 1]),
      ([1, 1, 1, 2, 1, 0, 0, 2, 2], [2, 1, 1, 2, 1, 0, 2, 1, 0]),
      ([0, 2, 1, 0, 1, 2, 1, 0], [1, 0, 1, 2, 1, 0, 0, 2]),
      ([0, 2, 2, 1, 2, 1, 0, 0, 2], [2, 1, 0, 0, 2, 2, 2, 1, 0])] },
  { idx := (20, 33, 1), img := ([0, 2, 2], [2, 1, 0], [1]),
    T := ([0, 2, 2, 1, 1, 2, 1, 0, 1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1],
          [1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1, 1, 2, 1, 0, 0, 2, 2]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([0, 2, 2, 2, 1, 0], [2, 1, 0, 0, 2, 2]),
      ([0, 2, 2, 1, 1, 1, 2, 1, 0, 0, 2, 2], [1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1]),
      ([2, 1, 0, 2, 1, 0, 2, 1, 0, 1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1],
       [1, 0, 0, 2, 2, 0, 2, 2, 1, 1, 0, 2, 2, 1, 1, 2, 1, 0, 2, 1, 0]),
      ([1, 0, 0, 2, 2, 1, 2, 1, 0, 0, 2, 2, 1, 2], [0, 0, 2, 2, 0, 2, 2, 1, 1, 0, 2, 2, 1, 1]),
      ([0, 1, 2], [2, 1, 0]),
      ([0, 2, 2, 2, 1, 0, 1], [1, 2, 1, 0, 0, 2, 2]),
      ([2, 1, 0, 0, 2, 2, 2, 1, 0], [0, 0, 2, 2, 0, 2, 2, 1, 1]),
      ([1, 1, 1, 2, 1, 0, 0, 2, 2], [2, 1, 1, 2, 1, 0, 2, 1, 0]),
      ([0, 2, 1, 0, 1, 2, 1, 0], [1, 0, 1, 2, 1, 0, 0, 2]),
      ([0, 2, 2, 1, 2, 1, 0, 0, 2], [2, 1, 0, 0, 2, 2, 2, 1, 0]),
      ([0, 2, 2, 1, 1, 2, 1, 0, 1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1],
       [1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1, 1, 2, 1, 0, 0, 2, 2])],
    ret := [([0, 1, 2], [2, 1, 0]),
      ([0, 2, 2, 2, 1, 0, 1], [1, 2, 1, 0, 0, 2, 2]),
      ([2, 1, 0, 0, 2, 2, 2, 1, 0], [0, 0, 2, 2, 0, 2, 2, 1, 1]),
      ([1, 1, 1, 2, 1, 0, 0, 2, 2], [2, 1, 1, 2, 1, 0, 2, 1, 0]),
      ([0, 2, 1, 0, 1, 2, 1, 0], [1, 0, 1, 2, 1, 0, 0, 2]),
      ([0, 2, 2, 1, 2, 1, 0, 0, 2], [2, 1, 0, 0, 2, 2, 2, 1, 0]),
      ([0, 2, 2, 1, 1, 2, 1, 0, 1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1],
       [1, 2, 1, 0, 0, 2, 2, 0, 2, 2, 1, 1, 1, 2, 1, 0, 0, 2, 2])] },
  { idx := (23, 0, 34), img := ([1, 0, 2], [0], [2, 1, 1]),
    T := ([1, 0, 2, 2, 1, 1, 1, 0, 2], [2, 1, 1, 0, 1, 0, 2, 2, 1]),
    seed := (0, 2), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([1, 0, 2, 2, 1, 1], [2, 1, 1, 1, 0, 2]),
      ([0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0], [2, 1, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1]),
      ([0, 2, 2, 1, 1, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0, 1, 0, 2, 1, 0, 2],
       [1, 0, 2, 1, 0, 2, 1, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0]),
      ([2, 2, 1, 1, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0], [0, 2, 2, 1, 1, 0, 1, 0, 2, 2, 1, 1, 0, 1]),
      ([1, 0, 2], [2, 0, 1]),
      ([0, 1, 0, 2, 2, 1, 1], [2, 1, 1, 1, 0, 2, 0]),
      ([2, 2, 1, 1, 2, 1, 1, 0, 0], [1, 0, 2, 2, 1, 1, 1, 0, 2]),
      ([1, 0, 0, 1, 0, 2, 1, 0, 2], [0, 0, 0, 1, 0, 2, 2, 1, 1]),
      ([0, 2, 0, 1, 0, 2, 2, 1], [2, 1, 0, 2, 0, 1, 0, 2]),
      ([1, 0, 2, 2, 1, 1, 1, 0, 2], [2, 1, 1, 0, 1, 0, 2, 2, 1])],
    ret := [([0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1],
             [2, 1, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0]),
      ([1, 0, 2], [2, 0, 1]),
      ([0, 1, 0, 2, 2, 1, 1], [2, 1, 1, 1, 0, 2, 0]),
      ([2, 2, 1, 1, 2, 1, 1, 0, 0], [1, 0, 2, 2, 1, 1, 1, 0, 2]),
      ([1, 0, 0, 1, 0, 2, 1, 0, 2], [0, 0, 0, 1, 0, 2, 2, 1, 1]),
      ([0, 2, 0, 1, 0, 2, 2, 1], [2, 1, 0, 2, 0, 1, 0, 2]),
      ([1, 0, 2, 2, 1, 1, 1, 0, 2], [2, 1, 1, 0, 1, 0, 2, 2, 1])] },
  { idx := (23, 0, 34), img := ([1, 0, 2], [0], [2, 1, 1]),
    T := ([0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1],
          [2, 1, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0]),
    seed := (0, 2), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([1, 0, 2, 2, 1, 1], [2, 1, 1, 1, 0, 2]),
      ([0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0], [2, 1, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1]),
      ([0, 2, 2, 1, 1, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0, 1, 0, 2, 1, 0, 2],
       [1, 0, 2, 1, 0, 2, 1, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0]),
      ([2, 2, 1, 1, 2, 1, 1, 0, 0, 2, 1, 1, 0, 0], [0, 2, 2, 1, 1, 0, 1, 0, 2, 2, 1, 1, 0, 1]),
      ([1, 0, 2], [2, 0, 1]),
      ([0, 1, 0, 2, 2, 1, 1], [2, 1, 1, 1, 0, 2, 0]),
      ([2, 2, 1, 1, 2, 1, 1, 0, 0], [1, 0, 2, 2, 1, 1, 1, 0, 2]),
      ([1, 0, 0, 1, 0, 2, 1, 0, 2], [0, 0, 0, 1, 0, 2, 2, 1, 1]),
      ([0, 2, 0, 1, 0, 2, 2, 1], [2, 1, 0, 2, 0, 1, 0, 2]),
      ([1, 0, 2, 2, 1, 1, 1, 0, 2], [2, 1, 1, 0, 1, 0, 2, 2, 1]),
      ([0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1],
       [2, 1, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0])],
    ret := [([1, 0, 2], [2, 0, 1]),
      ([0, 1, 0, 2, 2, 1, 1], [2, 1, 1, 1, 0, 2, 0]),
      ([2, 2, 1, 1, 2, 1, 1, 0, 0], [1, 0, 2, 2, 1, 1, 1, 0, 2]),
      ([1, 0, 0, 1, 0, 2, 1, 0, 2], [0, 0, 0, 1, 0, 2, 2, 1, 1]),
      ([0, 2, 0, 1, 0, 2, 2, 1], [2, 1, 0, 2, 0, 1, 0, 2]),
      ([1, 0, 2, 2, 1, 1, 1, 0, 2], [2, 1, 1, 0, 1, 0, 2, 2, 1]),
      ([0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1],
       [2, 1, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0])] },
  { idx := (23, 37, 0), img := ([1, 0, 2], [2, 2, 1], [0]),
    T := ([1, 0, 2, 2, 2, 1, 1, 0, 2], [2, 1, 1, 0, 2, 0, 2, 2, 1]),
    seed := (0, 1), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([1, 0, 2, 2, 2, 1], [2, 2, 1, 1, 0, 2]),
      ([2, 2, 1, 1, 0, 2, 0, 0, 0, 2, 2, 1], [0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0]),
      ([0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 1, 0, 2],
       [1, 0, 2, 1, 0, 2, 0, 0, 2, 2, 1, 0, 0, 2, 2, 1, 2, 2, 1, 1, 0]),
      ([1, 0, 2, 1, 0, 2, 0, 0, 2, 2, 1, 0, 0, 2, 2, 1, 2, 2, 1, 1],
       [2, 2, 1, 1, 0, 2, 0, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2]),
      ([1, 0, 2], [2, 0, 1]),
      ([2, 2, 1, 1, 0, 2, 0], [0, 1, 0, 2, 2, 2, 1]),
      ([0, 0, 2, 2, 1, 2, 2, 1, 1], [1, 0, 2, 2, 2, 1, 1, 0, 2]),
      ([1, 0, 2, 1, 0, 2, 0, 0, 2], [2, 2, 1, 1, 0, 2, 0, 0, 0]),
      ([2, 1, 1, 0, 2, 0, 1, 0], [1, 0, 2, 0, 1, 0, 2, 1]),
      ([1, 0, 2, 2, 2, 1, 1, 0, 2], [2, 1, 1, 0, 2, 0, 2, 2, 1])],
    ret := [([2, 2, 1, 1, 0, 2, 0, 0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0],
             [0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 2, 1]),
      ([1, 0, 2], [2, 0, 1]),
      ([2, 2, 1, 1, 0, 2, 0], [0, 1, 0, 2, 2, 2, 1]),
      ([0, 0, 2, 2, 1, 2, 2, 1, 1], [1, 0, 2, 2, 2, 1, 1, 0, 2]),
      ([1, 0, 2, 1, 0, 2, 0, 0, 2], [2, 2, 1, 1, 0, 2, 0, 0, 0]),
      ([2, 1, 1, 0, 2, 0, 1, 0], [1, 0, 2, 0, 1, 0, 2, 1]),
      ([1, 0, 2, 2, 2, 1, 1, 0, 2], [2, 1, 1, 0, 2, 0, 2, 2, 1])] },
  { idx := (23, 37, 0), img := ([1, 0, 2], [2, 2, 1], [0]),
    T := ([0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 2, 1],
          [2, 2, 1, 1, 0, 2, 0, 0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([1, 0, 2, 2, 2, 1], [2, 2, 1, 1, 0, 2]),
      ([2, 2, 1, 1, 0, 2, 0, 0, 0, 2, 2, 1], [0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0]),
      ([0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 1, 0, 2],
       [1, 0, 2, 1, 0, 2, 0, 0, 2, 2, 1, 0, 0, 2, 2, 1, 2, 2, 1, 1, 0]),
      ([2, 0, 2, 2, 1, 1, 0, 2, 0, 2, 2, 1, 1, 0], [0, 0, 2, 2, 1, 0, 0, 2, 2, 1, 2, 2, 1, 1]),
      ([2, 0, 1], [1, 0, 2]),
      ([0, 1, 0, 2, 2, 2, 1], [2, 2, 1, 1, 0, 2, 0]),
      ([1, 0, 2, 2, 2, 1, 1, 0, 2], [0, 0, 2, 2, 1, 2, 2, 1, 1]),
      ([2, 2, 1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 2, 0, 0, 2]),
      ([1, 0, 2, 0, 1, 0, 2, 1], [2, 1, 1, 0, 2, 0, 1, 0]),
      ([2, 1, 1, 0, 2, 0, 2, 2, 1], [1, 0, 2, 2, 2, 1, 1, 0, 2]),
      ([0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 2, 1],
       [2, 2, 1, 1, 0, 2, 0, 0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0])],
    ret := [([2, 0, 1], [1, 0, 2]),
      ([0, 1, 0, 2, 2, 2, 1], [2, 2, 1, 1, 0, 2, 0]),
      ([1, 0, 2, 2, 2, 1, 1, 0, 2], [0, 0, 2, 2, 1, 2, 2, 1, 1]),
      ([2, 2, 1, 1, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0, 2, 0, 0, 2]),
      ([1, 0, 2, 0, 1, 0, 2, 1], [2, 1, 1, 0, 2, 0, 1, 0]),
      ([2, 1, 1, 0, 2, 0, 2, 2, 1], [1, 0, 2, 2, 2, 1, 1, 0, 2]),
      ([0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2, 2, 1],
       [2, 2, 1, 1, 0, 2, 0, 0, 0, 2, 2, 1, 2, 2, 1, 1, 0, 2, 0])] },
  { idx := (24, 2, 19), img := ([1, 1, 0], [2], [0, 2, 1]),
    T := ([0, 2, 1, 1, 1, 0, 0, 2, 1], [1, 0, 0, 2, 1, 2, 1, 1, 0]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([1, 1, 0, 2], [2, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 0, 2, 1], [0, 2, 1, 2, 2, 1, 1, 0]),
      ([0, 2, 1, 0, 2, 1, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2],
       [1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 0, 2, 1, 2, 2, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2],
       [1, 2, 1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 0, 2, 1]),
      ([0, 2, 1], [1, 2, 0]),
      ([1, 1, 0, 0, 2, 1, 2], [2, 0, 2, 1, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 1, 1, 0, 0], [0, 2, 1, 1, 1, 0, 0, 2, 1]),
      ([0, 2, 1, 0, 2, 1, 2, 2, 1], [1, 1, 0, 0, 2, 1, 2, 2, 2]),
      ([1, 0, 0, 2, 1, 2, 0, 2], [0, 2, 1, 2, 0, 2, 1, 0]),
      ([0, 2, 1, 1, 1, 0, 0, 2, 1], [1, 0, 0, 2, 1, 2, 1, 1, 0])],
    ret := [([1, 1, 0, 0, 2, 1, 2, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2],
             [2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 2, 2, 1, 1, 0]),
      ([0, 2, 1], [1, 2, 0]),
      ([1, 1, 0, 0, 2, 1, 2], [2, 0, 2, 1, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 1, 1, 0, 0], [0, 2, 1, 1, 1, 0, 0, 2, 1]),
      ([0, 2, 1, 0, 2, 1, 2, 2, 1], [1, 1, 0, 0, 2, 1, 2, 2, 2]),
      ([1, 0, 0, 2, 1, 2, 0, 2], [0, 2, 1, 2, 0, 2, 1, 0]),
      ([0, 2, 1, 1, 1, 0, 0, 2, 1], [1, 0, 0, 2, 1, 2, 1, 1, 0])] },
  { idx := (24, 2, 19), img := ([1, 1, 0], [2], [0, 2, 1]),
    T := ([1, 1, 0, 0, 2, 1, 2, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2],
          [2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 2, 2, 1, 1, 0]),
    seed := (0, 1), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([1, 1, 0, 2], [2, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 0, 2, 1], [0, 2, 1, 2, 2, 1, 1, 0]),
      ([0, 2, 1, 0, 2, 1, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2],
       [1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 0, 2, 1, 2, 2, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2],
       [1, 2, 1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 0, 2, 1]),
      ([0, 2, 1], [1, 2, 0]),
      ([1, 1, 0, 0, 2, 1, 2], [2, 0, 2, 1, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 1, 1, 0, 0], [0, 2, 1, 1, 1, 0, 0, 2, 1]),
      ([0, 2, 1, 0, 2, 1, 2, 2, 1], [1, 1, 0, 0, 2, 1, 2, 2, 2]),
      ([1, 0, 0, 2, 1, 2, 0, 2], [0, 2, 1, 2, 0, 2, 1, 0]),
      ([0, 2, 1, 1, 1, 0, 0, 2, 1], [1, 0, 0, 2, 1, 2, 1, 1, 0]),
      ([1, 1, 0, 0, 2, 1, 2, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2],
       [2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 2, 2, 1, 1, 0])],
    ret := [([0, 2, 1], [1, 2, 0]),
      ([1, 1, 0, 0, 2, 1, 2], [2, 0, 2, 1, 1, 1, 0]),
      ([2, 2, 1, 1, 0, 1, 1, 0, 0], [0, 2, 1, 1, 1, 0, 0, 2, 1]),
      ([0, 2, 1, 0, 2, 1, 2, 2, 1], [1, 1, 0, 0, 2, 1, 2, 2, 2]),
      ([1, 0, 0, 2, 1, 2, 0, 2], [0, 2, 1, 2, 0, 2, 1, 0]),
      ([0, 2, 1, 1, 1, 0, 0, 2, 1], [1, 0, 0, 2, 1, 2, 1, 1, 0]),
      ([1, 1, 0, 0, 2, 1, 2, 2, 2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2],
       [2, 1, 1, 0, 1, 1, 0, 0, 2, 1, 2, 0, 2, 1, 2, 2, 1, 1, 0])] },
  { idx := (31, 0, 26), img := ([2, 0, 1], [0], [1, 1, 2]),
    T := ([1, 2, 2, 0, 1, 0, 1, 1, 2], [2, 0, 1, 1, 1, 2, 2, 0, 1]),
    seed := (0, 2), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([2, 0, 1, 1, 1, 2], [1, 1, 2, 2, 0, 1]),
      ([1, 1, 2, 2, 0, 1, 0, 0, 0, 1, 1, 2], [0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0]),
      ([0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 2, 0, 1],
       [2, 0, 1, 2, 0, 1, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 1, 1, 2, 2, 0]),
      ([1, 0, 1, 1, 2, 2, 0, 1, 0, 1, 1, 2, 2, 0], [0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 1, 1, 2, 2]),
      ([1, 0, 2], [2, 0, 1]),
      ([0, 2, 0, 1, 1, 1, 2], [1, 1, 2, 2, 0, 1, 0]),
      ([2, 0, 1, 1, 1, 2, 2, 0, 1], [0, 0, 1, 1, 2, 1, 1, 2, 2]),
      ([1, 1, 2, 2, 0, 1, 0, 0, 0], [2, 0, 1, 2, 0, 1, 0, 0, 1]),
      ([2, 0, 1, 0, 2, 0, 1, 2], [1, 2, 2, 0, 1, 0, 2, 0]),
      ([1, 2, 2, 0, 1, 0, 1, 1, 2], [2, 0, 1, 1, 1, 2, 2, 0, 1])],
    ret := [([0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 0, 0, 1, 1, 2],
             [1, 1, 2, 2, 0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0]),
      ([1, 0, 2], [2, 0, 1]),
      ([0, 2, 0, 1, 1, 1, 2], [1, 1, 2, 2, 0, 1, 0]),
      ([2, 0, 1, 1, 1, 2, 2, 0, 1], [0, 0, 1, 1, 2, 1, 1, 2, 2]),
      ([1, 1, 2, 2, 0, 1, 0, 0, 0], [2, 0, 1, 2, 0, 1, 0, 0, 1]),
      ([2, 0, 1, 0, 2, 0, 1, 2], [1, 2, 2, 0, 1, 0, 2, 0]),
      ([1, 2, 2, 0, 1, 0, 1, 1, 2], [2, 0, 1, 1, 1, 2, 2, 0, 1])] },
  { idx := (31, 0, 26), img := ([2, 0, 1], [0], [1, 1, 2]),
    T := ([0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 0, 0, 1, 1, 2],
          [1, 1, 2, 2, 0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0]),
    seed := (0, 2), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([2, 0, 1, 1, 1, 2], [1, 1, 2, 2, 0, 1]),
      ([1, 1, 2, 2, 0, 1, 0, 0, 0, 1, 1, 2], [0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0]),
      ([0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 2, 0, 1, 2, 0, 1],
       [2, 0, 1, 2, 0, 1, 0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 1, 1, 2, 2, 0]),
      ([1, 0, 1, 1, 2, 2, 0, 1, 0, 1, 1, 2, 2, 0], [0, 0, 1, 1, 2, 0, 0, 1, 1, 2, 1, 1, 2, 2]),
      ([1, 0, 2], [2, 0, 1]),
      ([0, 2, 0, 1, 1, 1, 2], [1, 1, 2, 2, 0, 1, 0]),
      ([2, 0, 1, 1, 1, 2, 2, 0, 1], [0, 0, 1, 1, 2, 1, 1, 2, 2]),
      ([1, 1, 2, 2, 0, 1, 0, 0, 0], [2, 0, 1, 2, 0, 1, 0, 0, 1]),
      ([2, 0, 1, 0, 2, 0, 1, 2], [1, 2, 2, 0, 1, 0, 2, 0]),
      ([1, 2, 2, 0, 1, 0, 1, 1, 2], [2, 0, 1, 1, 1, 2, 2, 0, 1]),
      ([0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 0, 0, 1, 1, 2],
       [1, 1, 2, 2, 0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0])],
    ret := [([1, 0, 2], [2, 0, 1]),
      ([0, 2, 0, 1, 1, 1, 2], [1, 1, 2, 2, 0, 1, 0]),
      ([2, 0, 1, 1, 1, 2, 2, 0, 1], [0, 0, 1, 1, 2, 1, 1, 2, 2]),
      ([1, 1, 2, 2, 0, 1, 0, 0, 0], [2, 0, 1, 2, 0, 1, 0, 0, 1]),
      ([2, 0, 1, 0, 2, 0, 1, 2], [1, 2, 2, 0, 1, 0, 2, 0]),
      ([1, 2, 2, 0, 1, 0, 1, 1, 2], [2, 0, 1, 1, 1, 2, 2, 0, 1]),
      ([0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 0, 0, 1, 1, 2],
       [1, 1, 2, 2, 0, 1, 0, 0, 0, 1, 1, 2, 1, 1, 2, 2, 0, 1, 0])] },
  { idx := (31, 29, 0), img := ([2, 0, 1], [1, 2, 2], [0]),
    T := ([1, 2, 2, 0, 2, 0, 1, 1, 2], [2, 0, 1, 1, 2, 2, 2, 0, 1]),
    seed := (0, 1), nz := (0, 0, 1), wit := (1, 1, 2),
    path := [([2, 0, 1, 1, 2, 2], [1, 2, 2, 2, 0, 1]),
      ([0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0], [1, 2, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2]),
      ([0, 1, 1, 2, 2, 1, 2, 2, 0, 0, 1, 2, 2, 0, 0, 2, 0, 1, 2, 0, 1],
       [2, 0, 1, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0]),
      ([2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 1, 2, 2, 0, 2, 0, 1, 1, 2, 2],
       [1, 1, 2, 2, 1, 2, 2, 0, 0, 1, 2, 2, 0, 0, 2, 0, 1, 2, 0, 1]),
      ([1, 0, 2], [2, 0, 1]),
      ([1, 2, 2, 2, 0, 1, 0], [0, 2, 0, 1, 1, 2, 2]),
      ([2, 0, 1, 1, 2, 2, 2, 0, 1], [1, 1, 2, 2, 1, 2, 2, 0, 0]),
      ([0, 0, 0, 2, 0, 1, 1, 2, 2], [2, 0, 0, 2, 0, 1, 2, 0, 1]),
      ([1, 2, 0, 1, 0, 2, 0, 1], [0, 1, 0, 2, 0, 1, 1, 2]),
      ([1, 2, 2, 0, 2, 0, 1, 1, 2], [2, 0, 1, 1, 2, 2, 2, 0, 1])],
    ret := [([1, 2, 2, 0, 0, 2, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0],
             [0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2]),
      ([1, 0, 2], [2, 0, 1]),
      ([1, 2, 2, 2, 0, 1, 0], [0, 2, 0, 1, 1, 2, 2]),
      ([2, 0, 1, 1, 2, 2, 2, 0, 1], [1, 1, 2, 2, 1, 2, 2, 0, 0]),
      ([0, 0, 0, 2, 0, 1, 1, 2, 2], [2, 0, 0, 2, 0, 1, 2, 0, 1]),
      ([1, 2, 0, 1, 0, 2, 0, 1], [0, 1, 0, 2, 0, 1, 1, 2]),
      ([1, 2, 2, 0, 2, 0, 1, 1, 2], [2, 0, 1, 1, 2, 2, 2, 0, 1])] },
  { idx := (31, 29, 0), img := ([2, 0, 1], [1, 2, 2], [0]),
    T := ([0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2],
          [1, 2, 2, 0, 0, 2, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([2, 0, 1, 1, 2, 2], [1, 2, 2, 2, 0, 1]),
      ([0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0], [1, 2, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2]),
      ([0, 1, 1, 2, 2, 1, 2, 2, 0, 0, 1, 2, 2, 0, 0, 2, 0, 1, 2, 0, 1],
       [2, 0, 1, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0]),
      ([1, 1, 2, 2, 1, 2, 2, 0, 0, 1, 2, 2, 0, 0], [0, 1, 1, 2, 2, 0, 2, 0, 1, 1, 2, 2, 0, 2]),
      ([2, 0, 1], [1, 0, 2]),
      ([0, 2, 0, 1, 1, 2, 2], [1, 2, 2, 2, 0, 1, 0]),
      ([1, 1, 2, 2, 1, 2, 2, 0, 0], [2, 0, 1, 1, 2, 2, 2, 0, 1]),
      ([2, 0, 0, 2, 0, 1, 2, 0, 1], [0, 0, 0, 2, 0, 1, 1, 2, 2]),
      ([0, 1, 0, 2, 0, 1, 1, 2], [1, 2, 0, 1, 0, 2, 0, 1]),
      ([2, 0, 1, 1, 2, 2, 2, 0, 1], [1, 2, 2, 0, 2, 0, 1, 1, 2]),
      ([0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2],
       [1, 2, 2, 0, 0, 2, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0])],
    ret := [([2, 0, 1], [1, 0, 2]),
      ([0, 2, 0, 1, 1, 2, 2], [1, 2, 2, 2, 0, 1, 0]),
      ([1, 1, 2, 2, 1, 2, 2, 0, 0], [2, 0, 1, 1, 2, 2, 2, 0, 1]),
      ([2, 0, 0, 2, 0, 1, 2, 0, 1], [0, 0, 0, 2, 0, 1, 1, 2, 2]),
      ([0, 1, 0, 2, 0, 1, 1, 2], [1, 2, 0, 1, 0, 2, 0, 1]),
      ([2, 0, 1, 1, 2, 2, 2, 0, 1], [1, 2, 2, 0, 2, 0, 1, 1, 2]),
      ([0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0, 0, 0, 2, 0, 1, 1, 2, 2],
       [1, 2, 2, 0, 0, 2, 0, 1, 0, 2, 0, 1, 1, 2, 2, 1, 2, 2, 0])] },
  { idx := (36, 17, 1), img := ([2, 2, 0], [0, 1, 2], [1]),
    T := ([0, 1, 2, 2, 2, 0, 0, 1, 2], [2, 0, 0, 1, 2, 1, 2, 2, 0]),
    seed := (0, 1), nz := (0, 0, 1), wit := (0, 0, 2),
    path := [([2, 2, 0, 0, 1, 2], [0, 1, 2, 2, 2, 0]),
      ([1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1], [2, 2, 0, 0, 1, 2, 1, 1, 1, 2, 2, 0]),
      ([0, 1, 2, 0, 1, 2, 1, 1, 2, 2, 0, 1, 1, 2, 2, 0, 2, 2, 0, 0, 1],
       [1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2]),
      ([1, 1, 2, 2, 0, 1, 1, 2, 2, 0, 2, 2, 0, 0], [2, 1, 2, 2, 0, 0, 1, 2, 1, 2, 2, 0, 0, 1]),
      ([0, 1, 2], [2, 1, 0]),
      ([2, 2, 0, 0, 1, 2, 1], [1, 0, 1, 2, 2, 2, 0]),
      ([1, 1, 2, 2, 0, 2, 2, 0, 0], [0, 1, 2, 2, 2, 0, 0, 1, 2]),
      ([0, 1, 2, 0, 1, 2, 1, 1, 2], [2, 2, 0, 0, 1, 2, 1, 1, 1]),
      ([2, 0, 0, 1, 2, 1, 0, 1], [0, 1, 2, 1, 0, 1, 2, 0]),
      ([0, 1, 2, 2, 2, 0, 0, 1, 2], [2, 0, 0, 1, 2, 1, 2, 2, 0])],
    ret := [([2, 2, 0, 0, 1, 2, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1],
             [1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1, 0, 1, 2, 1, 1, 2, 2, 0]),
      ([0, 1, 2], [2, 1, 0]),
      ([2, 2, 0, 0, 1, 2, 1], [1, 0, 1, 2, 2, 2, 0]),
      ([1, 1, 2, 2, 0, 2, 2, 0, 0], [0, 1, 2, 2, 2, 0, 0, 1, 2]),
      ([0, 1, 2, 0, 1, 2, 1, 1, 2], [2, 2, 0, 0, 1, 2, 1, 1, 1]),
      ([2, 0, 0, 1, 2, 1, 0, 1], [0, 1, 2, 1, 0, 1, 2, 0]),
      ([0, 1, 2, 2, 2, 0, 0, 1, 2], [2, 0, 0, 1, 2, 1, 2, 2, 0])] },
  { idx := (36, 17, 1), img := ([2, 2, 0], [0, 1, 2], [1]),
    T := ([1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1, 0, 1, 2, 1, 1, 2, 2, 0],
          [2, 2, 0, 0, 1, 2, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1]),
    seed := (0, 1), nz := (0, 0, 2), wit := (0, 0, 1),
    path := [([2, 2, 0, 0, 1, 2], [0, 1, 2, 2, 2, 0]),
      ([1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1], [2, 2, 0, 0, 1, 2, 1, 1, 1, 2, 2, 0]),
      ([0, 1, 2, 0, 1, 2, 1, 1, 2, 2, 0, 1, 1, 2, 2, 0, 2, 2, 0, 0, 1],
       [1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2]),
      ([2, 2, 0, 0, 1, 2, 1, 2, 2, 0, 0, 1, 2, 1, 0, 1, 2, 0, 1, 2],
       [0, 1, 2, 0, 1, 2, 1, 1, 2, 2, 0, 1, 1, 2, 2, 0, 2, 2, 0, 0]),
      ([2, 1, 0], [0, 1, 2]),
      ([1, 0, 1, 2, 2, 2, 0], [2, 2, 0, 0, 1, 2, 1]),
      ([0, 1, 2, 2, 2, 0, 0, 1, 2], [1, 1, 2, 2, 0, 2, 2, 0, 0]),
      ([2, 2, 0, 0, 1, 2, 1, 1, 1], [0, 1, 2, 0, 1, 2, 1, 1, 2]),
      ([0, 1, 2, 1, 0, 1, 2, 0], [2, 0, 0, 1, 2, 1, 0, 1]),
      ([2, 0, 0, 1, 2, 1, 2, 2, 0], [0, 1, 2, 2, 2, 0, 0, 1, 2]),
      ([1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1, 0, 1, 2, 1, 1, 2, 2, 0],
       [2, 2, 0, 0, 1, 2, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1])],
    ret := [([2, 1, 0], [0, 1, 2]),
      ([1, 0, 1, 2, 2, 2, 0], [2, 2, 0, 0, 1, 2, 1]),
      ([0, 1, 2, 2, 2, 0, 0, 1, 2], [1, 1, 2, 2, 0, 2, 2, 0, 0]),
      ([2, 2, 0, 0, 1, 2, 1, 1, 1], [0, 1, 2, 0, 1, 2, 1, 1, 2]),
      ([0, 1, 2, 1, 0, 1, 2, 0], [2, 0, 0, 1, 2, 1, 0, 1]),
      ([2, 0, 0, 1, 2, 1, 2, 2, 0], [0, 1, 2, 2, 2, 0, 0, 1, 2]),
      ([1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1, 0, 1, 2, 1, 1, 2, 2, 0],
       [2, 2, 0, 0, 1, 2, 1, 1, 1, 2, 2, 0, 2, 2, 0, 0, 1, 2, 1])] }]

/-- The `(σ, T)` pairs of the catalogue. -/
def occurrences : List (Img × (List (Fin 3) × List (Fin 3))) :=
  catalogue.map fun o => (o.img, o.T)

/-- `(M^{⊗3} K₃(u, v))(a, b, c)` over `ℤ`, for a natural `M`. -/
def phi3Coord (M : Matrix (Fin 3) (Fin 3) ℕ) (u v : List (Fin 3)) (a b c : Fin 3) : ℤ :=
  ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3, ((M a x : ℤ) * M b y * M c z) * Intertwiner3.K3 u v x y z

/-- The decidable facts checked for one occurrence. -/
def Occ.Check (o : Occ) : Prop :=
  -- the Mojo image indices decode to the images
  imageWords[o.idx.1]? = some o.img.1 ∧ imageWords[o.idx.2.1]? = some o.img.2.1 ∧
    imageWords[o.idx.2.2]? = some o.img.2.2 ∧
  -- primitivity (`M² > 0`) and the three identities of `charpoly_of_nat`
  (∀ a c : Fin 3, 0 < ∑ b : Fin 3, inc (toSubst o.img) a b * inc (toSubst o.img) b c) ∧
  (let M := inc (toSubst o.img)
   M 0 0 + M 1 1 + M 2 2 = 2 ∧
   M 0 0 * M 1 1 + M 0 0 * M 2 2 + M 1 1 * M 2 2 = M 0 1 * M 1 0 + M 0 2 * M 2 0 + M 1 2 * M 2 1 ∧
   M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 + M 0 2 * M 1 0 * M 2 1 =
      1 + (M 0 0 * M 1 2 * M 2 1 + M 0 1 * M 1 0 * M 2 2 + M 0 2 * M 1 1 * M 2 0)) ∧
  -- reachability
  o.seed.1 ≠ o.seed.2 ∧
  chainTo (toSubst o.img) ([o.seed.1, o.seed.2], [o.seed.2, o.seed.1]) o.path o.T = true ∧
  -- `∼₂`, `K₃ ≠ 0`, and the coordinate certificate
  Equiv2 o.T.1 o.T.2 ∧
  Intertwiner3.K3 o.T.1 o.T.2 o.nz.1 o.nz.2.1 o.nz.2.2 ≠ 0 ∧
  Intertwiner3.K3 o.T.1 o.T.2 o.wit.1 o.wit.2.1 o.wit.2.2 = 0 ∧
  phi3Coord (inc (toSubst o.img)) o.T.1 o.T.2 o.wit.1 o.wit.2.1 o.wit.2.2 ≠ 0 ∧
  -- the leak pattern
  ((o.T.1.length = 9 ∧
      (red (subst (toSubst o.img) o.T.1) (subst (toSubst o.img) o.T.2)).length = 1 ∧
      ∀ U ∈ red (subst (toSubst o.img) o.T.1) (subst (toSubst o.img) o.T.2),
        U.1.length = 19 ∧ ∃ o' ∈ catalogue, o'.img = o.img ∧ o'.T.1.length = 19 ∧
          (o'.T = U ∨ o'.T = U.swap)) ∨
    (o.T.1.length = 19 ∧
      (red (subst (toSubst o.img) o.T.1) (subst (toSubst o.img) o.T.2)).length = 5 ∧
      (red (subst (toSubst o.img) o.T.1) (subst (toSubst o.img) o.T.2)).Nodup ∧
      (red (subst (toSubst o.img) o.T.1) (subst (toSubst o.img) o.T.2)).countP
        (fun U => decide (U.1 = U.2)) = 1))

instance (o : Occ) : Decidable o.Check := by unfold Occ.Check; infer_instance

theorem catalogue_check : ∀ o ∈ catalogue, o.Check := by decide +kernel

/-- The return paths, checked by a separate kernel evaluation: each `ret` is a nonempty
`ChildNC` path from `T` back to `T`. -/
theorem catalogue_ret_check : ∀ o ∈ catalogue,
    o.ret ≠ [] ∧ chainTo (toSubst o.img) o.T o.ret o.T = true := by
  decide +kernel

/-! ### What the catalogue establishes -/

/-- **The contract for one occurrence `(σ, T)`**: items (a)–(e) of the module docstring. -/
structure OccSpec (σ : Img) (T : List (Fin 3) × List (Fin 3)) : Prop where
  /-- (a) `T` and its side swap are vertices of `B_σ` (reached from a seed `(ab, ba)` by a
  checked `ChildNC` path). -/
  reachable : T ∈ bpaStatesNC (toSubst σ) ∧ T.swap ∈ bpaStatesNC (toSubst σ)
  /-- (a) `T` is recurrent: it lies on a cycle of `B_σ` (a checked return path). -/
  recurrent : Relation.TransGen (ChildNC (toSubst σ)) T T
  noncoincident : T.1 ≠ T.2
  /-- (b) `K₁ = K₂ = 0` and `K₃ ≠ 0`: first defect degree three. -/
  equiv2 : Equiv2 T.1 T.2
  k3_ne : Lie3.k3Vec T.1 T.2 ≠ 0
  /-- (c) The leak pattern: a length-`9` state has exactly one child, a length-`19` state of
  the catalogue over the same `σ` (up to side swap); a length-`19` state has exactly five
  pairwise distinct children, exactly one of them a coincidence block. -/
  leak : (T.1.length = 9 ∧ ∃ U, red (subst (toSubst σ) T.1) (subst (toSubst σ) T.2) = [U] ∧
      U.1.length = 19 ∧ ((σ, U) ∈ occurrences ∨ (σ, U.swap) ∈ occurrences)) ∨
    (T.1.length = 19 ∧ (red (subst (toSubst σ) T.1) (subst (toSubst σ) T.2)).length = 5 ∧
      (red (subst (toSubst σ) T.1) (subst (toSubst σ) T.2)).Nodup ∧
      (red (subst (toSubst σ) T.1) (subst (toSubst σ) T.2)).countP
        (fun U => decide (U.1 = U.2)) = 1)
  /-- (d) A coincidence block within two inflations ... -/
  leak_two : ∃ n, 1 ≤ n ∧ n ≤ 2 ∧
    ∃ U ∈ red ((subst (toSubst σ))^[n] T.1) ((subst (toSubst σ))^[n] T.2), U.1 = U.2
  /-- ... so no child-closed, coincidence-free set (finite or not) contains `T`. -/
  not_closed : ∀ D : Set (List (Fin 3) × List (Fin 3)), ChildClosed (toSubst σ) D →
    CoincidenceFree D → T ∉ D
  /-- (e) The substitution: primitive, `χ_M = X³ - 2X² - 1`, `det M = 1`. -/
  primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc (toSubst σ) ^ k) a c
  charpoly : (incOf σ).charpoly = X ^ 3 - C 2 * X ^ 2 - 1
  det : (incOf σ).det = 1
  /-- `K₃(T)` is no eigenvector of `M^{⊗3}`; in particular `M^{⊗3} K₃(T) ≠ det M · K₃(T)`. -/
  phi3_ne : ∀ c : ℚ, Lie3.phi3 (incOf σ) (Lie3.k3Vec T.1 T.2) ≠ c • Lie3.k3Vec T.1 T.2
  /-- Spectral exclusion: `T` is a state of no `∼₂` child system over `σ` that has a
  normalisation (`thm:deg23` (iii), via `not_mem_of_coord`). -/
  not_mem : ∀ S : ChildSystem (Fin 3), S.s = toSubst σ → ∀ _ : Normalisation S,
    (∀ T' ∈ S.C, Equiv2 T'.1 T'.2) → T ∉ S.C

/-- A depth-`n` descendant (`n ≥ 1`) of a balanced pair is a block of the reduction of its
`n`-fold inflation (`Psc.Descendants.descR_succ`). -/
theorem mem_red_iterate_of_descR {s : Fin 3 → List (Fin 3)} {T U : List (Fin 3) × List (Fin 3)}
    {n : ℕ} (hn : 1 ≤ n) (h : Equiv1 T.1 T.2) (hU : U ∈ descR s n T) :
    U ∈ red ((subst s)^[n] T.1) ((subst s)^[n] T.2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rwa [← descR_succ s m h]

/-- A length-`19` occurrence has a coincidence child. -/
theorem exists_coincidence_child {o : Occ} (ho : o ∈ catalogue) (h19 : o.T.1.length = 19) :
    ∃ V, Child (toSubst o.img) o.T V ∧ V.1 = V.2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hleak⟩ := catalogue_check o ho
  rcases hleak with ⟨h9, -⟩ | ⟨-, -, -, hc⟩
  · omega
  · obtain ⟨V, hV, hVc⟩ := List.countP_pos_iff.1 (by rw [hc]; exact Nat.one_pos)
    exact ⟨V, hV, of_decide_eq_true hVc⟩

/-- **The main theorem: every catalogue occurrence satisfies its contract** `OccSpec`. -/
theorem catalogue_spec : ∀ o ∈ catalogue, OccSpec o.img o.T := by
  intro o ho
  obtain ⟨-, -, -, hprim, ⟨htr, hw, hdet⟩, hab, hpath, h2, hnz, hw0, hphi, hleak⟩ :=
    catalogue_check o ho
  have hnc : o.T.1 ≠ o.T.2 := fun h => hnz (by rw [Intertwiner3.K3, h, sub_self])
  have hreach := mem_bpaStatesNC_of_chainTo hab hpath
  have hrec : Relation.TransGen (ChildNC (toSubst o.img)) o.T o.T := by
    obtain ⟨hne, hret⟩ := catalogue_ret_check o ho
    obtain ⟨Y, ys, hY⟩ := List.exists_cons_of_ne_nil hne
    rw [hY] at hret
    exact transGen_of_chainTo hret
  have hprim' : ∃ k ≥ 1, ∀ a c, 0 < (inc (toSubst o.img) ^ k) a c :=
    ⟨2, by norm_num, fun a c => by rw [pow_two, mul_apply]; exact hprim a c⟩
  obtain ⟨hχ, hd⟩ := charpoly_of_nat (inc (toSubst o.img)) htr hw hdet
  -- a coincidence block among the depth-one or depth-two descendants
  have hdesc : ∃ n, 1 ≤ n ∧ n ≤ 2 ∧ ∃ U ∈ descR (toSubst o.img) n o.T, U.1 = U.2 := by
    rcases hleak with ⟨h9, hl, hall⟩ | ⟨h19, -, -, -⟩
    · obtain ⟨U, hU⟩ := List.length_eq_one_iff.1 hl
      have hUmem : U ∈ red (subst (toSubst o.img) o.T.1) (subst (toSubst o.img) o.T.2) := by
        rw [hU]; exact List.mem_singleton_self U
      obtain ⟨-, o', ho', himg, h19', hT'⟩ := hall U hUmem
      obtain ⟨V, hV, hVc⟩ := exists_coincidence_child ho' h19'
      rw [himg] at hV
      rcases hT' with hT' | hT'
      · rw [hT'] at hV
        exact ⟨2, by norm_num, le_rfl, V, mem_descR_two hUmem hV, hVc⟩
      · rw [hT'] at hV
        have hV' := child_swap hV
        rw [Prod.swap_swap] at hV'
        exact ⟨2, by norm_num, le_rfl, V.swap, mem_descR_two hUmem hV', hVc.symm⟩
    · obtain ⟨V, hV, hVc⟩ := exists_coincidence_child ho h19
      exact ⟨1, le_rfl, by norm_num, V, mem_descR_one hV, hVc⟩
  refine ⟨⟨hreach, swap_mem_bpaStatesNC hreach hnc⟩, hrec, hnc, h2, k3Vec_ne_of_coord hnz, ?_, ?_,
    ?_,
    hprim', hχ, hd, phi3_ne_smul_of_coord_nat _ hw0 hphi, ?_⟩
  · rcases hleak with ⟨h9, hl, hall⟩ | h19
    · obtain ⟨U, hU⟩ := List.length_eq_one_iff.1 hl
      obtain ⟨hU19, o', ho', himg, -, hT'⟩ := hall U (by rw [hU]; exact List.mem_singleton_self U)
      refine Or.inl ⟨h9, U, hU, hU19, ?_⟩
      rcases hT' with hT' | hT'
      · exact Or.inl (List.mem_map.2 ⟨o', ho', by rw [himg, hT']⟩)
      · exact Or.inr (List.mem_map.2 ⟨o', ho', by rw [himg, hT']⟩)
    · exact Or.inr h19
  · obtain ⟨n, h1, h2', U, hU, hUc⟩ := hdesc
    exact ⟨n, h1, h2', U, mem_red_iterate_of_descR h1 h2.1 hU, hUc⟩
  · intro D hD hfree
    obtain ⟨n, -, -, U, hU, hUc⟩ := hdesc
    exact not_mem_of_descR_coincidence hU hUc hD hfree
  · intro S hs P hbal
    have hq : incQ S = incOf o.img := by
      show (inc S.s).map (Nat.cast : ℕ → ℚ) = _
      rw [hs]
    exact not_mem_of_coord S P hbal (hs ▸ hprim') (hq ▸ hχ) hw0 (by rw [hs]; exact hphi)

/-- **The 24 occurrences, as `(σ, T)` pairs, each with its contract.** -/
theorem occurrences_spec : ∀ p ∈ occurrences, OccSpec p.1 p.2 := by
  intro p hp
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hp
  exact catalogue_spec o ho

/-- The census counts of `docs/c4-defect-degree-census.md` §2: `24` distinct occurrences,
over `12` distinct substitutions, exactly one of length `9` and one of length `19` over each
substitution (so `12` of each length). -/
theorem catalogue_counts : occurrences.length = 24 ∧ occurrences.Nodup ∧
    (catalogue.map Occ.img).dedup.length = 12 ∧
    (∀ o ∈ catalogue,
      (catalogue.filter fun o' => o'.img = o.img ∧ o'.T.1.length = 9).length = 1 ∧
      (catalogue.filter fun o' => o'.img = o.img ∧ o'.T.1.length = 19).length = 1) ∧
    (catalogue.filter fun o => o.T.1.length = 9).length = 12 ∧
    (catalogue.filter fun o => o.T.1.length = 19).length = 12 := by
  decide +kernel

/-- **The matrix hypotheses of `thm:deg23` (iii) for all twelve substitutions**: `χ_M`
irreducible, a real root `b > 2` and two further roots of modulus `< 1`, pairwise distinct
(`cubic_certificate`). -/
theorem catalogue_pisot : ∀ o ∈ catalogue, Irreducible (incOf o.img).charpoly ∧
    ∃ b : ℝ, 2 < b ∧ ∃ α γ : ℂ, aeval (b : ℂ) (incOf o.img).charpoly = 0 ∧
      aeval α (incOf o.img).charpoly = 0 ∧ aeval γ (incOf o.img).charpoly = 0 ∧
        (b : ℂ) ≠ α ∧ (b : ℂ) ≠ γ ∧ α ≠ γ ∧ ‖α‖ < 1 ∧ ‖γ‖ < 1 :=
  fun o ho => cubic_certificate (catalogue_spec o ho).charpoly

/-! ### The normal forms of `docs/c4-defect-degree-census.md` §3 (a cross-check) -/

/-- The substitution class `011 / 2 / 120` (`Psc.Degree3Sector.censusSubst`). -/
def sigmaA : Img := ([0, 1, 1], [2], [1, 2, 0])

/-- The substitution class `1 / 210 / 002`. -/
def sigmaB : Img := ([1], [2, 1, 0], [0, 0, 2])

/-- The four normalized state classes of §3. -/
def class9a : List (Fin 3) × List (Fin 3) :=
  ([0, 1, 1, 2, 0, 2, 0, 0, 1], [1, 2, 0, 0, 0, 1, 1, 2, 0])
def class9b : List (Fin 3) × List (Fin 3) :=
  ([0, 1, 1, 2, 1, 2, 0, 0, 1], [1, 2, 0, 0, 1, 1, 1, 2, 0])
def class19a : List (Fin 3) × List (Fin 3) :=
  ([0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2],
    [2, 0, 0, 1, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 2, 2, 0, 0, 1])
def class19b : List (Fin 3) × List (Fin 3) :=
  ([0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1],
    [2, 1, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 2, 1, 1, 2, 1, 1, 0])

/-- The four occurrences over the two class representatives: over `sigmaA` the length-`9`
state `class9b` (`Psc.Degree3Sector.censusPair`) and its child; over `sigmaB` the length-`9`
state `(022101002, 210002210)` and its child (Mojo indices `(16, 2, 27)` and `(1, 33, 14)`). -/
def basePairs : List (Img × (List (Fin 3) × List (Fin 3))) :=
  [(sigmaA, class9b),
    (sigmaA, ([0, 1, 1, 2, 2, 1, 2, 0, 2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2],
      [2, 1, 2, 0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 1, 2, 0, 0, 1, 1])),
    (sigmaB, ([0, 2, 2, 1, 0, 1, 0, 0, 2], [2, 1, 0, 0, 0, 2, 2, 1, 0])),
    (sigmaB, ([0, 0, 2, 2, 1, 0, 1, 1, 1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1],
      [1, 0, 0, 2, 0, 0, 2, 2, 1, 0, 1, 2, 1, 0, 1, 1, 0, 0, 2]))]

/-- The six permutations of `{0,1,2}`. -/
def perms3 : List (Fin 3 → Fin 3) :=
  [![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

theorem perms3_bijective : ∀ π ∈ perms3, Function.Bijective π := by decide

theorem sigmaA_eq : toSubst sigmaA = censusSubst := by
  funext a; fin_cases a <;> rfl

theorem class9b_eq : class9b = censusPair := rfl

theorem basePairs_sub : ∀ q ∈ basePairs, q ∈ occurrences := by decide +kernel

/-- **The catalogue is the relabelling orbit of the four base pairs**: every occurrence is
`(π τ π⁻¹, π R)` or `(π τ π⁻¹, (π R).swap)` for one `π ∈ perms3` and `(τ, R) ∈ basePairs`
(`σ (π a) = π (τ a)`). -/
theorem catalogue_orbit : ∀ o ∈ catalogue, ∃ π ∈ perms3, ∃ q ∈ basePairs,
    (∀ a, toSubst o.img (π a) = (toSubst q.1 a).map π) ∧
      (o.T = relabel π q.2 ∨ o.T = (relabel π q.2).swap) := by
  decide +kernel

/-- **§3's four state relabelling classes**: every catalogue state is a relabelling of
`class9a`, `class9b`, `class19a` or `class19b`, up to side swap (the relabelling need not
be the one that conjugates the substitution). -/
theorem catalogue_state_classes : ∀ o ∈ catalogue, ∃ π ∈ perms3,
    ∃ R ∈ [class9a, class9b, class19a, class19b],
      o.T = relabel π R ∨ o.T = (relabel π R).swap := by
  decide +kernel

/-- §3's two substitution classes: every catalogue substitution is conjugate by a
relabelling to `sigmaA` or `sigmaB`. -/
theorem catalogue_sigma_classes : ∀ o ∈ catalogue, ∃ π ∈ perms3, ∃ τ ∈ [sigmaA, sigmaB],
    ∀ a, toSubst o.img (π a) = (toSubst τ a).map π := by
  decide +kernel

/-- §3's reversal statements: reversing every image of `sigmaA` gives a relabelling of
`sigmaB`; reversing both words exchanges the two length-`9` classes and the two
length-`19` classes, up to relabelling. -/
theorem reversal_exchanges :
    (∃ π ∈ perms3, ∀ a, toSubst sigmaB (π a) = ((toSubst sigmaA a).reverse).map π) ∧
    (∃ π ∈ perms3, class9b = relabel π (class9a.1.reverse, class9a.2.reverse)) ∧
    (∃ π ∈ perms3, class19b = relabel π (class19a.1.reverse, class19a.2.reverse)) := by
  decide +kernel

/-- `perms3` lists every bijection of `{0,1,2}`, so a statement over `π ∈ perms3` is a
statement over every relabelling. -/
theorem perms3_complete : ∀ π : Fin 3 → Fin 3, Function.Bijective π → π ∈ perms3 := by
  decide +kernel

/-- §3's four state classes. -/
def stateClasses : List (List (Fin 3) × List (Fin 3)) := [class9a, class9b, class19a, class19b]

/-- **§3's "exactly four" state classes.**  Each class is attained by a catalogue state, up
to relabelling and side swap, and no two of the four are equivalent under relabelling and
side swap (the equivalence of `canonical_pair` in `kernel/substitution_dynamics/symmetry.mojo`).
With `catalogue_state_classes` (every catalogue state lies in one of them) and
`perms3_complete`, the catalogue meets exactly four classes. -/
theorem state_classes_exact :
    (∀ R ∈ stateClasses, ∃ o ∈ catalogue, ∃ π ∈ perms3,
      o.T = relabel π R ∨ o.T = (relabel π R).swap) ∧
    ∀ R ∈ stateClasses, ∀ R' ∈ stateClasses, ∀ π ∈ perms3,
      (R' = relabel π R ∨ R' = (relabel π R).swap) → R = R' := by
  decide +kernel

/-- **§3's "exactly two" substitution classes.**  Both representatives are catalogue
substitutions, and `sigmaB` is not conjugate to `sigmaA` by any relabelling (with
`catalogue_sigma_classes` and `perms3_complete`). -/
theorem sigma_classes_exact :
    sigmaA ∈ catalogue.map Occ.img ∧ sigmaB ∈ catalogue.map Occ.img ∧
    ∀ π ∈ perms3, ¬ ∀ a, toSubst sigmaB (π a) = (toSubst sigmaA a).map π := by
  decide +kernel

/-! ### Completeness over the twelve automata -/

section Closure

variable {α : Type*} [DecidableEq α]

/-- `X` is closed in `F`: a coincidence block, or every child of `X` lies in `F`. -/
def ClosedIn (s : α → List α) (F : List (List α × List α)) (X : List α × List α) : Prop :=
  X.1 = X.2 ∨ ∀ U ∈ red (subst s X.1) (subst s X.2), U ∈ F

theorem ClosedIn.mono {s : α → List α} {F G : List (List α × List α)} (hFG : F ⊆ G)
    {X : List α × List α} (h : ClosedIn s F X) : ClosedIn s G X :=
  h.imp id fun h U hU => hFG (h U hU)

/-- Append to `acc` the members of the list that are neither in `seen` nor already
appended. -/
def addNew (seen : List (List α × List α)) :
    List (List α × List α) → List (List α × List α) → List (List α × List α)
  | acc, [] => acc
  | acc, Y :: ys => addNew seen (if Y ∈ seen ∨ Y ∈ acc then acc else acc ++ [Y]) ys

theorem subset_addNew (seen : List (List α × List α)) :
    ∀ (acc l : List (List α × List α)), acc ⊆ addNew seen acc l
  | acc, [] => List.Subset.refl _
  | acc, Y :: ys => by
    refine fun Z hZ => subset_addNew seen _ ys ?_
    split_ifs
    · exact hZ
    · exact List.mem_append_left _ hZ

theorem mem_addNew (seen : List (List α × List α)) :
    ∀ (acc l : List (List α × List α)), ∀ Y ∈ l, Y ∈ seen ∨ Y ∈ addNew seen acc l
  | acc, [], Y, hY => absurd hY List.not_mem_nil
  | acc, Z :: zs, Y, hY => by
    rcases List.mem_cons.1 hY with rfl | hY
    · show Y ∈ seen ∨ Y ∈ addNew seen _ zs
      split_ifs with h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (subset_addNew seen _ zs h)
      · exact Or.inr (subset_addNew seen _ zs
          (List.mem_append_right _ (List.mem_singleton_self Y)))
    · exact mem_addNew seen _ zs Y hY

/-- `addNew` appends only members of the list. -/
theorem addNew_sub (seen : List (List α × List α)) :
    ∀ (acc l : List (List α × List α)), ∀ Y ∈ addNew seen acc l, Y ∈ acc ∨ Y ∈ l
  | acc, [], Y, hY => Or.inl hY
  | acc, Z :: zs, Y, hY => by
    have hY' : Y ∈ addNew seen (if Z ∈ seen ∨ Z ∈ acc then acc else acc ++ [Z]) zs := hY
    rcases addNew_sub seen _ zs Y hY' with h | h
    · split_ifs at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons.2 (Or.inl (List.mem_singleton.1 h)))
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- `addNew` appends without repetition, and nothing already in `seen`. -/
theorem addNew_nodup (seen : List (List α × List α)) :
    ∀ (acc l : List (List α × List α)), acc.Nodup → (∀ Y ∈ acc, Y ∉ seen) →
      (addNew seen acc l).Nodup ∧ ∀ Y ∈ addNew seen acc l, Y ∉ seen
  | acc, [], h1, h2 => ⟨h1, h2⟩
  | acc, Z :: zs, h1, h2 => by
    show (addNew seen (if Z ∈ seen ∨ Z ∈ acc then acc else acc ++ [Z]) zs).Nodup ∧
      ∀ Y ∈ addNew seen (if Z ∈ seen ∨ Z ∈ acc then acc else acc ++ [Z]) zs, Y ∉ seen
    split_ifs with h
    · exact addNew_nodup seen acc zs h1 h2
    · push Not at h
      refine addNew_nodup seen _ zs ?_ ?_
      · rw [← List.concat_eq_append]
        exact h1.concat h.2
      · intro Y hY
        rcases List.mem_append.1 hY with hY | hY
        · exact h2 Y hY
        · rw [List.mem_singleton.1 hY]
          exact h.1

/-- **Fuelled breadth-first closure** of a worklist under the children of noncoincident
states (coincidence blocks are terminal, as in `B_σ`).  Fails closed: `none` when the fuel
runs out before the worklist is empty. -/
def closureO (s : α → List α) :
    ℕ → List (List α × List α) → List (List α × List α) → Option (List (List α × List α))
  | 0, _, _ => none
  | _ + 1, [], seen => some seen
  | n + 1, X :: todo, seen =>
    if X.1 = X.2 then closureO s n todo seen
    else
      closureO s n (todo ++ addNew seen [] (red (subst s X.1) (subst s X.2)))
        (seen ++ addNew seen [] (red (subst s X.1) (subst s X.2)))

/-- **Soundness of the closure**: under the worklist invariant (every member of `seen` is
still to be processed or already closed in `seen`), a returned `F` contains `seen` and
every member of `F` is closed in `F`.  Nothing about the search order or the
deduplication is used. -/
theorem closureO_sound (s : α → List α) :
    ∀ (n : ℕ) (todo seen F : List (List α × List α)),
      closureO s n todo seen = some F → (∀ X ∈ seen, X ∈ todo ∨ ClosedIn s seen X) →
        seen ⊆ F ∧ ∀ X ∈ F, ClosedIn s F X
  | 0, _, _, F, h, _ => by simp [closureO] at h
  | n + 1, [], seen, F, h, hinv => by
    simp only [closureO, Option.some.injEq] at h
    subst h
    exact ⟨List.Subset.refl _, fun X hX => (hinv X hX).resolve_left List.not_mem_nil⟩
  | n + 1, X :: todo, seen, F, h, hinv => by
    simp only [closureO] at h
    split_ifs at h with hX
    · refine closureO_sound s n todo seen F h fun Y hY => ?_
      rcases hinv Y hY with hY' | hY'
      · rcases List.mem_cons.1 hY' with rfl | hY'
        · exact Or.inr (Or.inl hX)
        · exact Or.inl hY'
      · exact Or.inr hY'
    · set new := addNew seen [] (red (subst s X.1) (subst s X.2))
      have hsub : seen ⊆ seen ++ new := List.subset_append_left _ _
      obtain ⟨h1, h2⟩ := closureO_sound s n (todo ++ new) (seen ++ new) F h fun Y hY => by
        rcases List.mem_append.1 hY with hY | hY
        · rcases hinv Y hY with hY' | hY'
          · rcases List.mem_cons.1 hY' with rfl | hY'
            · refine Or.inr (Or.inr fun U hU => ?_)
              rcases mem_addNew seen [] _ U hU with hU | hU
              · exact List.mem_append_left _ hU
              · exact List.mem_append_right _ hU
            · exact Or.inl (List.mem_append_left _ hY')
          · exact Or.inr (hY'.mono hsub)
        · exact Or.inl (List.mem_append_right _ hY)
      exact ⟨fun Z hZ => h1 (hsub hZ), h2⟩

/-- **The closure adds nothing outside a child-closed set**: if `B` contains the children of
its noncoincident members, and `todo` and `seen` lie in `B`, a returned `F` lies in `B`. -/
theorem closureO_subset (s : α → List α) {B : Set (List α × List α)}
    (hB : ∀ X ∈ B, X.1 ≠ X.2 → ∀ U ∈ red (subst s X.1) (subst s X.2), U ∈ B) :
    ∀ (n : ℕ) (todo seen F : List (List α × List α)),
      closureO s n todo seen = some F → (∀ X ∈ todo, X ∈ B) → (∀ X ∈ seen, X ∈ B) →
        ∀ X ∈ F, X ∈ B
  | 0, _, _, F, h, _, _ => by simp [closureO] at h
  | n + 1, [], seen, F, h, _, hs => by
    simp only [closureO, Option.some.injEq] at h
    subst h
    exact hs
  | n + 1, X :: todo, seen, F, h, ht, hs => by
    simp only [closureO] at h
    have hX : X ∈ B := ht X (List.mem_cons_self ..)
    have ht' : ∀ Y ∈ todo, Y ∈ B := fun Y hY => ht Y (List.mem_cons_of_mem _ hY)
    split_ifs at h with hXc
    · exact closureO_subset s hB n todo seen F h ht' hs
    · have hnew : ∀ Y ∈ addNew seen [] (red (subst s X.1) (subst s X.2)), Y ∈ B := by
        intro Y hY
        rcases addNew_sub seen [] _ Y hY with h' | h'
        · exact absurd h' List.not_mem_nil
        · exact hB X hX hXc Y h'
      refine closureO_subset s hB n _ _ F h (fun Y hY => ?_) (fun Y hY => ?_)
      · rcases List.mem_append.1 hY with hY | hY
        · exact ht' Y hY
        · exact hnew Y hY
      · rcases List.mem_append.1 hY with hY | hY
        · exact hs Y hY
        · exact hnew Y hY

/-- **The closure lists without repetition** when `seen` does. -/
theorem closureO_nodup (s : α → List α) :
    ∀ (n : ℕ) (todo seen F : List (List α × List α)),
      closureO s n todo seen = some F → seen.Nodup → F.Nodup
  | 0, _, _, F, h, _ => by simp [closureO] at h
  | n + 1, [], seen, F, h, hs => by
    simp only [closureO, Option.some.injEq] at h
    subst h
    exact hs
  | n + 1, X :: todo, seen, F, h, hs => by
    simp only [closureO] at h
    split_ifs at h with hX
    · exact closureO_nodup s n todo seen F h hs
    · refine closureO_nodup s n _ _ F h ?_
      obtain ⟨h1, h2⟩ := addNew_nodup seen [] (red (subst s X.1) (subst s X.2))
        List.nodup_nil (fun _ h => absurd h List.not_mem_nil)
      exact List.nodup_append.2 ⟨hs, h1, fun a ha b hb hab => h2 b hb (hab ▸ ha)⟩

/-- `B_σ` contains the children of its noncoincident vertices. -/
theorem bpaStatesNC_closed [Fintype α] (s : α → List α) :
    ∀ X ∈ bpaStatesNC s, X.1 ≠ X.2 → ∀ U ∈ red (subst s X.1) (subst s X.2),
      U ∈ bpaStatesNC s :=
  fun _ ⟨T, hT, hTX⟩ hne _ hU => ⟨T, hT, hTX.tail ⟨hne, hU⟩⟩

/-- A closed list containing the seeds contains `B_σ` (`bpaStatesNC_subset`). -/
theorem bpaStatesNC_subset_of_closed [Fintype α] {s : α → List α}
    {F : List (List α × List α)} (hseed : ∀ a b : α, a ≠ b → ([a, b], [b, a]) ∈ F)
    (hF : ∀ X ∈ F, ClosedIn s F X) : bpaStatesNC s ⊆ {T | T ∈ F} := by
  refine bpaStatesNC_subset s (fun T hT => ?_) (fun T hT hne U hU => ?_)
  · obtain ⟨a, b, hab, rfl⟩ := mem_seeds.1 hT
    exact hseed a b hab
  · exact ((hF T hT).resolve_left hne) U hU

end Closure

/-- The six seeds `(ab, ba)` over `{0,1,2}`. -/
def seedList : List (List (Fin 3) × List (Fin 3)) :=
  [([0, 1], [1, 0]), ([0, 2], [2, 0]), ([1, 0], [0, 1]), ([1, 2], [2, 1]), ([2, 0], [0, 2]),
    ([2, 1], [1, 2])]

theorem seedList_spec : ∀ a b : Fin 3, a ≠ b → ([a, b], [b, a]) ∈ seedList := by decide

theorem seedList_nodup : seedList.Nodup := by decide

theorem seedList_mem_bpaStatesNC (s : Fin 3 → List (Fin 3)) :
    ∀ X ∈ seedList, X ∈ bpaStatesNC s := by
  have h : ∀ X ∈ seedList, ∃ a b : Fin 3, a ≠ b ∧ X = ([a, b], [b, a]) := by decide
  intro X hX
  exact ⟨X, mem_seeds.2 (h X hX), .refl⟩

/-- The fuel of the closure, one step per worklist entry.  It is a budget, not a bound
on `B_σ`: an exhausted budget makes `completeCheck` return `false`, so the check refuses
to conclude rather than concluding wrongly (`budget_control`). -/
def closureFuel : ℕ := 1000

/-- The census statistics of a closure list `F`: its length, its number of noncoincident
members, and its number of noncoincident `∼₂` members. -/
def closureStats (F : List (List (Fin 3) × List (Fin 3))) : ℕ × ℕ × ℕ :=
  (F.length, (F.filter fun T => !decide (T.1 = T.2)).length,
    (F.filter fun T => !decide (T.1 = T.2) && decide (Equiv2 T.1 T.2)).length)

/-- The census check over one substitution, with a budget `fuel` and pinned statistics
`stats`: the closure from the seeds terminates within the budget, its statistics are
`stats`, and its only noncoincident `∼₂` members are catalogue states over `σ`, in either
orientation. -/
def completeCheck (fuel : ℕ) (σ : Img) (stats : ℕ × ℕ × ℕ) : Bool :=
  match closureO (toSubst σ) fuel seedList seedList with
  | none => false
  | some F => decide (closureStats F = stats) && F.all fun T =>
      decide (T.1 = T.2) || !decide (Equiv2 T.1 T.2) ||
      occurrences.any (fun p => decide (p = (σ, T))) ||
      occurrences.any (fun p => decide (p = (σ, T.swap)))

/-- **What `completeCheck` certifies, exactly**: the vertex set of `B_σ` is listed without
repetition by a list `F` whose statistics are `stats`, and the noncoincident `∼₂` members
of `F` are catalogue states over `σ`, up to side swap.  The closure is sound in both
directions: it contains `B_σ` (`closureO_sound`, `bpaStatesNC_subset_of_closed`) and adds
nothing outside it (`closureO_subset`, `bpaStatesNC_closed`). -/
theorem exact_of_check {fuel : ℕ} {σ : Img} {stats : ℕ × ℕ × ℕ}
    (h : completeCheck fuel σ stats = true) :
    ∃ F : List (List (Fin 3) × List (Fin 3)), F.Nodup ∧
      (∀ T, T ∈ bpaStatesNC (toSubst σ) ↔ T ∈ F) ∧ closureStats F = stats ∧
      ∀ T ∈ F, T.1 ≠ T.2 → Equiv2 T.1 T.2 →
        (σ, T) ∈ occurrences ∨ (σ, T.swap) ∈ occurrences := by
  unfold completeCheck at h
  split at h
  · exact absurd h Bool.false_ne_true
  · rename_i F hF
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hst, hall⟩ := h
    obtain ⟨hseen, hcl⟩ := closureO_sound _ _ _ _ F hF fun X hX => Or.inl hX
    have hsub := bpaStatesNC_subset_of_closed (fun a b hab => hseen (seedList_spec a b hab)) hcl
    have hsup := closureO_subset _ (bpaStatesNC_closed _) _ _ _ F hF
      (seedList_mem_bpaStatesNC _) (seedList_mem_bpaStatesNC _)
    refine ⟨F, closureO_nodup _ _ _ _ F hF seedList_nodup, fun T => ⟨fun hT => hsub hT, hsup T⟩,
      hst, fun T hT hne h2 => ?_⟩
    have hT' := List.all_eq_true.1 hall T hT
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      List.any_eq_true] at hT'
    rcases hT' with ((h1 | h1) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact absurd h1 hne
    · exact absurd h2 h1
    · exact Or.inl hp
    · exact Or.inr hp

/-- What `completeCheck` certifies about `∼₂`: `B_σ` is finite (G1 for `σ`), and its
noncoincident `∼₂` vertices (first defect degree `≥ 3`) are catalogue states over `σ`, up
to side swap. -/
theorem complete_of_check {fuel : ℕ} {σ : Img} {stats : ℕ × ℕ × ℕ}
    (h : completeCheck fuel σ stats = true) :
    (bpaStatesNC (toSubst σ)).Finite ∧ ∀ T ∈ bpaStatesNC (toSubst σ), T.1 ≠ T.2 →
      Equiv2 T.1 T.2 → (σ, T) ∈ occurrences ∨ (σ, T.swap) ∈ occurrences := by
  obtain ⟨F, -, hF, -, hcl⟩ := exact_of_check h
  exact ⟨(List.finite_toSet F).subset fun T hT => (hF T).1 hT,
    fun T hT => hcl T ((hF T).1 hT)⟩

/-- What `completeCheck` certifies about sizes: `stats = (n₀, n₁, n₂)` are the numbers of
vertices, noncoincident vertices and noncoincident `∼₂` vertices of `B_σ`. -/
theorem card_of_check {fuel : ℕ} {σ : Img} {n₀ n₁ n₂ : ℕ}
    (h : completeCheck fuel σ (n₀, n₁, n₂) = true) :
    (bpaStatesNC (toSubst σ)).ncard = n₀ ∧
      {T ∈ bpaStatesNC (toSubst σ) | T.1 ≠ T.2}.ncard = n₁ ∧
      {T ∈ bpaStatesNC (toSubst σ) | T.1 ≠ T.2 ∧ Equiv2 T.1 T.2}.ncard = n₂ := by
  obtain ⟨F, hnd, hF, hst, -⟩ := exact_of_check h
  simp only [closureStats, Prod.mk.injEq] at hst
  obtain ⟨h0, h1, h2⟩ := hst
  refine ⟨by rw [ncard_of_list hnd hF, h0], ?_, ?_⟩
  · rw [ncard_sep_of_list hnd hF (fun T => !decide (T.1 = T.2)) (fun T => by simp), h1]
  · rw [ncard_sep_of_list hnd hF (fun T => !decide (T.1 = T.2) && decide (Equiv2 T.1 T.2))
      (fun T => by simp), h2]

/-- **`B_σ` for the two class representatives, by a checked closure** (each a separate
kernel evaluation of `closureO`): `226` vertices, `224` of them noncoincident, `4` of those
`∼₂`, all catalogue states or their swaps. -/
theorem complete_sigmaA : completeCheck closureFuel sigmaA (226, 224, 4) = true := by
  decide +kernel

theorem complete_sigmaB : completeCheck closureFuel sigmaB (226, 224, 4) = true := by
  decide +kernel

/-- Relabelling the base occurrences along a conjugating permutation gives catalogue
occurrences (a finite table, by evaluation). -/
theorem transfer_table : ∀ o ∈ catalogue, ∀ π ∈ perms3, ∀ τ ∈ [sigmaA, sigmaB],
    (∀ a, toSubst o.img (π a) = (toSubst τ a).map π) → ∀ q ∈ occurrences, q.1 = τ →
      ∃ p ∈ occurrences, p = (o.img, relabel π q.2) ∨ p = (o.img, (relabel π q.2).swap) := by
  decide +kernel

/-- **Completeness of the catalogue over its twelve automata.**  For every catalogue
substitution `σ`, `B_σ` is finite, and every noncoincident `∼₂` vertex of `B_σ` is a
catalogue state over `σ`, up to side swap.  (The consequences for the other vertices are
`catalogue_degree_two` and `catalogue_k3_ne`.)  Proof:
`σ = π τ π⁻¹` with `τ ∈ {sigmaA, sigmaB}` (`catalogue_sigma_classes`); relabel along `π⁻¹`
into `B_τ` (`relabel_mem_bpaStatesNC`, `equiv2_map`), apply `complete_sigmaA` /
`complete_sigmaB`, and relabel back (`transfer_table`). -/
theorem catalogue_complete : ∀ o ∈ catalogue, (bpaStatesNC (toSubst o.img)).Finite ∧
    ∀ T ∈ bpaStatesNC (toSubst o.img), T.1 ≠ T.2 → Equiv2 T.1 T.2 →
      (o.img, T) ∈ occurrences ∨ (o.img, T.swap) ∈ occurrences := by
  intro o ho
  obtain ⟨π, hπ, τ, hτ, hc⟩ := catalogue_sigma_classes o ho
  have hbij := perms3_bijective π hπ
  set e := Equiv.ofBijective π hbij
  have he1 : ∀ x, π (e.symm x) = x := fun x => e.apply_symm_apply x
  have he2 : ∀ x, e.symm (π x) = x := fun x => e.symm_apply_apply x
  -- the inverse conjugacy `τ ∘ π⁻¹ = map π⁻¹ ∘ σ`
  have hc' : ∀ y, toSubst τ (e.symm y) = (toSubst o.img y).map e.symm := by
    intro y
    conv_rhs => rw [← he1 y, hc (e.symm y), List.map_map]
    rw [show (e.symm ∘ π) = id from funext he2, List.map_id]
  have hbase : completeCheck closureFuel τ (226, 224, 4) = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl
    · exact complete_sigmaA
    · exact complete_sigmaB
  obtain ⟨hfin, hcomp⟩ := complete_of_check hbase
  have hback : ∀ T : List (Fin 3) × List (Fin 3), relabel π (relabel e.symm T) = T := by
    intro T
    rw [relabel_relabel, show (π ∘ e.symm) = id from funext he1]
    simp [relabel]
  have hmem : ∀ T ∈ bpaStatesNC (toSubst o.img), relabel e.symm T ∈ bpaStatesNC (toSubst τ) :=
    fun T hT => relabel_mem_bpaStatesNC e.symm.injective hc' hT
  refine ⟨(hfin.image (relabel π)).subset fun T hT => ⟨_, hmem T hT, hback T⟩,
    fun T hT hne h2 => ?_⟩
  have hne' : (relabel e.symm T).1 ≠ (relabel e.symm T).2 :=
    fun h => hne (List.map_injective_iff.2 e.symm.injective h)
  have h2' : Equiv2 (relabel e.symm T).1 (relabel e.symm T).2 :=
    equiv2_map e.symm.bijective h2
  have key : ∀ q ∈ occurrences, q.1 = τ → q.2 = relabel e.symm T ∨ q.2 = (relabel e.symm T).swap →
      (o.img, T) ∈ occurrences ∨ (o.img, T.swap) ∈ occurrences := by
    intro q hq hq1 hq2
    obtain ⟨p, hp, hpq⟩ := transfer_table o ho π hπ τ hτ hc q hq hq1
    rcases hq2 with hq2 | hq2 <;> rw [hq2] at hpq
    · rw [hback] at hpq
      rcases hpq with rfl | rfl
      · exact Or.inl hp
      · exact Or.inr hp
    · rw [relabel_swap, hback, Prod.swap_swap] at hpq
      rcases hpq with rfl | rfl
      · exact Or.inr hp
      · exact Or.inl hp
  rcases hcomp _ (hmem T hT) hne' h2' with h | h
  · exact key _ h rfl (Or.inl rfl)
  · exact key _ h rfl (Or.inr rfl)

/-- **The catalogue is exact over its twelve automata**: for a catalogue substitution `σ`,
the noncoincident `∼₂` vertices of `B_σ` are exactly the catalogue states over `σ` and
their side swaps (`catalogue_complete` and `occurrences_spec`). -/
theorem catalogue_exact : ∀ o ∈ catalogue, ∀ T : List (Fin 3) × List (Fin 3),
    (T ∈ bpaStatesNC (toSubst o.img) ∧ T.1 ≠ T.2 ∧ Equiv2 T.1 T.2) ↔
      ((o.img, T) ∈ occurrences ∨ (o.img, T.swap) ∈ occurrences) := by
  intro o ho T
  constructor
  · rintro ⟨hT, hne, h2⟩
    exact (catalogue_complete o ho).2 T hT hne h2
  · rintro (h | h)
    · have hs := occurrences_spec _ h
      exact ⟨hs.reachable.1, hs.noncoincident, hs.equiv2⟩
    · have hs := occurrences_spec _ h
      refine ⟨by simpa using hs.reachable.2, fun e => hs.noncoincident e.symm, ?_⟩
      exact ⟨fun a => (hs.equiv2.1 a).symm, fun a b => (hs.equiv2.2 a b).symm⟩

/-- **`docs/c4-defect-degree-census.md` §7 over the twelve catalogue automata.**  For a
catalogue substitution `σ`, no nonempty child-closed, coincidence-free set of vertices of
`B_σ` has only `∼₂` states; in particular `B_σ` has no strict component whose first
nonzero defect has degree `≥ 3`.  Every such state would be a catalogue state or its swap
(`catalogue_exact`), and those leak (`OccSpec.not_closed`, applied to the swap closure of
the set, `swapClosure_childClosed`, `swapClosure_coincidenceFree`).  This does not use
`OccSpec.not_mem`, the independent spectral exclusion. -/
theorem no_closed_equiv2 : ∀ o ∈ catalogue, ∀ D : Set (List (Fin 3) × List (Fin 3)),
    D ⊆ bpaStatesNC (toSubst o.img) → ChildClosed (toSubst o.img) D → CoincidenceFree D →
      (∀ T ∈ D, Equiv2 T.1 T.2) → D = ∅ := by
  intro o ho D hDB hD hfree h2
  refine Set.eq_empty_of_forall_notMem fun T hT => ?_
  have hD' := swapClosure_childClosed hD
  have hfree' := swapClosure_coincidenceFree hfree
  rcases (catalogue_exact o ho T).1 ⟨hDB hT, hfree T hT, h2 T hT⟩ with h | h
  · exact (occurrences_spec _ h).not_closed _ hD' hfree' (subset_swapClosure hT)
  · exact (occurrences_spec _ h).not_closed _ hD' hfree' (Or.inr ⟨T, hT, rfl⟩)

/-- **First defect degree over the twelve automata.**  For a catalogue substitution `σ`,
every noncoincident vertex of `B_σ` that is not a catalogue state over `σ` (in either
orientation) has `K₁ = 0` and `K₂ ≠ 0`: first defect degree exactly two. -/
theorem catalogue_degree_two : ∀ o ∈ catalogue, ∀ T ∈ bpaStatesNC (toSubst o.img),
    T.1 ≠ T.2 → (o.img, T) ∉ occurrences → (o.img, T.swap) ∉ occurrences →
      Equiv1 T.1 T.2 ∧ ∃ a b, n2 T.1 a b ≠ n2 T.2 a b := by
  intro o ho T hT hne h1 h2
  have he1 := bpaStates_equiv1 _ T (bpaStatesNC_subset_bpaStates _ hT)
  refine ⟨he1, ?_⟩
  by_contra hn
  push Not at hn
  rcases (catalogue_complete o ho).2 T hT hne ⟨he1, hn⟩ with h | h
  · exact h1 h
  · exact h2 h

/-- **No first defect degree `≥ 4` over the twelve automata**: a noncoincident `∼₂` vertex
of `B_σ` has `K₃ ≠ 0` (`catalogue_complete`, `OccSpec.k3_ne`, `k3Vec_swap_ne`). -/
theorem catalogue_k3_ne : ∀ o ∈ catalogue, ∀ T ∈ bpaStatesNC (toSubst o.img), T.1 ≠ T.2 →
    Equiv2 T.1 T.2 → Lie3.k3Vec T.1 T.2 ≠ 0 := by
  intro o ho T hT hne h2
  rcases (catalogue_complete o ho).2 T hT hne h2 with h | h
  · exact (occurrences_spec _ h).k3_ne
  · exact k3Vec_swap_ne (occurrences_spec _ h).k3_ne

/-- **The size of each of the twelve automata**: for every catalogue substitution `σ`,
`B_σ` has exactly `226` vertices (ordered pairs), `224` of them noncoincident, and exactly
`4` of those `∼₂` (the two catalogue states over `σ` and their swaps).  Proof: `B_σ` is the
relabelling of `B_τ` (`bpaStatesNC_conj`), and the counts for `τ` are pinned in the kernel
evaluations `complete_sigmaA`, `complete_sigmaB` (`card_of_check`). -/
theorem catalogue_card : ∀ o ∈ catalogue,
    (bpaStatesNC (toSubst o.img)).ncard = 226 ∧
      {T ∈ bpaStatesNC (toSubst o.img) | T.1 ≠ T.2}.ncard = 224 ∧
      {T ∈ bpaStatesNC (toSubst o.img) | T.1 ≠ T.2 ∧ Equiv2 T.1 T.2}.ncard = 4 := by
  intro o ho
  obtain ⟨π, hπ, τ, hτ, hc⟩ := catalogue_sigma_classes o ho
  set e := Equiv.ofBijective π (perms3_bijective π hπ)
  have hB : bpaStatesNC (toSubst o.img) = relabel e '' bpaStatesNC (toSubst τ) :=
    bpaStatesNC_conj e hc
  have hbase : completeCheck closureFuel τ (226, 224, 4) = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl
    · exact complete_sigmaA
    · exact complete_sigmaB
  obtain ⟨h0, h1, h2⟩ := card_of_check hbase
  have hinj := relabel_injective e.injective
  have hnc : ∀ T : List (Fin 3) × List (Fin 3),
      (relabel e T).1 ≠ (relabel e T).2 ↔ T.1 ≠ T.2 :=
    fun T => (List.map_injective_iff.2 e.injective).ne_iff
  refine ⟨?_, ?_, ?_⟩
  · rw [hB, Set.ncard_image_of_injective _ hinj, h0]
  · rw [hB, ncard_sep_image hinj _ (p := fun T => T.1 ≠ T.2) (q := fun T => T.1 ≠ T.2) hnc, h1]
  · rw [hB, ncard_sep_image hinj _ (p := fun T => T.1 ≠ T.2 ∧ Equiv2 T.1 T.2)
      (q := fun T => T.1 ≠ T.2 ∧ Equiv2 T.1 T.2)
      (fun T => and_congr (hnc T) (equiv2_map_iff e)), h2]

/-! ### Controls -/

/-- **Negative control: the leak pattern is not a property of every `∼₂` pair over a
catalogue substitution.**  `class9a = (011202001, 120001120)` is `∼₂` with `K₃ ≠ 0` (it is
the catalogue state over `(2, 13, 27)`), but over `sigmaA` it is not an occurrence: its
inflation is a single `∼₂` block of length `21`, not a catalogue state in either
orientation, and no coincidence block occurs among its depth-one or depth-two descendants.
So `OccSpec.leak` and `OccSpec.leak_two` depend on the pairing of state and substitution;
indeed `class9a` is not a vertex of `B_σ` for `σ = sigmaA` (`class9a_not_mem_sigmaA`). -/
theorem class9a_sigmaA_control :
    Equiv2 class9a.1 class9a.2 ∧ Lie3.k3Vec class9a.1 class9a.2 ≠ 0 ∧
      (sigmaA, class9a) ∉ occurrences ∧ (sigmaA, class9a.swap) ∉ occurrences ∧
      (red (subst (toSubst sigmaA) class9a.1) (subst (toSubst sigmaA) class9a.2)).length = 1 ∧
      (∀ U ∈ red (subst (toSubst sigmaA) class9a.1) (subst (toSubst sigmaA) class9a.2),
        U.1.length = 21 ∧ Equiv2 U.1 U.2) ∧
      (∀ U ∈ red (subst (toSubst sigmaA) class9a.1) (subst (toSubst sigmaA) class9a.2),
        ∀ p ∈ occurrences, p ≠ (sigmaA, U) ∧ p ≠ (sigmaA, U.swap)) ∧
      ∀ n ∈ [1, 2], ∀ U ∈ descR (toSubst sigmaA) n class9a, U.1 ≠ U.2 :=
  ⟨by decide +kernel, k3Vec_ne_of_coord (a := 0) (b := 0) (c := 2) (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- `class9a` is not a vertex of `B_σ` for `σ = sigmaA` (`complete_sigmaA`): the
catalogue's pairing of states with substitutions is forced, not chosen. -/
theorem class9a_not_mem_sigmaA : class9a ∉ bpaStatesNC (toSubst sigmaA) := by
  intro h
  rcases (complete_of_check complete_sigmaA).2 class9a h (by decide)
    class9a_sigmaA_control.1 with h' | h'
  · exact class9a_sigmaA_control.2.2.1 h'
  · exact class9a_sigmaA_control.2.2.2.1 h'

/-- **Non-vacuity of `OccSpec.not_closed`**: for Thue–Morse the seed `(01, 10)` does lie in
a child-closed, coincidence-free set, namely `bpaStates thueMorseSubst`
(`Psc.Descendants.tm_bpaStates`). -/
theorem tm_closed_control : ∃ D : Set (List (Fin 2) × List (Fin 2)),
    ChildClosed thueMorseSubst D ∧ CoincidenceFree D ∧ tmPair ∈ D := by
  refine ⟨bpaStates thueMorseSubst, bpaStates_childClosed _, ?_, ?_⟩
  · intro T hT
    rw [tm_bpaStates, Finset.mem_coe] at hT
    revert T
    decide
  · rw [tm_bpaStates, Finset.mem_coe]
    decide

/-- **Fail-closed control of the closure check.**  With a budget of `10` worklist steps the
closure over `sigmaA` does not finish (`B_σ` has `226` vertices), and `completeCheck`
refuses, returning `false`, rather than concluding. -/
theorem budget_control : closureO (toSubst sigmaA) 10 seedList seedList = none ∧
    completeCheck 10 sigmaA (226, 224, 4) = false := by
  decide +kernel

/-- **Sensitivity of the pinned counts**: any other vertex count is refused by the full
check (no second evaluation; by `card_of_check` and `complete_sigmaA`). -/
theorem stats_control : ∀ n₀ n₁ n₂ : ℕ, n₀ ≠ 226 →
    completeCheck closureFuel sigmaA (n₀, n₁, n₂) = false := by
  intro n₀ n₁ n₂ hn
  cases h : completeCheck closureFuel sigmaA (n₀, n₁, n₂)
  · rfl
  · exact absurd ((card_of_check h).1.symm.trans (card_of_check complete_sigmaA).1) hn

end Psc.Degree3Catalogue
