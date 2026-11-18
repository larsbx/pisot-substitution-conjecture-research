/-
# Theorem FC1 on the standing class: contraction data from an irreducible Pisot spectrum

`docs/c4-geometric-f-class-2026-11-16.md` §1 (the standing class PIP3: `σ` primitive, `χ_M`
irreducible over `ℚ` with roots `β > 1 > |λ₂|, |λ₃|`; the Perron row `ℓ` and the left
eigenvectors `η₂, η₃`), §2 (Lemma 1 (2), Lemma 3 (1)–(3)) and §3 (Theorem FC1).
`PscVerif.GeometricFInclusion` and `PscVerif.GeometricFStrict` prove Theorem FC1 in abstract
form, with `LengthData`, `β > 1` and `ContractionData` as hypotheses, and record that no
theorem binds those hypotheses to the standing class.  This module proves the binding: the
abstract hypotheses follow from the spectral hypotheses the repository states for the
standing class, so Theorem FC1 holds there with property (F) as the only hypothesis left.

**Setting.**  That of `PscVerif.GeometricFInclusion`: `α` a finite alphabet with decidable
equality, `s : α → List α`, `M = Psc.Incidence.inc s`.  The standing spectral hypotheses are
used in the forms in which they are stated on main, with no new predicate:
* (P) primitivity `∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c`;
* (I) `Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly`;
* (E) a positive left eigen-row `ℓ`, `ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ` (it exists
  under (P): `Psc.PerronExistence.exists_pos_left_eigen_inc`); the length functional is
  `Psc.GeometricF.lenHom ℓ`;
* the Pisot hypothesis, in one of three forms: (R) the root form of `Psc.BPrime.isPisot_of`
  and of the conclusion of `Psc.BPrime.bprime_cubic`, "every complex root `z ≠ β` of `χ_M`
  has `‖z‖ < 1`"; `Psc.BPrime.IsPisot β`; or the form of `Psc.Degree4Floor.sieve4_pisot` and
  `Psc.Degree5Completion`, a complex root `β` of `χ_M` with `1 < ‖β‖` and every other complex
  root of modulus `< 1`;
* (F) `Psc.GeometricF.PropertyF s (lenHom ℓ)`.

**Definitions.**  `dotHom w` (`v ↦ w·v` on integer vectors, for a complex row `w`); `fibX`,
`fibY` (the length coordinate and its conjugate for Fibonacci).

**Proved here, in full** (`propext`, `Classical.choice`, `Quot.sound` only):
* **Lemma 1 (2), in the form of properness.**  `finite_of_span_eq_top` (rows that span
  `ℂ^α`: only finitely many integer vectors have all coordinates bounded);
  `span_eq_top_of_left_eigen` (`|α|` nonzero left eigen-rows for pairwise distinct
  eigenvalues span `ℂ^α`); `card_roots_toFinset` (a separable `χ_M` has `|α|` distinct
  complex roots); `charpoly_separable_of_irreducible`; `proper_of_span`.
* **(A) Contraction data.**  `contractionData_of_eigenrows` (eigen-row form: eigenvalues
  `μ k` pairwise distinct, one row real, the others with `‖μ k‖ ≤ ρ < 1`; on three letters:
  `β, λ₂, λ₃`); **`exists_eigenfunctionals_of_separable`** (separable `χ_M` over `ℂ`, a
  nonzero real left eigen-row for `β`, (R): there are contracted eigenfunctionals `η i` with
  eigenvalues the roots other than `β`, and `ν v = ∑ i, ‖η i v‖` is contraction data, through
  `Psc.GeometricF.contractionData_of_eigenfunctionals`); `exists_contractionData_of_separable`;
  **`exists_contractionData_of_pisot`** ((I), (E), (R)).
* **The Pisot hypothesis.**  `pisot_roots_of_isPisot` ((I), (E), `IsPisot β` give (R));
  `perron_eq_pisot_root` and `pisot_roots_of_pisot_root` (the sieve form gives `r = β`,
  `1 < r` and (R) for every positive left eigen-row; any alphabet, no primitivity).
* **(B) `β > 1`.**  Bound to `Psc.BPrimeCore.one_lt_perron` ((P), at least two letters, (E));
  in the other two forms it is part of the hypothesis.  `fc1_hypotheses_of_primitive_pisot`
  ((P), (I), (E), (R): `LengthData`, `1 < β` and `ContractionData`);
  `exists_fc1_data_of_primitive_pisot` (the sieve form with the Perron row produced).
* **(C) Theorem FC1 on the standing class.**  **`fc1_equivalence_of_primitive_pisot`** ((P),
  at least two letters, (I), (E), (R), (F): `σ` has a strict system iff some pair of distinct
  `g`-periodic letters has no left strong-coincidence witness iff left strong coincidence
  fails for some pair) and **`fc1_pip3`** (three letters); `fc1_equivalence_of_pisot` ((I),
  (E), `β > 1`, (R), (F)), `fc1_equivalence_of_isPisot`, `fc1_equivalence_of_pisot_root`;
  items (1), (2): **`fc1_inclusion_gap_of_pisot`** ((I), (E), `β > 0`, (R), (F)) and
  `fc1_inclusion_gap_of_primitive_pisot`; item (3): `fc1_strictSystem_of_pisot`.
* **Lemma 3 (1), (3), abstract form.**  `step_bound_proper`, `stepN_bound_pow`
  (`ν(fⁿ(x)) ≤ ρⁿ ν(x) + (1 − ρⁿ) D / (1 − ρ)`, `D` over proper prefixes), **`periodic_bound`**
  (an `f`-periodic state has `ν ≤ D / (1 − ρ)`), `periodicStates_finite` and
  `periodicStates_finite_of_pisot` (finitely many `f`-periodic states).
* **Non-vacuity.**  Tribonacci (`Psc.Descendants.tribSubst`, PIP3): `trib_fc1_hypotheses`
  ((P), (I), (E), (R), `IsPisot β`, `LengthData`, `β > 1`, `ContractionData`: everything
  except (F)), `trib_fc1_of_propertyF`, `trib_fc1_statements` (with no hypothesis, the three
  statements of the equivalence are all false there, so it does not assert anything false).
  Fibonacci (`Psc.Descendants.fibSubst`, two letters): `fib_propertyF` ((F) for every
  positive left eigen-row: a periodic state has `|Y| ≤ β`, the box has the lattice points
  `0, (0, 1), (1, −1)`, and all reach a vertex state), `fib_pisot_roots`,
  **`fib_fc1_hypotheses`** (every hypothesis of `fc1_equivalence_of_primitive_pisot` holds),
  `fib_fc1`, `fib_fc1_statements` (the three statements are all false there).
* **Negative control.**  `carrier_not_pisot_roots`: on the reducible strict control
  `10/102/211` (`Psc.StrictSystem.carrierSubst`) no positive left eigen-row satisfies
  "separable and (R)", by `Psc.GeometricF.carrier_not_contractionData`.
* **Bridges.**  `pvec_eq_parikhCast` (`Psc.GeometricF.pvec` is `Psc.BPrimeCore.parikhCast` at
  `ℤ`), `incZ_eq_degree2Sector` (`Psc.GeometricF.incZ` is `Psc.Degree2Sector.incZ`); both
  `rfl`.  `Psc.OccurrenceGraph.incZ` has the same body but is not imported here.

**Hypotheses and where they enter.**
* (I): only through (i) separability of `χ_M` over `ℂ`, i.e. `|α|` pairwise distinct roots,
  which makes the eigen-rows a basis and gives properness; (ii) a nonempty alphabet;
  (iii) in the `IsPisot` form, `χ_M` is the minimal polynomial of `β`.  The core
  `exists_eigenfunctionals_of_separable` assumes separability instead.
* The Pisot hypothesis: `ρ < 1`.  It must hold for every root of `χ_M` other than `β`; for a
  reducible `χ_M` this is more than "`β` is a Pisot number" (`carrier_not_pisot_roots`).
* (E): `L = lenHom ℓ`; `ℓ` real makes `|ℓ·v|` the first proper coordinate; `ℓ > 0` is
  `LengthData.pos`.  The theorems hold for every positive left eigen-row; that it is unique
  up to a positive factor under (P) is not used.
* (P): only the existence of `ℓ` and, with at least two letters, `β > 1`.  It is not a
  hypothesis of (A), nor of the forms that assume `β > 1` or `β > 0`.
* (F): the remaining hypothesis.  Three letters are not used; `fc1_pip3` is the
  specialisation.

**Deviations from the note.**  Any finite alphabet.  `ν` is the sum `∑ |η_i·v|` over all
roots other than `β` (the note's `max` works as well).  Lemma 1 (2) is proved as properness on
`ℤ^α` (the form `ContractionData.proper` consumes), by expressing each coordinate of `v`
through the eigen-coordinates.  Lemma 1 (1) and (3) are not needed.

**Not proved here.**  Property (F) for any substitution on three letters: no PIP3 specimen is
shown to satisfy all hypotheses of `fc1_pip3` at once (Tribonacci: all but (F); the complete
instance is Fibonacci, on two letters).  No irreducible Pisot instance with a strict system (the
open statement C4 is that PIP3 has none): on Tribonacci and Fibonacci the three statements of
the equivalence are false; they are true on the Thue–Morse control (`Psc.GeometricF.tm_fc1`),
which is not Pisot.  The Pisot hypothesis for any specimen other than Tribonacci and Fibonacci.
Whether `IsPisot β` holds on `10/102/211` (on paper its `β = 1 + √3` is a Pisot number; the
machine-checked control is the root form).  Lemma 1 (1), (3); the explicit bound "`N₀` is less
than the number of states of the box"; Lemma 4; Lemma 5; the converse of the Powers paragraph;
Theorems FC2, P, FC3, N, Fork.  Universal C4 is open: Theorem FC1 is an equivalence and excludes
no strict system.
-/
import PscVerif.GeometricFStrict
import PscVerif.BPrime

namespace Psc.GeometricFPisot

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.BPrimeBinding Psc.GeometricF
open Psc.StrictSystem (StrictSystem StrongCoincidenceWitness)

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### Complex functionals on integer vectors -/

/-- The additive functional `v ↦ w·v` on integer vectors, for a complex row `w`. -/
def dotHom (w : α → ℂ) : (α → ℤ) →+ ℂ where
  toFun v := ∑ a, w a * (v a : ℂ)
  map_zero' := by simp
  map_add' v v' := by simp [mul_add, Finset.sum_add_distrib]

omit [DecidableEq α] in
theorem dotHom_apply (w : α → ℂ) (v : α → ℤ) : dotHom w v = ∑ a, w a * (v a : ℂ) := rfl

/-- A left eigen-row `w M = z w` of the complex incidence matrix is an eigenfunctional of the
integer incidence action: `w·(M v) = z (w·v)`. -/
theorem dotHom_mulVec {s : α → List α} {w : α → ℂ} {z : ℂ}
    (h : w ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = z • w) (v : α → ℤ) :
    dotHom w (incZ s *ᵥ v) = z * dotHom w v := by
  have hc : ∀ c, ∑ a, w a * ((inc s a c : ℕ) : ℂ) = z * w c := fun c => by
    have := congrFun h c
    simpa [Matrix.vecMul, dotProduct] using this
  simp only [dotHom_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_assoc, ← hc c, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => by ring

/-- A real left eigen-row, read over `ℂ`. -/
theorem ofReal_left_eigen {s : α → List α} {ℓ : α → ℝ} {β : ℝ}
    (h : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    (fun a => (ℓ a : ℂ)) ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = (β : ℂ) • fun a => (ℓ a : ℂ) := by
  funext c
  have := congrFun h c
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  exact_mod_cast this

omit [DecidableEq α] in
/-- The complexified length functional is the length functional. -/
theorem dotHom_ofReal (ℓ : α → ℝ) (v : α → ℤ) :
    dotHom (fun a => (ℓ a : ℂ)) v = ((lenHom ℓ v : ℝ) : ℂ) := by
  simp [dotHom_apply, lenHom_apply]

/-! ### Properness: Lemma 1 (2) -/

/-- **Properness from a spanning family of functionals.**  If the rows `W k` span `ℂ^α`, then
only finitely many integer vectors have all the coordinates `W k · v` bounded by `B`: each
`v_a` is a fixed linear combination of the `W k · v`. -/
theorem finite_of_span_eq_top {κ : Type*} [Fintype κ] (W : κ → α → ℂ)
    (hW : Submodule.span ℂ (Set.range W) = ⊤) (B : ℝ) :
    {v : α → ℤ | ∀ k, ‖dotHom (W k) v‖ ≤ B}.Finite := by
  have hc : ∀ a : α, ∃ c : κ → ℂ, ∑ k, c k • W k = Pi.single a 1 := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (by rw [hW]; exact Submodule.mem_top)
  choose c hc using hc
  refine (Set.Finite.pi fun a : α =>
    Set.finite_Icc (-⌈(∑ k, ‖c a k‖) * B⌉) ⌈(∑ k, ‖c a k‖) * B⌉).subset ?_
  intro v hv a _
  have e : ((v a : ℤ) : ℂ) = ∑ k, c a k * dotHom (W k) v := by
    have h1 : ((v a : ℤ) : ℂ) = ∑ b, (Pi.single a (1 : ℂ) : α → ℂ) b * (v b : ℂ) := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [h1, ← hc a]
    simp only [dotHom_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
  have hn : |((v a : ℤ) : ℝ)| ≤ (∑ k, ‖c a k‖) * B := by
    have h2 : ‖((v a : ℤ) : ℂ)‖ ≤ (∑ k, ‖c a k‖) * B := by
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hv k) (norm_nonneg _)
    rwa [Complex.norm_intCast] at h2
  rw [abs_le] at hn
  have hceil := Int.le_ceil ((∑ k, ‖c a k‖) * B)
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · have : ((-⌈(∑ k, ‖c a k‖) * B⌉ : ℤ) : ℝ) ≤ ((v a : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have : ((v a : ℤ) : ℝ) ≤ ((⌈(∑ k, ‖c a k‖) * B⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this

omit [DecidableEq α] in
/-- **Left eigen-rows for pairwise distinct eigenvalues, as many as letters, span `ℂ^α`**
(eigenvectors for distinct eigenvalues are linearly independent). -/
theorem span_eq_top_of_left_eigen {κ : Type*} [Fintype κ] (A : Matrix α α ℂ) (μ : κ → ℂ)
    (hμ : Function.Injective μ) (W : κ → α → ℂ) (hW0 : ∀ k, W k ≠ 0)
    (hW : ∀ k, W k ᵥ* A = μ k • W k) (hcard : Fintype.card κ = Fintype.card α) :
    Submodule.span ℂ (Set.range W) = ⊤ := by
  have hli : LinearIndependent ℂ W :=
    Module.End.eigenvectors_linearIndependent' A.vecMulLinear μ hμ W fun k =>
      ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.vecMulLinear_apply]; exact hW k), hW0 k⟩
  exact hli.span_eq_top_of_card_eq_finrank' (by rw [hcard, Module.finrank_fintype_fun_eq_card])

/-- A separable characteristic polynomial over `ℂ` has as many distinct roots as letters. -/
theorem card_roots_toFinset (A : Matrix α α ℂ) (hsep : A.charpoly.Separable) :
    A.charpoly.roots.toFinset.card = Fintype.card α := by
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    charpoly_natDegree_eq_dim]

/-- An irreducible `χ_M` over `ℚ` is separable over `ℂ`. -/
theorem charpoly_separable_of_irreducible (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) :
    ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.Separable := by
  have e : ((inc s).map (Nat.cast : ℕ → ℚ)).map (algebraMap ℚ ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by
    ext; simp
  rw [← e, Matrix.charpoly_map]
  exact hirr.separable.map

/-- An irreducible `χ_M` forces a nonempty alphabet (`χ = 1` on the empty one). -/
theorem nonempty_of_irreducible (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  rw [Matrix.charpoly_isEmpty] at hirr
  exact not_irreducible_one hirr

/-! ### (A) Contraction data from the spectral hypotheses -/

/-- **Properness of the eigen-coordinates** (Lemma 1 (2) of the note).  If the rows `W k`
span `ℂ^α` and `W k₀` is the real row `ℓ`, then for all real `a, b` only finitely many integer
vectors `v` have `|ℓ·v| ≤ a` and `∑_{k ≠ k₀} |W k · v| ≤ b`. -/
theorem proper_of_span {κ : Type*} [Fintype κ] (W : κ → α → ℂ)
    (hW : Submodule.span ℂ (Set.range W) = ⊤) {ℓ : α → ℝ} (k₀ : κ)
    (hk₀ : W k₀ = fun a => (ℓ a : ℂ)) [Fintype {k : κ // k ≠ k₀}] (a b : ℝ) :
    {v : α → ℤ | |lenHom ℓ v| ≤ a ∧
      ∑ i : {k : κ // k ≠ k₀}, ‖dotHom (W i.1) v‖ ≤ b}.Finite := by
  refine (finite_of_span_eq_top W hW (|a| + |b|)).subset ?_
  rintro v ⟨hv1, hv2⟩ k
  by_cases h : k = k₀
  · rw [h, hk₀, dotHom_ofReal, Complex.norm_real, Real.norm_eq_abs]
    linarith [le_abs_self a, abs_nonneg b]
  · have h1 : ‖dotHom (W k) v‖ ≤ ∑ i : {k : κ // k ≠ k₀}, ‖dotHom (W i.1) v‖ :=
      Finset.single_le_sum (f := fun i : {k : κ // k ≠ k₀} => ‖dotHom (W i.1) v‖)
        (a := ⟨k, h⟩) (fun i _ => norm_nonneg _) (Finset.mem_univ _)
    linarith [le_abs_self b, abs_nonneg a]

/-- **(A), eigen-row form.**  Let `W k` (`k : κ`, `|κ| = |α|`) be nonzero left eigen-rows of
the complex incidence matrix for pairwise distinct eigenvalues `μ k`, let `W k₀` be a real row
`ℓ`, and let `‖μ k‖ ≤ ρ < 1` for every `k ≠ k₀`.  Then `ν v = ∑_{k ≠ k₀} |W k · v|` and `ρ`
are contraction data for the length functional `v ↦ ℓ·v`.  On three letters this is the
statement for eigenvalues `β, λ₂, λ₃` with `|λ₂|, |λ₃| < 1`; the eigen-rows are a basis of
`ℂ^α` because the eigenvalues are pairwise distinct (`span_eq_top_of_left_eigen`). -/
theorem contractionData_of_eigenrows {κ : Type*} [Fintype κ] (s : α → List α) (μ : κ → ℂ)
    (hμ : Function.Injective μ) (W : κ → α → ℂ) (hW0 : ∀ k, W k ≠ 0)
    (hWA : ∀ k, W k ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = μ k • W k)
    (hcard : Fintype.card κ = Fintype.card α) {ℓ : α → ℝ} (k₀ : κ)
    (hk₀ : W k₀ = fun a => (ℓ a : ℂ)) [Fintype {k : κ // k ≠ k₀}] {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hlam : ∀ k, k ≠ k₀ → ‖μ k‖ ≤ ρ) :
    ContractionData s (lenHom ℓ) (fun v => ∑ i : {k : κ // k ≠ k₀}, ‖dotHom (W i.1) v‖) ρ :=
  contractionData_of_eigenfunctionals (fun i : {k : κ // k ≠ k₀} => dotHom (W i.1))
    (fun i => μ i.1) (fun i v => dotHom_mulVec (hWA i.1) v) hρ0 hρ1 (fun i => hlam i.1 i.2)
    (proper_of_span W (span_eq_top_of_left_eigen _ μ hμ W hW0 hWA hcard) k₀ hk₀)

/-- A finite family of reals `< 1` is bounded by one `ρ` with `0 ≤ ρ < 1`. -/
theorem exists_bound_lt_one {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, f i < 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ i, f i ≤ ρ := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact ⟨0, le_rfl, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
    exact ⟨max (f i₀) 0, le_max_right _ _, max_lt (hf i₀) one_pos,
      fun i => (hi₀ i).trans (le_max_left _ _)⟩

/-- **(A), the core: contracted eigenfunctionals and contraction data from the spectrum.**
Let the complex characteristic polynomial of the incidence matrix be separable (pairwise
distinct eigenvalues), let `ℓ ≠ 0` be a real left eigen-row for `β`, and let every other
complex root of `χ_M` lie in the open unit disc.  Then there are finitely many additive
functionals `η i` on integer vectors with `η i (M v) = lam i * η i v`, each `lam i` a root of
`χ_M` other than `β`, all of modulus at most some `ρ < 1`, such that
`ν v = ∑ i, ‖η i v‖` and `ρ` are contraction data for the length functional `v ↦ ℓ·v`.

Properness (Lemma 1 (2) of the note) is where distinctness enters: `ℓ` and one left eigen-row
for each other root are `|α|` eigen-rows for pairwise distinct eigenvalues, hence a basis of
`ℂ^α`, and `finite_of_span_eq_top` applies. -/
theorem exists_eigenfunctionals_of_separable (s : α → List α)
    (hsep : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.Separable) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (ι : Type) (_ : Fintype ι) (η : ι → (α → ℤ) →+ ℂ) (lam : ι → ℂ) (ρ : ℝ),
      (∀ i v, η i (incZ s *ᵥ v) = lam i * η i v) ∧
      (∀ i, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval (lam i) = 0 ∧ lam i ≠ β) ∧
      (∀ i, ‖lam i‖ ≤ ρ) ∧
      ContractionData s (lenHom ℓ) (fun v => ∑ i, ‖η i v‖) ρ := by
  classical
  have hp0 : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  -- the set of roots: as many as letters
  obtain ⟨R, hmem, hcard⟩ : ∃ R : Finset ℂ,
      (∀ z : ℂ, z ∈ R ↔ ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) ∧
        R.card = Fintype.card α :=
    ⟨_, fun z => by rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def],
      card_roots_toFinset _ hsep⟩
  -- the Perron row over `ℂ`
  have hℓc0 : (fun a => (ℓ a : ℂ)) ≠ 0 := fun h => hℓ0 (funext fun a => by
    have := congrFun h a
    simpa using this)
  have hℓcA := ofReal_left_eigen hℓM
  have hβroot : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval (β : ℂ) = 0 :=
    Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ _ _ hℓc0 hℓcA
  -- a left eigen-row for every root
  have hq : ∀ z : R, ∃ q : α → ℂ, q ≠ 0 ∧
      q ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = (z : ℂ) • q := fun z => by
    obtain ⟨q, hq0, hq⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot
      ((inc s).map (Nat.cast : ℕ → ℂ))ᵀ (z : ℂ)
      (by rw [Matrix.charpoly_transpose]; exact (hmem z).1 z.2)
    exact ⟨q, hq0, by rw [← Matrix.mulVec_transpose]; exact hq⟩
  choose q hq0 hqA using hq
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : R, (k₀ : ℂ) = β := ⟨⟨β, (hmem _).2 hβroot⟩, rfl⟩
  have hW0 : ∀ k, Function.update q k₀ (fun a => (ℓ a : ℂ)) k ≠ 0 := fun k => by
    by_cases h : k = k₀
    · rw [h, Function.update_self]
      exact hℓc0
    · rw [Function.update_of_ne h]
      exact hq0 k
  have hWA : ∀ k : R, Function.update q k₀ (fun a => (ℓ a : ℂ)) k ᵥ*
      (inc s).map (Nat.cast : ℕ → ℂ) = (k : ℂ) • Function.update q k₀ (fun a => (ℓ a : ℂ)) k :=
    fun k => by
      by_cases h : k = k₀
      · rw [h, Function.update_self, hk₀]
        exact hℓcA
      · rw [Function.update_of_ne h]
        exact hqA k
  have hne : ∀ i : {k : R // k ≠ k₀}, ((i.1 : ℂ)) ≠ β := fun i h =>
    i.2 (Subtype.ext (h.trans hk₀.symm))
  obtain ⟨ρ, hρ0, hρ1, hlam⟩ := exists_bound_lt_one (fun i : {k : R // k ≠ k₀} => ‖(i.1 : ℂ)‖)
    fun i => hpisot _ ((hmem _).1 i.1.2) (hne i)
  exact ⟨{k : R // k ≠ k₀}, inferInstance,
    fun i => dotHom (Function.update q k₀ (fun a => (ℓ a : ℂ)) i.1),
    fun i => (i.1 : ℂ), ρ, fun i v => dotHom_mulVec (hWA i.1) v,
    fun i => ⟨(hmem _).1 i.1.2, hne i⟩, hlam,
    contractionData_of_eigenrows s (fun k : R => (k : ℂ)) Subtype.val_injective _ hW0 hWA
      (by rw [Fintype.card_coe]; exact hcard) k₀ (Function.update_self ..)
      hρ0 hρ1 fun k hk => hlam ⟨k, hk⟩⟩

/-- **(A), separable form**: contraction data exist. -/
theorem exists_contractionData_of_separable (s : α → List α)
    (hsep : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.Separable) {β : ℝ} {ℓ : α → ℝ}
    (hℓ0 : ℓ ≠ 0) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (ν : (α → ℤ) → ℝ) (ρ : ℝ), ContractionData s (lenHom ℓ) ν ρ := by
  obtain ⟨ι, _, η, lam, ρ, -, -, -, hc⟩ :=
    exists_eigenfunctionals_of_separable s hsep hℓ0 hℓM hpisot
  exact ⟨_, ρ, hc⟩

/-- **(A) on the standing class.**  Let `χ_M` be irreducible over `ℚ`, let `ℓ > 0` be a left
eigen-row of the incidence matrix for `β` (the Perron row), and let every complex root of
`χ_M` other than `β` lie in the open unit disc (the Pisot hypothesis, in the form of the
conclusion of `Psc.BPrime.bprime_cubic`).  Then `ContractionData s (lenHom ℓ) ν ρ` holds for
some `ν`, `ρ`.  Primitivity is not used. -/
theorem exists_contractionData_of_pisot (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (ν : (α → ℤ) → ℝ) (ρ : ℝ), ContractionData s (lenHom ℓ) ν ρ := by
  have := nonempty_of_irreducible s hirr
  exact exists_contractionData_of_separable s (charpoly_separable_of_irreducible s hirr)
    (fun h => (hℓ (Classical.arbitrary α)).ne' (congrFun h _)) hℓM hpisot

/-! ### The Pisot hypothesis in the repository's other two forms -/

/-- **From `Psc.BPrime.IsPisot`.**  With `χ_M` irreducible, the Perron root `β` of a positive
left eigen-row is a root of `χ_M`, `χ_M` is its minimal polynomial
(`Psc.BPrime.minpoly_eq_charpoly`), and `IsPisot β` puts every other complex root of `χ_M`
in the open unit disc. -/
theorem pisot_roots_of_isPisot (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hP : Psc.BPrime.IsPisot β) :
    ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β → ‖z‖ < 1 := by
  have := nonempty_of_irreducible s hirr
  have hroot := Psc.BPrime.isRoot_of_pos_left_eigen s hℓ hℓM
  intro z hz hzβ
  refine hP.2.2 z ?_ hzβ
  rw [Psc.BPrime.minpoly_eq_charpoly s hirr hroot, Psc.BPrime.aeval_charpoly]
  exact hz

/-- **The Perron root is the Pisot root**, on any alphabet (three letters:
`Psc.Degree4Floor.perron_eq_pisot`).  If `β` is a complex root of `χ_M` with `1 < ‖β‖` and
every other complex root has modulus `< 1` (the hypotheses `hβ`, `hβ1`, `hpisot` of
`Psc.Degree4Floor.sieve4_pisot` and `Psc.Degree5Completion`), and `ℓ > 0` is a left eigen-row
for the real `r`, then `r = β` and `1 < r`.  No primitivity: `‖β‖ ≤ r` is
`Psc.PerronExistence.norm_le_of_pos_left_eigen`. -/
theorem perron_eq_pisot_root (s : α → List α) {r : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1) : (r : ℂ) = β ∧ 1 < r := by
  have hne : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Matrix.charpoly_isEmpty] at hβ
    simp at hβ
  have hc : ((inc s).map (Nat.cast : ℕ → ℝ)).map ((↑) : ℝ → ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by
    ext; simp
  have hN : ∀ a c, 0 ≤ (inc s).map (Nat.cast : ℕ → ℝ) a c := fun a c => Nat.cast_nonneg _
  have hle : ‖β‖ ≤ r :=
    Psc.PerronExistence.norm_le_of_pos_left_eigen _ hN ℓ hℓ r hℓM β
      (by rw [hc, ← Psc.BPrime.aeval_charpoly]; exact hβ)
  have hr : aeval (r : ℂ) ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 := by
    rw [Psc.BPrime.aeval_charpoly, ← hc]
    exact Psc.PerronExistence.isRoot_ofReal_of_left_eigen _ ℓ
      (fun h => (hℓ (Classical.arbitrary α)).ne' (congrFun h _)) r hℓM
  refine ⟨?_, lt_of_lt_of_le hβ1 hle⟩
  by_contra hne'
  have h1 := hpisot _ hr hne'
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  linarith [le_abs_self r]

/-- **From the sieve form to the root form.**  Under the hypotheses of
`perron_eq_pisot_root`, the eigenvalue `r` of a positive left eigen-row satisfies `1 < r` and
every complex root of `χ_M` other than `r` has modulus `< 1`. -/
theorem pisot_roots_of_pisot_root (s : α → List α) {r : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1) :
    1 < r ∧ ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ r →
      ‖z‖ < 1 := by
  obtain ⟨hr, hr1⟩ := perron_eq_pisot_root s hℓ hℓM hβ hβ1 hpisot
  refine ⟨hr1, fun z hz hzr => ?_⟩
  rw [hr] at hzr
  exact hpisot z (by rw [Psc.BPrime.aeval_charpoly]; exact hz) hzr

/-! ### (B) and (C): Theorem FC1 on the standing class -/

section Instance

variable {s : α → List α} {β : ℝ} {ℓ : α → ℝ}

/-- **(A) and (B): the abstract hypotheses of Theorem FC1 hold on the standing class.**  For
a primitive substitution on at least two letters with `χ_M` irreducible over `ℚ`, Perron row
`ℓ > 0`, `ℓ M = β ℓ`, and every other complex root of `χ_M` in the open unit disc:
`LengthData`, `1 < β` (`Psc.BPrimeCore.one_lt_perron`) and `ContractionData` all hold for the
length functional `v ↦ ℓ·v`. -/
theorem fc1_hypotheses_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    LengthData s (lenHom ℓ) β ∧ 1 < β ∧
      ∃ (ν : (α → ℤ) → ℝ) (ρ : ℝ), ContractionData s (lenHom ℓ) ν ρ := by
  have hβ := Psc.BPrimeCore.one_lt_perron s hprim hℓ hℓM
  exact ⟨lengthData_of_left_eigen (by linarith) hℓ hℓM, hβ,
    exists_contractionData_of_pisot s hirr hℓ hℓM hpisot⟩

/-- **(A) and (B) in the hypothesis form of the sieve theorems, with the Perron row
produced.**  Let `σ` be primitive with `χ_M` irreducible over `ℚ`, and let `β` be a complex
root of `χ_M` with `1 < ‖β‖` and every other complex root of modulus `< 1` (the standing
hypotheses of `Psc.Degree4Floor.sieve4_pisot`).  Then there are a real `r` with `r = β`, a
left eigen-row `ℓ > 0` for `r`, and `ν`, `ρ` such that `LengthData s (lenHom ℓ) r`, `1 < r` and
`ContractionData s (lenHom ℓ) ν ρ` hold: every abstract hypothesis of
`Psc.GeometricF.fc1_equivalence_of_contraction` except `PropertyF`. -/
theorem exists_fc1_data_of_primitive_pisot
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1) :
    ∃ (r : ℝ) (ℓ : α → ℝ) (ν : (α → ℤ) → ℝ) (ρ : ℝ), (r : ℂ) = β ∧ (∀ a, 0 < ℓ a) ∧
      ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ ∧
      LengthData s (lenHom ℓ) r ∧ 1 < r ∧ ContractionData s (lenHom ℓ) ν ρ := by
  obtain ⟨r, hr0, ℓ, hℓ, hℓM⟩ := Psc.PerronExistence.exists_pos_left_eigen_inc s hprim
  obtain ⟨hr1, hroots⟩ := pisot_roots_of_pisot_root s hℓ hℓM hβ hβ1 hpisot
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hroots
  exact ⟨r, ℓ, ν, ρ, (perron_eq_pisot_root s hℓ hℓM hβ hβ1 hpisot).1, hℓ, hℓM,
    lengthData_of_left_eigen hr0 hℓ hℓM, hr1, hc⟩

/-- **Theorem FC1 (the equivalences) for an irreducible Pisot incidence matrix.**  Let `χ_M`
be irreducible over `ℚ`, `ℓ > 0` a left eigen-row for `β > 1`, every other complex root of
`χ_M` of modulus `< 1`, and let property (F) hold for the tile lengths `ℓ`.  Then `σ` has a
strict system iff some pair of distinct `g`-periodic letters has no left strong-coincidence
witness iff left strong coincidence fails for some pair of distinct letters. -/
theorem fc1_equivalence_of_pisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') := by
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hpisot
  exact fc1_equivalence_of_contraction (lengthData_of_left_eigen (by linarith) hℓ hℓM) hβ hc hF

/-- **Theorem FC1 (the equivalences) on the standing class**, in the hypothesis form of
`Psc.BPrime`: `σ` primitive on at least two letters, `χ_M` irreducible over `ℚ`, `ℓ > 0` with
`ℓ M = β ℓ`, every complex root of `χ_M` other than `β` in the open unit disc, and
property (F) for the tile lengths `ℓ`.  No abstract hypothesis is left: `β > 1` is
`Psc.BPrimeCore.one_lt_perron` and the contraction data are
`exists_contractionData_of_pisot`. -/
theorem fc1_equivalence_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') :=
  fc1_equivalence_of_pisot hirr hℓ hℓM (Psc.BPrimeCore.one_lt_perron s hprim hℓ hℓM) hpisot hF

/-- **Theorem FC1 (the equivalences) with `Psc.BPrime.IsPisot`**: `χ_M` irreducible over
`ℚ`, `ℓ > 0` with `ℓ M = β ℓ`, `β` a Pisot number, and property (F).  Irreducibility cannot
be dropped in this form: `IsPisot β` constrains only the conjugates of `β`. -/
theorem fc1_equivalence_of_isPisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hP : Psc.BPrime.IsPisot β) (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') :=
  fc1_equivalence_of_pisot hirr hℓ hℓM hP.1 (pisot_roots_of_isPisot s hirr hℓ hℓM hP) hF

/-- **Theorem FC1 (the equivalences) in the hypothesis form of the sieve theorems**
(`Psc.Degree4Floor.sieve4_pisot`, `Psc.Degree5Completion`): `χ_M` irreducible over `ℚ`, a
complex root `β` with `1 < ‖β‖`, every other complex root of modulus `< 1`; then for every
positive left eigen-row `ℓ` (eigenvalue `r`, which is `β`: `perron_eq_pisot_root`) with
property (F) the equivalences hold. -/
theorem fc1_equivalence_of_pisot_root
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℂ}
    (hβ : aeval β ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0) (hβ1 : 1 < ‖β‖)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 → z ≠ β →
      ‖z‖ < 1)
    {r : ℝ} (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = r • ℓ)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') := by
  obtain ⟨hr1, hroots⟩ := pisot_roots_of_pisot_root s hℓ hℓM hβ hβ1 hpisot
  exact fc1_equivalence_of_pisot hirr hℓ hℓM hr1 hroots hF

/-- **Theorem FC1, items (1) and (2), for an irreducible Pisot incidence matrix**: `χ_M`
irreducible over `ℚ`, `ℓ > 0` with `ℓ M = β ℓ`, `β > 0`, every other complex root of `χ_M` of
modulus `< 1`, and property (F).  For any two `σ^m`-fixed words, `m ≥ 1`, there is `N` with
`M^{mN}(V_X ∪ V_{X'}) ⊆ V_X ∩ V_{X'}`, and every window `(t, t + β^{mN} ℓ_max]`, `t ≥ 0`,
holds the position of a common vertex (`ℓ_max ≥ max_a ℓ_a`).  `β > 1` is not needed here. -/
theorem fc1_inclusion_gap_of_pisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 0 < β)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X') :
    ∃ N, (∀ y ∈ vertexSet X ∪ vertexSet X',
        incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X') ∧
      ∀ ℓmax : ℝ, (∀ a, ℓ a ≤ ℓmax) → ∀ t : ℝ, 0 ≤ t →
        ∃ z ∈ vertexSet X ∩ vertexSet X',
          t < lenHom ℓ z ∧ lenHom ℓ z ≤ t + β ^ (m * N) * ℓmax := by
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hpisot
  obtain ⟨N, h1, h2⟩ := fc1_inclusion_gap_of_contraction (lengthData_of_left_eigen hβ hℓ hℓM)
    hc hF hm hX hX'
  exact ⟨N, h1, fun ℓmax hmax t ht =>
    h2 ℓmax (fun a => by rw [lenHom_single]; exact hmax a) t ht⟩

/-- **Theorem FC1, item (3), for an irreducible Pisot incidence matrix**: under the
hypotheses of `fc1_equivalence_of_pisot`, if the first letters of two `σ^m`-fixed words have
no left strong-coincidence witness, the blocks of `(X, X')` between consecutive common
vertices form a strict system for `σ^m`, and `σ` has a strict system. -/
theorem fc1_strictSystem_of_pisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ : 1 < β)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    (hnw : ¬ StrongCoincidenceWitness s (X 0) (X' 0)) :
    (∃ C : Finset (List α × List α), (↑C : Set (List α × List α)) = cutBlocks X X' ∧
      StrictSystem (power s m) C) ∧ ∃ C : Finset (List α × List α), StrictSystem s C := by
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hpisot
  have hL := lengthData_of_left_eigen (lt_trans one_pos hβ) hℓ hℓM
  exact fc1_strictSystem hL hβ hm hX hX' (relStates_finite_of_contraction hL hc hm hX hX')
    (fun _ hx => reaches_vertex_of_propertyF hL hc hF (relStates_isState hx)) hnw

/-- **Theorem FC1, items (1) and (2), on the standing class** (primitive, at least two
letters, `χ_M` irreducible, every root other than the Perron root in the open unit disc,
property (F)). -/
theorem fc1_inclusion_gap_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X') :
    ∃ N, (∀ y ∈ vertexSet X ∪ vertexSet X',
        incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X') ∧
      ∀ ℓmax : ℝ, (∀ a, ℓ a ≤ ℓmax) → ∀ t : ℝ, 0 ≤ t →
        ∃ z ∈ vertexSet X ∩ vertexSet X',
          t < lenHom ℓ z ∧ lenHom ℓ z ≤ t + β ^ (m * N) * ℓmax :=
  fc1_inclusion_gap_of_pisot hirr hℓ hℓM
    (lt_trans one_pos (Psc.BPrimeCore.one_lt_perron s hprim hℓ hℓM)) hpisot hF hm hX hX'

end Instance

/-- **Theorem FC1 (the equivalences) on PIP3** (three letters): `σ` primitive, `χ_M` irreducible
over `ℚ`, `ℓ > 0` with `ℓ M = β ℓ`, every complex root of `χ_M` other than `β` in the open unit
disc, and (F) for the lengths `ℓ`.  Then `σ` has a strict system iff some two distinct
`g`-periodic letters have no left strong-coincidence witness iff some two distinct letters have
none.  Items (1), (2): `fc1_inclusion_gap_of_primitive_pisot`; (3): `fc1_strictSystem_of_pisot`. -/
theorem fc1_pip3 {s : Fin 3 → List (Fin 3)} {β : ℝ} {ℓ : Fin 3 → ℝ}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') :=
  fc1_equivalence_of_primitive_pisot hprim hirr hℓ hℓM hpisot hF

/-! ### Lemma 3 (1), (3): the box of the periodic states -/

section Box

variable {s : α → List α} {L : (α → ℤ) →+ ℝ} {ν : (α → ℤ) → ℝ} {ρ D : ℝ}

/-- **Lemma 3 (1)**, with `D` a bound over the proper prefixes of the images only (the
note's `D`): `ν(f(x)) ≤ ρ ν(x) + D`. -/
theorem step_bound_proper (hc : ContractionData s L ν ρ)
    (hD : ∀ a P b S, s a = P ++ b :: S → ν (pvec P) ≤ D) {x y : α × (α → ℤ)}
    (h : Step s L x y) : ν y.2 ≤ ρ * ν x.2 + D := by
  obtain ⟨P, S, hP, hy, -⟩ := h
  rw [hy, sub_eq_add_neg]
  refine (hc.add_le _ _).trans (add_le_add (hc.contract _) ?_)
  rw [hc.neg]
  exact hD x.1 P y.1 S hP

/-- **Lemma 3 (1)**, the geometric form: `ν(fⁿ(x)) ≤ ρⁿ ν(x) + (1 − ρⁿ) B` with
`B = D / (1 − ρ)`. -/
theorem stepN_bound_pow (hc : ContractionData s L ν ρ)
    (hD : ∀ a P b S, s a = P ++ b :: S → ν (pvec P) ≤ D) {x : α × (α → ℤ)} :
    ∀ (n : ℕ) {y : α × (α → ℤ)}, StepN s L n x y →
      ν y.2 ≤ ρ ^ n * ν x.2 + (1 - ρ ^ n) * (D / (1 - ρ))
  | 0, _, h => by rw [← h]; simp
  | n + 1, y, ⟨z, hz, hy⟩ => by
    have ih := stepN_bound_pow hc hD n hz
    have hs := step_bound_proper hc hD hy
    have h1ρ : (1 - ρ) ≠ 0 := by linarith [hc.rho_lt_one]
    have hB : D = D / (1 - ρ) * (1 - ρ) := by field_simp
    have h3 := mul_le_mul_of_nonneg_left ih hc.rho_nonneg
    generalize D / (1 - ρ) = B at ih hB h3 ⊢
    rw [pow_succ]
    nlinarith

/-- **Lemma 3 (3)**: every `f`-periodic state lies in the box `ν ≤ D / (1 − ρ)`. -/
theorem periodic_bound (hc : ContractionData s L ν ρ)
    (hD : ∀ a P b S, s a = P ++ b :: S → ν (pvec P) ≤ D) {x : α × (α → ℤ)} {k : ℕ}
    (hk : 1 ≤ k) (h : StepN s L k x x) : ν x.2 ≤ D / (1 - ρ) := by
  have hb := stepN_bound_pow hc hD k h
  have hp : ρ ^ k < 1 := pow_lt_one₀ hc.rho_nonneg hc.rho_lt_one (by omega)
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos (sub_pos.2 hp) (sub_pos.2 hcon)]

/-- **Lemma 3 (2), (3)**: under contraction data the `f`-periodic states form a finite set,
so property (F) is a statement about finitely many states. -/
theorem periodicStates_finite (hc : ContractionData s L ν ρ) :
    {x : α × (α → ℤ) | IsState L x ∧ ∃ k, 1 ≤ k ∧ StepN s L k x x}.Finite := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact Set.toFinite _
  obtain ⟨D, hD⟩ := exists_prefix_bound ν s
  obtain ⟨a₁, h₁⟩ := Finite.exists_max fun a : α => L (pvec [a])
  refine ((Set.finite_univ (α := α)).prod
    (hc.proper (L (pvec [a₁])) (D / (1 - ρ)))).subset ?_
  rintro x ⟨hx, k, hk, hper⟩
  refine ⟨Set.mem_univ _, ?_, periodic_bound hc (fun a P b S h => hD a P ⟨b :: S, h.symm⟩) hk hper⟩
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2, h₁ x.1]

/-- On the standing class the `f`-periodic states form a finite set (hypotheses of
`exists_contractionData_of_pisot`). -/
theorem periodicStates_finite_of_pisot
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1) :
    {x : α × (α → ℤ) | IsState (lenHom ℓ) x ∧
      ∃ k, 1 ≤ k ∧ StepN s (lenHom ℓ) k x x}.Finite := by
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_pisot s hirr hℓ hℓM hpisot
  exact periodicStates_finite hc

end Box

/-! ### Non-vacuity on a PIP3 specimen, and the strict control -/

section Controls

open Psc.Descendants (tribSubst)

/-- **Non-vacuity of (A) and (B) on PIP3.**  For Tribonacci `0 ↦ 01, 1 ↦ 02, 2 ↦ 0` every
spectral hypothesis of this module holds (`Psc.BPrime.trib_prim`, `trib_irreducible`,
`trib_isPisot`), so its Perron row `ℓ` has `LengthData`, `β > 1` and `ContractionData`: every
hypothesis of `Psc.GeometricF.fc1_equivalence_of_contraction` except `PropertyF`. -/
theorem trib_fc1_hypotheses : ∃ (β : ℝ) (ℓ : Fin 3 → ℝ) (ν : (Fin 3 → ℤ) → ℝ) (ρ : ℝ),
    (∀ a, 0 < ℓ a) ∧ ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ ∧
      Psc.BPrime.IsPisot β ∧
      (∀ z : ℂ, ((inc tribSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
        ‖z‖ < 1) ∧
      LengthData tribSubst (lenHom ℓ) β ∧ 1 < β ∧ ContractionData tribSubst (lenHom ℓ) ν ρ := by
  obtain ⟨β, hβ0, ℓ, hℓ, hℓM⟩ :=
    Psc.PerronExistence.exists_pos_left_eigen_inc tribSubst Psc.BPrime.trib_prim
  have hP := Psc.BPrime.trib_isPisot hℓ hℓM
  have hroots := pisot_roots_of_isPisot tribSubst Psc.BPrime.trib_irreducible hℓ hℓM hP
  obtain ⟨ν, ρ, hc⟩ :=
    exists_contractionData_of_pisot tribSubst Psc.BPrime.trib_irreducible hℓ hℓM hroots
  exact ⟨β, ℓ, ν, ρ, hℓ, hℓM, hP, hroots, lengthData_of_left_eigen hβ0 hℓ hℓM, hP.1, hc⟩

/-- **Theorem FC1 for Tribonacci, with property (F) as the only hypothesis left**: for every
positive left eigen-row `ℓ` of its incidence matrix. -/
theorem trib_fc1_of_propertyF {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hF : PropertyF tribSubst (lenHom ℓ)) :
    ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter tribSubst c ∧ IsPeriodicLetter tribSubst c' ∧
          ¬ StrongCoincidenceWitness tribSubst c c') ∧
      ((∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness tribSubst c c') :=
  fc1_equivalence_of_isPisot Psc.BPrime.trib_irreducible hℓ hℓM (Psc.BPrime.trib_isPisot hℓ hℓM)
    hF

/-- **The conclusion of `trib_fc1_of_propertyF` is true unconditionally**: on Tribonacci
every pair of distinct letters has a left strong-coincidence witness
(`Psc.StrictSystem.trib_least`), so all three statements of the equivalence are false
(`Psc.StrictSystem.trib_no_strictSystem`).  This is proved without Theorem FC1 and without
`PropertyF`; it shows that the instance does not assert anything false on this specimen. -/
theorem trib_fc1_statements :
    (¬ ∃ C : Finset (List (Fin 3) × List (Fin 3)), StrictSystem tribSubst C) ∧
      (¬ ∃ c c', c ≠ c' ∧ IsPeriodicLetter tribSubst c ∧ IsPeriodicLetter tribSubst c' ∧
          ¬ StrongCoincidenceWitness tribSubst c c') ∧
      ¬ ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness tribSubst c c' := by
  have hall : ∀ c c' : Fin 3, c ≠ c' → StrongCoincidenceWitness tribSubst c c' :=
    Psc.StrictSystem.fin3_all_pairs
      (Psc.StrictSystem.witness_of_least Psc.StrictSystem.trib_least.1)
      (Psc.StrictSystem.witness_of_least Psc.StrictSystem.trib_least.2.1)
      (Psc.StrictSystem.witness_of_least Psc.StrictSystem.trib_least.2.2)
  exact ⟨fun ⟨C, hC⟩ => Psc.StrictSystem.trib_no_strictSystem C hC,
    fun ⟨c, c', hne, _, _, hnw⟩ => hnw (hall c c' hne), fun h => h hall⟩

/-- **Negative control for (A).**  On the reducible strict control `10/102/211`
(`Psc.StrictSystem.carrierSubst`, primitive, `χ_M = (X − 1)(X² − 2X − 2)`) the hypotheses of
`exists_contractionData_of_separable` fail for every positive left eigen-row, as they must
(`Psc.GeometricF.carrier_not_contractionData`): `χ_M` is not both separable over `ℂ` and
Pisot in the root form.  In particular the standing hypotheses (irreducible, root form) fail
there. -/
theorem carrier_not_pisot_roots {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc Psc.StrictSystem.carrierSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ¬ (((inc Psc.StrictSystem.carrierSubst).map (Nat.cast : ℕ → ℂ)).charpoly.Separable ∧
      ∀ z : ℂ, ((inc Psc.StrictSystem.carrierSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 →
        z ≠ β → ‖z‖ < 1) := by
  rintro ⟨hsep, hp⟩
  have hβ := Psc.BPrimeCore.one_lt_perron _ Psc.StrictSystem.carrier_primitive hℓ hℓM
  obtain ⟨ν, ρ, hc⟩ := exists_contractionData_of_separable _ hsep
    (fun h => (hℓ 0).ne' (congrFun h 0)) hℓM hp
  exact carrier_not_contractionData (lengthData_of_left_eigen (by linarith) hℓ hℓM) hβ hc

end Controls

/-! ### Non-vacuity of the instance: Fibonacci satisfies every hypothesis -/

section Fibonacci

open Psc.Descendants (fibSubst)

/-- The incidence action of Fibonacci `0 ↦ 01, 1 ↦ 0`: `M (v₀, v₁) = (v₀ + v₁, v₀)`. -/
theorem fib_mulVec (v : Fin 2 → ℤ) : incZ fibSubst *ᵥ v = ![v 0 + v 1, v 0] := by
  funext a
  fin_cases a <;> simp [incZ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, fibSubst]

/-- The length coordinate `β v₀ + v₁` of Fibonacci (`ℓ·v = ℓ₁ (β v₀ + v₁)`). -/
def fibX (β : ℝ) (v : Fin 2 → ℤ) : ℝ := β * v 0 + v 1

/-- The contracted coordinate `(1 − β) v₀ + v₁` of Fibonacci (the conjugate of `fibX`). -/
def fibY (β : ℝ) (v : Fin 2 → ℤ) : ℝ := (1 - β) * v 0 + v 1

variable {β : ℝ} {ℓ : Fin 2 → ℝ}

/-- The Perron data of Fibonacci: `ℓ₀ = β ℓ₁`, `β² = β + 1`, `3/2 < β < 2`. -/
theorem fib_perron (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ℓ 0 = β * ℓ 1 ∧ β ^ 2 = β + 1 ∧ 3 / 2 < β ∧ β < 2 := by
  have h0 := congrFun hℓM 0
  have h1 := congrFun hℓM 1
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Psc.BPrime.fib_inc] at h0 h1
  have hsq : β ^ 2 = β + 1 := by
    have h : (β ^ 2 - β - 1) * ℓ 1 = 0 := by
      rw [h1] at h0
      linear_combination -h0
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · exact absurd h (hℓ 1).ne'
  have hβ0 : 0 < β := by
    by_contra h
    push Not at h
    nlinarith [hℓ 0, hℓ 1, mul_nonpos_of_nonpos_of_nonneg h (hℓ 1).le]
  refine ⟨h1, hsq, ?_, ?_⟩
  · by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_left h hβ0.le]
  · by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_right h hβ0.le]

theorem fibX_mulVec (hsq : β ^ 2 = β + 1) (v : Fin 2 → ℤ) :
    fibX β (incZ fibSubst *ᵥ v) = β * fibX β v := by
  rw [fib_mulVec]
  simp only [fibX, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  linear_combination (-(v 0 : ℝ)) * hsq

theorem fibY_mulVec (hsq : β ^ 2 = β + 1) (v : Fin 2 → ℤ) :
    fibY β (incZ fibSubst *ᵥ v) = (1 - β) * fibY β v := by
  rw [fib_mulVec]
  simp only [fibY, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  linear_combination (-(v 0 : ℝ)) * hsq

theorem fib_pvec_zero : pvec [(0 : Fin 2)] = ![1, 0] := by
  funext a
  fin_cases a <;> simp [pvec]

/-- A Fibonacci state `(j, v)` has `0 ≤ β v₀ + v₁`, `< β` in a tile `0` and `< 1` in a
tile `1`. -/
theorem fib_state (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) {x : Fin 2 × (Fin 2 → ℤ)}
    (hx : IsState (lenHom ℓ) x) :
    0 ≤ fibX β x.2 ∧ (x.1 = 0 → fibX β x.2 < β) ∧ (x.1 = 1 → fibX β x.2 < 1) := by
  obtain ⟨h1, -, -, -⟩ := fib_perron hℓ hℓM
  have hlen : lenHom ℓ x.2 = ℓ 1 * fibX β x.2 := by
    simp only [lenHom_apply, Fin.sum_univ_two, fibX, h1]
    ring
  obtain ⟨hs0, hs1⟩ := hx
  rw [hlen] at hs0 hs1
  rw [lenHom_single] at hs1
  refine ⟨nonneg_of_mul_nonneg_right hs0 (hℓ 1), fun h => ?_, fun h => ?_⟩
  · rw [h, h1, mul_comm β] at hs1
    exact lt_of_mul_lt_mul_left hs1 (hℓ 1).le
  · rw [h] at hs1
    nlinarith [hℓ 1]

/-- The two shapes of a step of the Fibonacci state map: into the first tile of the image
(`P = []`), or from a tile `0` into the second tile of `σ(0) = 01` (`P = 0`). -/
theorem fib_step_cases {L : (Fin 2 → ℤ) →+ ℝ} {x y : Fin 2 × (Fin 2 → ℤ)}
    (h : Step fibSubst L x y) :
    (y.1 = 0 ∧ y.2 = incZ fibSubst *ᵥ x.2) ∨
      (y.1 = 1 ∧ y.2 = incZ fibSubst *ᵥ x.2 - pvec [0]) := by
  obtain ⟨P, S, hP, hy, -⟩ := h
  rcases P with _ | ⟨p, _ | ⟨q, r⟩⟩
  · left
    refine ⟨?_, by simpa using hy⟩
    by_cases h0 : x.1 = 0
    · rw [h0] at hP
      simp [fibSubst] at hP
      exact hP.1.symm
    · simp [fibSubst, h0] at hP
      exact hP.1.symm
  · right
    by_cases h0 : x.1 = 0
    · rw [h0] at hP
      simp [fibSubst] at hP
      refine ⟨hP.2.1.symm, ?_⟩
      rw [hy, ← hP.1]
    · simp [fibSubst, h0] at hP
  · exfalso
    by_cases h0 : x.1 = 0
    · rw [h0] at hP
      simp [fibSubst] at hP
    · simp [fibSubst, h0] at hP

/-- One step contracts the conjugate coordinate: `|Y(f x)| ≤ (β − 1)(|Y(x)| + 1)`. -/
theorem fibY_step (hsq : β ^ 2 = β + 1) (h1 : 1 < β) {L : (Fin 2 → ℤ) →+ ℝ}
    {x y : Fin 2 × (Fin 2 → ℤ)} (h : Step fibSubst L x y) :
    |fibY β y.2| ≤ (β - 1) * (|fibY β x.2| + 1) := by
  have hab : |1 - β| = β - 1 := by rw [abs_of_neg (by linarith)]; ring
  rcases fib_step_cases h with ⟨-, hy⟩ | ⟨-, hy⟩
  · rw [hy, fibY_mulVec hsq, abs_mul, hab]
    nlinarith [abs_nonneg (fibY β x.2)]
  · have e : fibY β (incZ fibSubst *ᵥ x.2 - pvec [0]) = (1 - β) * (fibY β x.2 - 1) := by
      have := fibY_mulVec hsq x.2
      rw [fib_pvec_zero]
      simp only [fibY, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this ⊢
      push_cast
      linear_combination this
    rw [hy, e, abs_mul, hab]
    have h2 : |fibY β x.2 - 1| ≤ |fibY β x.2| + 1 := by
      have := abs_sub (fibY β x.2) 1
      simpa using this
    nlinarith

/-- `|Y(fⁿ x)| ≤ (β − 1)ⁿ |Y(x)| + β (1 − (β − 1)ⁿ)`. -/
theorem fibY_stepN (hsq : β ^ 2 = β + 1) (h1 : 1 < β) {L : (Fin 2 → ℤ) →+ ℝ}
    {x : Fin 2 × (Fin 2 → ℤ)} :
    ∀ (n : ℕ) {y : Fin 2 × (Fin 2 → ℤ)}, StepN fibSubst L n x y →
      |fibY β y.2| ≤ (β - 1) ^ n * |fibY β x.2| + β * (1 - (β - 1) ^ n)
  | 0, _, h => by rw [← h]; simp
  | n + 1, y, ⟨z, hz, hy⟩ => by
    have ih := fibY_stepN hsq h1 n hz
    have hs := fibY_step hsq h1 hy
    have h3 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ β - 1)
    rw [pow_succ]
    nlinarith [hsq]

/-- **Lemma 3 (3) on Fibonacci**: an `f`-periodic state has `|Y| ≤ β`. -/
theorem fibY_periodic (hsq : β ^ 2 = β + 1) (h1 : 1 < β) (h2 : β < 2)
    {L : (Fin 2 → ℤ) →+ ℝ} {x : Fin 2 × (Fin 2 → ℤ)} {k : ℕ} (hk : 1 ≤ k)
    (h : StepN fibSubst L k x x) : |fibY β x.2| ≤ β := by
  have hb := fibY_stepN hsq h1 k h
  have hp : (β - 1) ^ k < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  by_contra hc
  push Not at hc
  nlinarith [mul_pos (sub_pos.2 hp) (sub_pos.2 hc)]

/-- The lattice points of the box of periodic states: `0 ≤ β v₀ + v₁ < β` and
`|(1 − β) v₀ + v₁| ≤ β` leave `v = 0`, `(0, 1)`, `(1, −1)`. -/
theorem fib_candidates (h32 : 3 / 2 < β) (h2 : β < 2) {v : Fin 2 → ℤ}
    (hX0 : 0 ≤ fibX β v) (hXβ : fibX β v < β) (hY : |fibY β v| ≤ β) :
    v = 0 ∨ v = ![0, 1] ∨ v = ![1, -1] := by
  rw [abs_le] at hY
  simp only [fibX, fibY] at hX0 hXβ hY
  have h0 : 0 ≤ v 0 := by
    by_contra h
    have h' : (v 0 : ℝ) ≤ -1 := by exact_mod_cast (by omega : v 0 ≤ -1)
    nlinarith [mul_le_mul_of_nonneg_left h' (by linarith : (0 : ℝ) ≤ 2 * β - 1)]
  have h1 : v 0 ≤ 1 := by
    by_contra h
    have h' : (2 : ℝ) ≤ v 0 := by exact_mod_cast (by omega : 2 ≤ v 0)
    nlinarith [mul_le_mul_of_nonneg_left h' (by linarith : (0 : ℝ) ≤ 2 * β - 1)]
  have hv0 : v 0 = 0 ∨ v 0 = 1 := by omega
  rcases hv0 with e | e
  · rw [e] at hX0 hXβ
    simp only [Int.cast_zero, mul_zero, zero_add] at hX0 hXβ
    have a0 : 0 ≤ v 1 := by exact_mod_cast hX0
    have a1 : v 1 < 2 := by
      have : (v 1 : ℝ) < 2 := by linarith
      exact_mod_cast this
    have hv1 : v 1 = 0 ∨ v 1 = 1 := by omega
    rcases hv1 with e' | e'
    · left
      funext a
      fin_cases a <;> simp [e, e']
    · right; left
      funext a
      fin_cases a <;> simp [e, e']
  · rw [e] at hX0 hXβ
    simp only [Int.cast_one, mul_one] at hX0 hXβ
    have a0 : -2 < v 1 := by
      have : ((-2 : ℤ) : ℝ) < v 1 := by push_cast; linarith
      exact_mod_cast this
    have a1 : v 1 < 0 := by
      have : (v 1 : ℝ) < 0 := by linarith
      exact_mod_cast this
    have hv1 : v 1 = -1 := by omega
    right; right
    funext a
    fin_cases a <;> simp [e, hv1]

/-- The state with `v = (0, 1)` is mapped to a vertex state. -/
theorem fib_reach_one (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) {x : Fin 2 × (Fin 2 → ℤ)}
    (hx : IsState (lenHom ℓ) x) (hv : x.2 = ![0, 1]) :
    ∃ a, Step fibSubst (lenHom ℓ) x (a, 0) := by
  obtain ⟨-, hsq, h32, h2⟩ := fib_perron hℓ hℓM
  have hL := lengthData_of_left_eigen (s := fibSubst) (by linarith : (0 : ℝ) < β) hℓ hℓM
  obtain ⟨y, hy⟩ := step_total hL hx
  rcases fib_step_cases hy with ⟨hy1, hy2⟩ | ⟨-, hy2⟩
  · exfalso
    have hs := (fib_state hℓ hℓM hy.isState).2.1 hy1
    rw [hy2, fibX_mulVec hsq, hv] at hs
    simp [fibX] at hs
  · refine ⟨y.1, ?_⟩
    have h0 : y.2 = 0 := by
      rw [hy2, hv, fib_mulVec, fib_pvec_zero]
      funext a
      fin_cases a <;> simp
    have e : (y.1, (0 : Fin 2 → ℤ)) = y := Prod.ext rfl h0.symm
    rw [e]
    exact hy

/-- The states with `v = (0, 1)` or `(1, −1)` reach a vertex state. -/
theorem fib_reach (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) {x : Fin 2 × (Fin 2 → ℤ)}
    (hx : IsState (lenHom ℓ) x) (hv : x.2 = ![0, 1] ∨ x.2 = ![1, -1]) :
    ∃ n a, StepN fibSubst (lenHom ℓ) n x (a, 0) := by
  rcases hv with hv | hv
  · obtain ⟨a, ha⟩ := fib_reach_one hℓ hℓM hx hv
    exact ⟨1, a, x, rfl, ha⟩
  · obtain ⟨-, hsq, h32, h2⟩ := fib_perron hℓ hℓM
    have hL := lengthData_of_left_eigen (s := fibSubst) (by linarith : (0 : ℝ) < β) hℓ hℓM
    obtain ⟨y, hy⟩ := step_total hL hx
    rcases fib_step_cases hy with ⟨-, hy2⟩ | ⟨-, hy2⟩
    · have hyv : y.2 = ![0, 1] := by
        rw [hy2, hv, fib_mulVec]
        funext a
        fin_cases a <;> simp
      obtain ⟨a, ha⟩ := fib_reach_one hℓ hℓM hy.isState hyv
      exact ⟨2, a, y, ⟨x, rfl, hy⟩, ha⟩
    · exfalso
      have hs := (fib_state hℓ hℓM hy.isState).1
      rw [hy2, hv, fib_mulVec, fib_pvec_zero] at hs
      simp [fibX] at hs
      linarith

/-- **Property (F) for Fibonacci**, for every positive left eigen-row of its incidence
matrix: an `f`-periodic state lies in the box `|Y| ≤ β` (`fibY_periodic`), whose three lattice
points (`fib_candidates`) all reach a vertex state (`fib_reach`). -/
theorem fib_propertyF (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    PropertyF fibSubst (lenHom ℓ) := by
  intro x hx k hk hper
  obtain ⟨-, hsq, h32, h2⟩ := fib_perron hℓ hℓM
  have hL := lengthData_of_left_eigen (s := fibSubst) (by linarith : (0 : ℝ) < β) hℓ hℓM
  obtain ⟨hX0, hXa, hXb⟩ := fib_state hℓ hℓM hx
  have hXβ : fibX β x.2 < β := by
    by_cases h0 : x.1 = 0
    · exact hXa h0
    · have h1 : x.1 = 1 := by omega
      linarith [hXb h1]
  have hmul : ∀ j, StepN fibSubst (lenHom ℓ) (k * j) x x := by
    intro j
    induction j with
    | zero => exact rfl
    | succ j ih => rw [Nat.mul_succ]; exact stepN_add ih k hper
  rcases fib_candidates h32 h2 hX0 hXβ (fibY_periodic hsq (by linarith) h2 hk hper) with
    h | h | h
  · exact h
  · obtain ⟨n, a, hn⟩ := fib_reach hℓ hℓM hx (Or.inl h)
    exact stepN_absorb hL.pos hn (Nat.le_mul_of_pos_left n hk) (hmul n)
  · obtain ⟨n, a, hn⟩ := fib_reach hℓ hℓM hx (Or.inr h)
    exact stepN_absorb hL.pos hn (Nat.le_mul_of_pos_left n hk) (hmul n)

/-- The Pisot hypothesis for Fibonacci in the root form: the only complex root of
`χ_M = X² − X − 1` other than `β` is `1 − β`, of modulus `β − 1 < 1`. -/
theorem fib_pisot_roots (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ∀ z : ℂ, ((inc fibSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1 := by
  obtain ⟨-, hsq, h32, h2⟩ := fib_perron hℓ hℓM
  intro z hz hzβ
  rw [Psc.BPrime.fib_charpoly] at hz
  simp only [eval_sub, eval_pow, eval_X, eval_one] at hz
  have hβC : (β : ℂ) ^ 2 = β + 1 := by exact_mod_cast hsq
  have hfac : (z - β) * (z - (1 - β)) = 0 := by linear_combination hz - hβC
  have hz' : z = ((1 - β : ℝ) : ℂ) := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd (sub_eq_zero.1 h) hzβ
    · rw [sub_eq_zero.1 h]
      push_cast
      ring
  rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

/-- **Non-vacuity of Theorem FC1 on the standing hypotheses.**  Every hypothesis of
`fc1_equivalence_of_primitive_pisot` holds for Fibonacci `0 ↦ 01, 1 ↦ 0` (two letters, so
not PIP3): primitive (`Psc.BPrimeBinding.fib_primitive`), `χ_M = X² − X − 1` irreducible over
`ℚ` (`Psc.BPrime.fib_irreducible`), a positive left eigen-row, every other root in the open
unit disc (`fib_pisot_roots`), and property (F) for the tile lengths (`fib_propertyF`). -/
theorem fib_fc1_hypotheses : ∃ (β : ℝ) (ℓ : Fin 2 → ℝ),
    (∃ k ≥ 1, ∀ a c, 0 < (inc fibSubst ^ k) a c) ∧
      Irreducible ((inc fibSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (∀ a, 0 < ℓ a) ∧ ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ ∧
      (∀ z : ℂ, ((inc fibSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
        ‖z‖ < 1) ∧
      PropertyF fibSubst (lenHom ℓ) := by
  obtain ⟨β, -, ℓ, hℓ, hℓM⟩ := Psc.PerronExistence.exists_pos_left_eigen_inc fibSubst
    Psc.BPrimeBinding.fib_primitive
  exact ⟨β, ℓ, Psc.BPrimeBinding.fib_primitive, Psc.BPrime.fib_irreducible, hℓ, hℓM,
    fib_pisot_roots hℓ hℓM, fib_propertyF hℓ hℓM⟩

/-- **Theorem FC1 on Fibonacci, with every hypothesis discharged**
(`fc1_equivalence_of_primitive_pisot`). -/
theorem fib_fc1 :
    ((∃ C : Finset (List (Fin 2) × List (Fin 2)), StrictSystem fibSubst C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter fibSubst c ∧ IsPeriodicLetter fibSubst c' ∧
          ¬ StrongCoincidenceWitness fibSubst c c') ∧
      ((∃ C : Finset (List (Fin 2) × List (Fin 2)), StrictSystem fibSubst C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness fibSubst c c') := by
  obtain ⟨β, ℓ, hprim, hirr, hℓ, hℓM, hroots, hF⟩ := fib_fc1_hypotheses
  exact fc1_equivalence_of_primitive_pisot hprim hirr hℓ hℓM hroots hF

/-- **What the instance says on Fibonacci.**  Both images begin with `0`, so the pair `0, 1`
has a left strong-coincidence witness at level `1`; by `fib_fc1` there is no strict system and
no pair of distinct `g`-periodic letters without a witness.  All three statements of the
equivalence are false here: the instance exercises the hypotheses, not the construction of a
strict system (item 3 of Theorem FC1). -/
theorem fib_fc1_statements :
    (¬ ∃ C : Finset (List (Fin 2) × List (Fin 2)), StrictSystem fibSubst C) ∧
      (¬ ∃ c c', c ≠ c' ∧ IsPeriodicLetter fibSubst c ∧ IsPeriodicLetter fibSubst c' ∧
          ¬ StrongCoincidenceWitness fibSubst c c') ∧
      ¬ ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness fibSubst c c' := by
  have h01 : StrongCoincidenceWitness fibSubst 0 1 :=
    ⟨1, [], [1], [], [], 0, by decide, by decide, fun _ => rfl⟩
  have hall : ∀ c c' : Fin 2, c ≠ c' → StrongCoincidenceWitness fibSubst c c' := by
    intro c c' hne
    fin_cases c <;> fin_cases c' <;> simp at hne
    · exact h01
    · exact Psc.StrictSystem.strongCoincidenceWitness_comm.1 h01
  have h1 : ¬ ∃ C : Finset (List (Fin 2) × List (Fin 2)), StrictSystem fibSubst C :=
    fun h => fib_fc1.2.1 h hall
  exact ⟨h1, fun h => h1 (fib_fc1.1.2 h), fun h => h hall⟩

end Fibonacci

/-! ### Bridges for the local copies of `PscVerif.GeometricFInclusion` -/

omit [Fintype α] in
/-- `Psc.GeometricF.pvec` is `Psc.BPrimeCore.parikhCast` at `ℤ`. -/
theorem pvec_eq_parikhCast (w : List α) :
    pvec w = (Psc.BPrimeCore.parikhCast w : α → ℤ) := rfl

/-- `Psc.GeometricF.incZ` is `Psc.Degree2Sector.incZ` on the substitution of a child
system. -/
theorem incZ_eq_degree2Sector (S : Psc.Binomial.ChildSystem (Fin 3)) :
    incZ S.s = Psc.Degree2Sector.incZ S := rfl

end Psc.GeometricFPisot
