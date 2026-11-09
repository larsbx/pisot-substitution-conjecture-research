/-
# Proposition B′ and Corollary B (i), end to end

`docs/c4-general-structure-2026-11-06.md` §3, **Proposition B′** (termination forces the
conjugates into the disc; any alphabet) and **Corollary B (i)** (the balanced pair algorithm
off the Pisot cone); `docs/c4-bprime-independent-proof-audit-2026-11-07.md`, "Corrected
theorem (exact scope)", "Independent proof" steps 1–6, the adversarial assumption inventory,
the independent negative control, and the acceptance matrix;
`docs/c4-bprime-machine-verification-priority-2026-11-07.md`, derivation items 1–6.  This
module composes `PscVerif.BPrimeBinding` (audit step 1, Sirvent–Solomyak (3.1)) with
`PscVerif.BPrimeCore` (audit steps 2–6).  `tools/audit_bpa_bprime.py` is the numerical
control of the specimen of control (a).

Setting.  `σ = subst s` on a finite alphabet `α`, with incidence matrix `M = inc s` (cast to
`ℚ`, `ℝ`, `ℂ`) and `χ_M` its characteristic polynomial.  Primitivity is
`∃ k ≥ 1, ∀ a c, 0 < (Mᵏ) a c`; nonerasing follows from it
(`Psc.PrimitiveExpansion.nonerasing_of_primitive`), so it is not a separate hypothesis.  A
one-sided fixed point is `IsFixed s u` (`Psc.BPrimeBinding`: the image of every prefix of
`u : ℕ → α` is a prefix of `u`), a prefix is `PrefixOf u W`, and `IW s u W` is the
Sirvent–Solomyak set `I(W) = ⋃ₙ Iₙ(W)` (coincidence blocks retained; `Iₙ(W)` the blocks of
the reduction of `(u, S^{|σⁿ W|} u)`, equal to the recursion (3.1) by
`Psc.BPrimeBinding.ssLevel_eq_of_primitive`).  *Termination* of `bpa-W` means that `I(W)` is
finite, not termination with coincidence.  The Perron root `β` is named by a positive left
eigenvector `ℓ M = β ℓ`, which determines it (`Psc.PerronExistence.PerronData.left_nonneg`);
the `_perron` forms supply it from `Psc.PerronExistence.perron_inc`.  `IsPisot b`: `b` is a
real algebraic integer `> 1` whose other conjugates over `ℚ` (roots of `minpoly ℚ b`) lie in
the open unit disc; `IsPisotOrSalem b`: the same with the closed disc.

## Proved here, in full

* **The binding** (audit steps 1 and 2, "fixed point used twice"): `isPrefixOf_iterate`
  (a fixed point with prefix `W` has every `σⁿ(W)` as a prefix, the hypothesis `hpre` of
  `Psc.BPrimeCore.bprime_core`); **`cutGaps_of_finite`** (a finite `I(W)` gives one `L` with
  the cut hypothesis `CutGaps u |σⁿ W| L` at every level: `BPrimeBinding.BoundedGaps` and
  `tn` are `BPrimeCore.CutGaps` and `len` by unfolding); `exists_isFixed_of_seed` (for a
  nonerasing `σ`, the limit word `Psc.BPrimeBinding.seedLimit` grown from `u₀ <+: σ(u₀)`,
  `|u₀| < |σ(u₀)|`, is a fixed point with prefix `u₀`).
* **Proposition B′** (the audit's corrected theorem): **`bprime`** (fixed point `u`,
  nonempty prefix `W`, `σ` primitive, `χ_M` irreducible over `ℚ`, `I(W)` finite: every
  complex root `z ≠ β` of `χ_M` has `‖z‖ ≤ 1`); `bprime_perron` (with `PerronData`);
  **`bprime_isPisotOrSalem`** (on two or more letters, "so `β` is Pisot or Salem": `β > 1`
  is an algebraic integer with minimal polynomial `χ_M`).
* **Proposition B′ on three letters** (audit step 6): **`bprime_cubic`** (`natDegree χ_M = 3`:
  `1 < β` and every complex root `z ≠ β` has `‖z‖ < 1`); **`bprime_cubic_isPisot`**
  ("so `χ_M` is Pisot": `IsPisot β`); `bprime_cubic_perron`.  The algebraic reading uses
  `minpoly_eq_charpoly` (an irreducible `χ_M` is the minimal polynomial of each real root),
  `isIntegral_of_root`, `aeval_charpoly`, `isRoot_of_pos_left_eigen`, `isPisot_of`,
  `isPisotOrSalem_of`.
* **Corollary B (i)**, the contrapositive: **`corB_infinite`** (any alphabet: `χ_M`
  irreducible and some root `z ≠ β` with `‖z‖ > 1`; then for every fixed point and every
  nonempty prefix `W`, `I(W)` is infinite); `corB_infinite_of_not_isPisotOrSalem`;
  **`corB_infinite_cubic`** (three letters: `χ_M` irreducible and `β` not Pisot).
* **`I(W)` read literally** (Sirvent–Solomyak (3.1): reduce `(u, S^{|W|} u)`, then reduce
  all substituted pairs): `bprime_ss`, `corB_infinite_ss`, `corB_infinite_cubic_ss` state
  termination on `⋃ₙ ssLevel s u W n`, equal to `IW s u W` by
  `Psc.BPrimeBinding.IW_eq_iUnion_ssLevel`.
* **Control (a)**, negative, the audit specimen `0 ↦ 01, 1 ↦ 2, 2 ↦ 00`
  (`Psc.BPrimeCore.zetaSubst`, `χ_M = X³ - X² - 2`): `zetaU` (its fixed point `σ^ω(0)`,
  `Psc.BPrimeBinding.seedLimit`), `zetaU_isFixed`, `zetaU_prefix`, `zeta_prim` (`M⁴ > 0`),
  `zeta_not_isPisotOrSalem` and `zeta_not_isPisot` (a non-Perron root has modulus `> 1`, by
  the product of the roots, `Psc.BPrimeCore.zeta_root_outside`); **`zeta_control`** (every
  hypothesis of Corollary B (i) is discharged: `M⁴ > 0` by `decide +kernel`, irreducibility
  by the rational root test `Psc.BPrimeCore.irreducible_cubic`, degree `3` by
  `Psc.Degree4Floor.natDegree_charpoly`); **`zeta_IW_infinite`** (every fixed point, every
  nonempty prefix: `I(W)` infinite) and **`zetaU_IW_infinite`** (the `bpa-0` of `σ^ω(0)` does
  not terminate), the same from each other form of Corollary B (i):
  `zetaU_IW_infinite_of_root` (`corB_infinite`, no degree hypothesis),
  `zetaU_IW_infinite_of_not_isPisotOrSalem`, and `zetaU_ssLevel_infinite` (the literal
  recursion (3.1) never closes up).
* **Control (b)**, negative, irreducibility in the nonvanishing step (audit step 4):
  `ctrlSubst = (0 ↦ 0001, 1 ↦ 0111)` realizes `Psc.BPrimeCore.ctrlM = [[3,1],[1,3]]`
  (`ctrlSubst_inc`); **`reducible_control`**: primitive, `χ_M` reducible, and the left
  eigenvector `(1, -1)` of the non-Perron root `2 > 1` kills the Parikh vector of the nonempty
  word `01` (`Psc.BPrimeCore.irreducibility_needed`).
* **Control (c)**, positive, Tribonacci `0 ↦ 01, 1 ↦ 02, 2 ↦ 0`
  (`Psc.Descendants.tribSubst`): `trib_inc`, `trib_primitive` (`M³ > 0`), `trib_prim`,
  `trib_charpoly` (`X³ - X² - X - 1`), `trib_irreducible` (`irreducible_cubic`), the fixed
  point `tribU` (`tribU_isFixed`, `tribU_prefix`), `trib_norm_lt` (a non-real conjugate `z`
  has `β ‖z‖² = det M = 1`, `Psc.Degree4Floor.exists_other_roots`,
  `Psc.SectorBridge.det_eq_mul_roots`), `trib_isPisot` (the Perron root is Pisot, proved
  directly); **`trib_control`**: every hypothesis of `bprime_cubic_isPisot` except the
  finiteness of `I(0)` holds, and so does its conclusion.  `plastic_not_isFixed`: the
  plastic substitution `0 ↦ 1, 1 ↦ 2, 2 ↦ 01` has no one-sided fixed point, so `bprime`
  does not apply to it (a remark about scope, not a proof that the fixed-point hypothesis is
  necessary).
* **Control (d)**, positive, joint satisfiability: **`one_letter_control`** (for
  `0 ↦ 00`, `u = 0^∞`, `W = 0`, every hypothesis of `bprime` holds at once, including the
  finiteness of `I(0) ⊆ {(0, 0)}` by `isBlock_fin_one`; the conclusion is empty there);
  `prefixOf_fin_one`.  On two letters with a reducible `χ_M`:
  `Psc.BPrimeBinding.per_control`.
* **Control (e)**, positive, the full hypothesis set with an irreducible `χ_M` and a
  nonempty conclusion: Fibonacci `0 ↦ 01, 1 ↦ 0` (`Psc.Descendants.fibSubst`), `fib_inc`,
  `fib_charpoly` (`X² - X - 1`), `fib_irreducible` (`(2x - 1)² = 5` has no rational
  solution), `fib_conj` (`1 - β` is a root `≠ β`); **`fib_control`** (fixed point `fibU`,
  `W = 0`, `M² > 0`, irreducibility and the finiteness of `I(0)`,
  `Psc.BPrimeBinding.fib_terminates`, all hold); **`fib_bprime`** (`bprime` puts
  `1 - β` in the closed unit disc) and `fib_isPisotOrSalem`.

## Hypotheses and their roles

* `IsFixed s u` and `PrefixOf u W`: both uses of the fixed point in the audit's inventory,
  `P(tₙ) = Mⁿ w` (through `isPrefixOf_iterate`) and the identification of the substituted
  reductions with shifts of the same `u` (inside `cutGaps_of_finite`);
* `W ≠ []`: `w ≠ 0` (cyclicity, growth);
* primitivity: recurrence and the initial reductions (`Psc.BPrimeBinding.unbounded_of_primitive`),
  nonerasing, Perron data, `β > 1` and strict dominance `‖z‖ < β`;
* irreducibility of `χ_M` over `ℚ`: the nonvanishing `q · w ≠ 0` (step 4; control (b)), the
  cubic boundary (step 6) and the minimal-polynomial reading;
* finiteness of `I(W)`: the only place where termination enters, through one `L` for all
  levels;
* `natDegree χ_M = 3` (cubic forms): no unit-circle root, through the abstract cubic boundary
  `Psc.BPrimeCore.norm_ne_one_of_cubic`.  Its control `Psc.BPrimeCore.degree_three_needed`
  (`X² + 1`) shows only that this lemma needs its degree among arbitrary monic irreducible
  rational polynomials; `X² + 1` is not the `χ_M` of a primitive substitution, so it does
  not show that degree three is necessary for the strict disc in B′.  In degree two the
  strict disc follows from `bprime` by hand (the conjugate `tr M - β` is real, and modulus
  one would make it a rational root `±1`), but it is not stated here.

## Acceptance matrix of the audit (status of each item in Lean)

* P0.1 (shift/count identity): `proof/bpa/BpaPrefixBridge.lean`, restated in the library as
  `Psc.BPrimeCore.shift_factor_identity`.
* P0.2 (bounded-block cancellation, with the off-by-one at block ends):
  `Psc.BPrimeCore.cut_bound`, `exists_cut_of_blocks`, `cut_bound_of_blocks`.
* P0.3 (bind (3.1), orientation, coincidences, index `I_{n+1}` versus `tₙ`):
  `Psc.BPrimeBinding.I_succ_of_primitive`, `ssLevel_eq_of_primitive`, `tn_succ`,
  `boundedGaps_of_finite_primitive`, against the Lean reduction `Psc.Reduction.red` and the
  child relation `Psc.Descendants.Child`.  A refinement proof for the Mojo implementation
  `kernel/psc/bpa.mojo` is not part of it.
* P1.4 (algebraic cyclicity): `Psc.BPrimeCore.krylov_span_eq_top`,
  `dotProduct_ne_zero_of_left_eigen`.
* P1.5 (averaging and growth): replaced by the frequency-free `Psc.BPrimeCore.window_sum_swap`,
  `avg_bound`, `len_growth`, `orbit_limit_bound`, `norm_le_one_of_bounded`.
* **Now closed by this module**: the composition of P0.2–P1.5 into the audit's corrected
  theorem (`bprime`, and `bprime_ss` with `I(W)` read as the literal recursion (3.1)), its
  cubic Pisot reading with minimal polynomial and integrality (`bprime_cubic_isPisot`,
  closing the "minimal polynomial not restated" item of `PscVerif.BPrimeCore`), Corollary
  B (i) (`corB_infinite`, `corB_infinite_cubic`, `corB_infinite_ss`) with the audit's
  negative control instantiated at a fixed point (`zetaU_IW_infinite`), and non-vacuity of
  B′ where its conclusion has content (two letters, irreducible `χ_M`, `I(0)` finite:
  `fib_control`, `fib_bprime`).
* Not addressed: P1.6 (sources and novelty) and P2.7 (the Quint model
  `proof/quint/BpaCutBound.qnt` is unchanged).

## Not proved here

* Corollary B (ii) and (iii) (they rest on R3 and R2), the pure-discrete-spectrum half of
  Sirvent–Solomyak Remark 2, and the remark after Corollary B that `I(W)` contains a
  noncoincident pair.
* Periodic points that are not fixed points (the audit's "passing to its fixing power"),
  `bpa` seeds other than prefixes of a fixed point, and the existence of a fixed point for a
  general primitive `σ` (only seeds `u₀ <+: σ(u₀)` are handled, `exists_isFixed_of_seed`).
* That `I(W)` is finite for any specimen on three letters with irreducible `χ_M`: in
  control (c) the termination of Tribonacci's `bpa-0` is not checked; the conclusion of B′
  there is proved independently (`trib_isPisot`).  The only irreducible specimen with a
  machine-checked finite `I(W)` is Fibonacci, on two letters (control (e)).
* Strict exclusion of the unit circle outside degree three: in degree two (true by hand, see
  "Hypotheses and their roles", but not stated) and in degree `≥ 4` (the Salem case, about
  which nothing is claimed).
* Novelty or priority, and any statement about C4, A1′, BH or PSC.
-/
import PscVerif.BPrimeCore
import PscVerif.BPrimeBinding

namespace Psc.BPrime

open Matrix Polynomial Psc.Binomial Psc.Incidence
open Psc.BPrimeBinding (IsFixed PrefixOf IW ssLevel)

/-! ### Pisot and Salem numbers -/

/-- `b` is a **Pisot number**: a real algebraic integer `b > 1` whose other conjugates over
`ℚ` (the other complex roots of its minimal polynomial) lie in the open unit disc. -/
def IsPisot (b : ℝ) : Prop :=
  1 < b ∧ IsIntegral ℤ b ∧ ∀ z : ℂ, aeval z (minpoly ℚ b) = 0 → z ≠ (b : ℂ) → ‖z‖ < 1

/-- `b` is a **Pisot or a Salem number**: a real algebraic integer `b > 1` whose other
conjugates over `ℚ` lie in the closed unit disc (a Salem number is one of these with a
conjugate on the unit circle). -/
def IsPisotOrSalem (b : ℝ) : Prop :=
  1 < b ∧ IsIntegral ℤ b ∧ ∀ z : ℂ, aeval z (minpoly ℚ b) = 0 → z ≠ (b : ℂ) → ‖z‖ ≤ 1

/-- A Pisot number is a Pisot or a Salem number. -/
theorem IsPisot.isPisotOrSalem {b : ℝ} (h : IsPisot b) : IsPisotOrSalem b :=
  ⟨h.1, h.2.1, fun z hz hzb => (h.2.2 z hz hzb).le⟩

section Charpoly

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Evaluating the rational `χ_M` at a point of a field `K ⊇ ℚ` is evaluating `χ` of `M`
cast to `K`. -/
theorem aeval_charpoly {K : Type*} [Field K] [Algebra ℚ K] (s : α → List α) (x : K) :
    aeval x ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly =
      ((inc s).map (Nat.cast : ℕ → K)).charpoly.eval x := by
  rw [aeval_def, ← eval_map, ← Matrix.charpoly_map]
  congr 2
  ext a c
  simp

/-- An irreducible `χ_M` is the minimal polynomial over `ℚ` of each of its real roots. -/
theorem minpoly_eq_charpoly (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {b : ℝ}
    (hb : ((inc s).map (Nat.cast : ℕ → ℝ)).charpoly.eval b = 0) :
    minpoly ℚ b = ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly :=
  (minpoly.eq_of_irreducible_of_monic hirr (by rw [aeval_charpoly]; exact hb)
    (Matrix.charpoly_monic _)).symm

/-- A real root of `χ_M` is an algebraic integer: `χ_M` is monic with integer
coefficients. -/
theorem isIntegral_of_root (s : α → List α) {b : ℝ}
    (hb : ((inc s).map (Nat.cast : ℕ → ℝ)).charpoly.eval b = 0) : IsIntegral ℤ b := by
  refine ⟨((inc s).map (Nat.cast : ℕ → ℤ)).charpoly, Matrix.charpoly_monic _, ?_⟩
  have e : ((inc s).map (Nat.cast : ℕ → ℤ)).map (algebraMap ℤ ℝ) =
      (inc s).map (Nat.cast : ℕ → ℝ) := by
    ext; simp
  rw [← eval_map, ← Matrix.charpoly_map, e]
  exact hb

/-- The eigenvalue of a positive left eigenvector of `M` is a root of `χ_M`. -/
theorem isRoot_of_pos_left_eigen [Nonempty α] (s : α → List α) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ((inc s).map (Nat.cast : ℕ → ℝ)).charpoly.eval β = 0 :=
  Psc.ConcentrationAlgebra.isRoot_of_left_eigen _ β ℓ
    (fun h => (hℓ (Classical.arbitrary α)).ne' (congrFun h _)) hℓM

/-- Reading the root bound of `χ_M` as a statement about the conjugates of `b`: with `χ_M`
irreducible, a real root `b > 1` all of whose companion roots lie in the closed unit disc is
a Pisot or a Salem number. -/
theorem isPisotOrSalem_of (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {b : ℝ} (hb1 : 1 < b)
    (hb : ((inc s).map (Nat.cast : ℕ → ℝ)).charpoly.eval b = 0)
    (h : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ (b : ℂ) →
      ‖z‖ ≤ 1) :
    IsPisotOrSalem b := by
  refine ⟨hb1, isIntegral_of_root s hb, fun z hz hzb => h z ?_ hzb⟩
  rwa [minpoly_eq_charpoly s hirr hb, aeval_charpoly] at hz

/-- As `isPisotOrSalem_of`, with the open unit disc: a Pisot number. -/
theorem isPisot_of (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {b : ℝ} (hb1 : 1 < b)
    (hb : ((inc s).map (Nat.cast : ℕ → ℝ)).charpoly.eval b = 0)
    (h : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ (b : ℂ) →
      ‖z‖ < 1) :
    IsPisot b := by
  refine ⟨hb1, isIntegral_of_root s hb, fun z hz hzb => h z ?_ hzb⟩
  rwa [minpoly_eq_charpoly s hirr hb, aeval_charpoly] at hz

end Charpoly

/-! ### The binding: fixed points and termination in the form `BPrimeCore` consumes -/

section Binding

variable {α : Type*} {s : α → List α} {u : ℕ → α} {W : List α}

/-- **The prefix hypothesis from a fixed point.**  If `u` is a one-sided fixed point of `σ`
(`IsFixed`: the image of every prefix of `u` is a prefix of `u`) and `W` is a prefix of `u`,
then every `σⁿ(W)` is a prefix of `u`, in the per-index form `hpre` of
`Psc.BPrimeCore.bprime_core` (`Psc.BPrimeBinding.prefixOf_iterate`). -/
theorem isPrefixOf_iterate (hfix : IsFixed s u) (hW : PrefixOf u W) (n : ℕ) :
    Psc.BPrimeCore.IsPrefixOf ((subst s)^[n] W) u :=
  Psc.BPrimeBinding.prefixOf_iff_getElem.1 (Psc.BPrimeBinding.prefixOf_iterate hfix hW n)

/-- **Audit step 1 in the form `Psc.BPrimeCore` consumes.**  For a fixed point of a
primitive `σ` with prefix `W`, a finite `I(W)` gives one `L` with the cut hypothesis
`CutGaps u |σⁿ W| L` at every level `n` (`Psc.BPrimeBinding.boundedGaps_of_finite_primitive`;
its `BoundedGaps` and `tn` are `CutGaps` and `len` by unfolding). -/
theorem cutGaps_of_finite [Fintype α] [DecidableEq α] (hfix : IsFixed s u) (hW : PrefixOf u W)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) (hfin : (IW s u W).Finite) :
    ∃ L, ∀ n, Psc.BPrimeCore.CutGaps u (Psc.BPrimeCore.len s W n) L :=
  Psc.BPrimeBinding.boundedGaps_of_finite_primitive hfix hW hprim hfin

/-- **Fixed points from `Psc.FixedPointLimit`.**  For a nonerasing `σ` (a primitive one is
nonerasing, `Psc.PrimitiveExpansion.nonerasing_of_primitive`) and a seed `u₀` with
`u₀ <+: σ(u₀)` and `|u₀| < |σ(u₀)|`, the limit word grown from `u₀`
(`Psc.BPrimeBinding.seedLimit`) is a one-sided fixed point with prefix `u₀`, so the
fixed-point hypotheses below are met by every such seed. -/
theorem exists_isFixed_of_seed [DecidableEq α] (hs : ∀ a, s a ≠ []) {u₀ : List α}
    (hu : u₀ <+: subst s u₀) (hlt : u₀.length < (subst s u₀).length) :
    ∃ u, IsFixed s u ∧ PrefixOf u u₀ :=
  ⟨_, Psc.BPrimeBinding.isFixed_seedLimit s u₀ hs hu hlt,
    Psc.BPrimeBinding.prefixOf_seedLimit s u₀ hs hu hlt⟩

end Binding

/-! ### Proposition B′ -/

section BPrime

variable {α : Type*} [Fintype α] [DecidableEq α] {s : α → List α} {u : ℕ → α} {W : List α}

/-- **Proposition B′** (the corrected theorem of the audit).  Let `σ = subst s` be primitive
(`Mᵏ > 0` for some `k ≥ 1`; nonerasing follows,
`Psc.PrimitiveExpansion.nonerasing_of_primitive`) on a finite alphabet, with `χ_M`
irreducible over `ℚ`; let `β` be its Perron root, given by a positive left eigenvector
`ℓ M = β ℓ` (which determines `β`, `Psc.PerronExistence.PerronData.left_nonneg`).  Let `u`
be a one-sided fixed point of `σ` and `W` a nonempty prefix of `u`.  If the
Sirvent–Solomyak `bpa-W` terminates (`I(W)` finite), then every complex root `z ≠ β` of
`χ_M` has `‖z‖ ≤ 1`. -/
theorem bprime (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ [])
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hfin : (IW s u W).Finite) {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) : ‖z‖ ≤ 1 := by
  obtain ⟨L, hL⟩ := cutGaps_of_finite hfix hW hprim hfin
  exact Psc.BPrimeCore.bprime_core s hWne (isPrefixOf_iterate hfix hW) hprim hirr L hL hℓ hℓM
    hz hzβ

/-- **Proposition B′ with the Perron data supplied** (`Psc.PerronExistence.perron_inc`):
there is a Perron root `β = ρ(M)` (`PerronData`) such that every other complex root of `χ_M`
lies in the closed unit disc. -/
theorem bprime_perron (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ [])
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hfin : (IW s u W).Finite) :
    ∃ (β : ℝ) (ℓ v : α → ℝ),
      Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧
        ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β → ‖z‖ ≤ 1 := by
  obtain ⟨L, hL⟩ := cutGaps_of_finite hfix hW hprim hfin
  exact Psc.BPrimeCore.bprime_core_perron s hWne (isPrefixOf_iterate hfix hW) hprim hirr L hL

/-- **Proposition B′, "so `β` is Pisot or Salem"**: on two or more letters the Perron root
is a real algebraic integer `β > 1` (`Psc.BPrimeCore.one_lt_perron`) with minimal
polynomial `χ_M` (`minpoly_eq_charpoly`), and all its other conjugates lie in the closed
unit disc. -/
theorem bprime_isPisotOrSalem [Nontrivial α] (hfix : IsFixed s u) (hW : PrefixOf u W)
    (hWne : W ≠ []) (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hfin : (IW s u W).Finite) {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) : IsPisotOrSalem β :=
  isPisotOrSalem_of s hirr (Psc.BPrimeCore.one_lt_perron s hprim hℓ hℓM)
    (isRoot_of_pos_left_eigen s hℓ hℓM)
    fun _ hz hzβ => bprime hfix hW hWne hprim hirr hfin hℓ hℓM hz hzβ

/-- **Proposition B′ on three letters** (audit step 6): if `χ_M` is an irreducible cubic,
then `β > 1` and every complex root `z ≠ β` of `χ_M` has `‖z‖ < 1`. -/
theorem bprime_cubic (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ [])
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3)
    (hfin : (IW s u W).Finite) {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    1 < β ∧ ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1 := by
  obtain ⟨L, hL⟩ := cutGaps_of_finite hfix hW hprim hfin
  exact Psc.BPrimeCore.bprime_core_cubic s hWne (isPrefixOf_iterate hfix hW) hprim hirr hdeg L
    hL hℓ hℓM

/-- **Proposition B′ on three letters, "so `χ_M` is Pisot"**: the Perron root is a Pisot
number, with minimal polynomial `χ_M`. -/
theorem bprime_cubic_isPisot (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ [])
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3)
    (hfin : (IW s u W).Finite) {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) : IsPisot β := by
  have : Nonempty α := ⟨W.head hWne⟩
  obtain ⟨h1, h⟩ := bprime_cubic hfix hW hWne hprim hirr hdeg hfin hℓ hℓM
  exact isPisot_of s hirr h1 (isRoot_of_pos_left_eigen s hℓ hℓM) h

/-- **Proposition B′ on three letters, Perron data supplied**: the Perron root `β = ρ(M)` of
`M` is a Pisot number. -/
theorem bprime_cubic_perron (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ [])
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3)
    (hfin : (IW s u W).Finite) :
    ∃ (β : ℝ) (ℓ v : α → ℝ),
      Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧ IsPisot β := by
  have : Nonempty α := ⟨W.head hWne⟩
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc s hprim
  exact ⟨β, ℓ, v, hP,
    bprime_cubic_isPisot hfix hW hWne hprim hirr hdeg hfin hP.left_pos hP.left⟩

/-! ### Corollary B (i): the balanced pair algorithm off the Pisot cone -/

/-- **Corollary B (i), any alphabet.**  Let `σ` be primitive with `χ_M` irreducible over
`ℚ`, and let some complex root `z` of `χ_M` other than the Perron root `β` satisfy
`‖z‖ > 1`.  Then for every one-sided fixed point `u` of `σ` and every nonempty prefix `W`
of `u`, the `bpa-W` does not terminate: `I(W)` is infinite. -/
theorem corB_infinite (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) (hz1 : 1 < ‖z‖)
    (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ []) : (IW s u W).Infinite :=
  fun hfin => (bprime hfix hW hWne hprim hirr hfin hℓ hℓM hz hzβ).not_gt hz1

/-- **Corollary B (i), any alphabet, Pisot–Salem form**: on two or more letters, if the
Perron root is neither a Pisot nor a Salem number, no prefix-seeded `bpa-W` terminates. -/
theorem corB_infinite_of_not_isPisotOrSalem [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hnot : ¬ IsPisotOrSalem β) (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ []) :
    (IW s u W).Infinite :=
  fun hfin => hnot (bprime_isPisotOrSalem hfix hW hWne hprim hirr hfin hℓ hℓM)

/-- **Corollary B (i) on three letters**: if `σ` is primitive with `χ_M` an irreducible,
non-Pisot cubic (its Perron root is not a Pisot number), then for every one-sided fixed point
`u` and every nonempty prefix `W` of `u`, `I(W)` is infinite. -/
theorem corB_infinite_cubic (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hnot : ¬ IsPisot β) (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ []) :
    (IW s u W).Infinite :=
  fun hfin => hnot (bprime_cubic_isPisot hfix hW hWne hprim hirr hdeg hfin hℓ hℓM)

/-! ### The literal recursion (3.1) -/

/-- **Proposition B′ with `I(W)` read literally**: as `bprime`, with termination stated on
the union of Sirvent–Solomyak's recursive levels (3.1) (`ssLevel`: start with the reduction
of `(u, S^{|W|} u)`, then reduce all substituted pairs, coincidence blocks included) instead
of the window-defined `IW`.  The two sets are equal
(`Psc.BPrimeBinding.IW_eq_iUnion_ssLevel`). -/
theorem bprime_ss (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ [])
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hfin : (⋃ n, ssLevel s u W n).Finite) {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) : ‖z‖ ≤ 1 :=
  bprime hfix hW hWne hprim hirr (Psc.BPrimeBinding.IW_eq_iUnion_ssLevel hfix hW hprim ▸ hfin)
    hℓ hℓM hz hzβ

/-- **Corollary B (i), any alphabet, with `I(W)` read literally**: under the hypotheses of
`corB_infinite`, the union of the recursive levels (3.1) is infinite. -/
theorem corB_infinite_ss (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) (hz1 : 1 < ‖z‖)
    (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ []) :
    (⋃ n, ssLevel s u W n).Infinite := by
  rw [Psc.BPrimeBinding.IW_eq_iUnion_ssLevel hfix hW hprim]
  exact corB_infinite hprim hirr hℓ hℓM hz hzβ hz1 hfix hW hWne

/-- **Corollary B (i) on three letters, with `I(W)` read literally**: under the hypotheses of
`corB_infinite_cubic`, the union of the recursive levels (3.1) is infinite. -/
theorem corB_infinite_cubic_ss (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hnot : ¬ IsPisot β) (hfix : IsFixed s u) (hW : PrefixOf u W) (hWne : W ≠ []) :
    (⋃ n, ssLevel s u W n).Infinite := by
  rw [Psc.BPrimeBinding.IW_eq_iUnion_ssLevel hfix hW hprim]
  exact corB_infinite_cubic hprim hirr hdeg hℓ hℓM hnot hfix hW hWne

end BPrime

/-! ### Control (a): the audit specimen `0 ↦ 01`, `1 ↦ 2`, `2 ↦ 00` -/

section Zeta

open Psc.BPrimeCore (zetaSubst zeta_primitive zeta_irreducible zeta_root_outside)

/-- The fixed point `σ^ω(0) = 0120001…` of the specimen: the limit word grown from
`0 <+: σ(0) = 01` (`Psc.BPrimeBinding.seedLimit`). -/
noncomputable def zetaU : ℕ → Fin 3 :=
  Psc.BPrimeBinding.seedLimit zetaSubst [0] (by decide) (by decide) (by decide)

/-- `zetaU` is a one-sided fixed point. -/
theorem zetaU_isFixed : IsFixed zetaSubst zetaU := Psc.BPrimeBinding.isFixed_seedLimit _ _ _ _ _

/-- `0` is a prefix of `zetaU`. -/
theorem zetaU_prefix : PrefixOf zetaU [0] := Psc.BPrimeBinding.prefixOf_seedLimit _ _ _ _ _

/-- Primitivity of the specimen in the form of the hypotheses (`M⁴ > 0`,
`Psc.BPrimeCore.zeta_primitive`). -/
theorem zeta_prim : ∃ k ≥ 1, ∀ a c, 0 < (inc zetaSubst ^ k) a c :=
  ⟨4, by norm_num, zeta_primitive.1⟩

/-- The Perron root of the specimen is neither a Pisot nor a Salem number: a non-Perron root
has modulus `> 1` (`Psc.BPrimeCore.zeta_root_outside`, by the product of the roots). -/
theorem zeta_not_isPisotOrSalem {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc zetaSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) : ¬ IsPisotOrSalem β := by
  intro hP
  have hroot := isRoot_of_pos_left_eigen zetaSubst hℓ hℓM
  obtain ⟨z, hz, hzβ, hz1⟩ := zeta_root_outside (by linarith [hP.1]) hroot
  refine (hP.2.2 z ?_ hzβ).not_gt hz1
  rw [minpoly_eq_charpoly zetaSubst zeta_irreducible hroot, aeval_charpoly]
  exact hz

/-- The Perron root of the specimen is not a Pisot number. -/
theorem zeta_not_isPisot {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc zetaSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) : ¬ IsPisot β :=
  fun hP => zeta_not_isPisotOrSalem hℓ hℓM hP.isPisotOrSalem

/-- **Every hypothesis of Corollary B (i) holds for the specimen**, at the fixed point
`zetaU` with `W = 0`: fixed point, prefix, `W ≠ []`, primitivity (`M⁴ > 0`), irreducibility
(rational root test), degree `3`, and a Perron root that is not Pisot, with a non-Perron
root outside the closed unit disc. -/
theorem zeta_control :
    IsFixed zetaSubst zetaU ∧ PrefixOf zetaU [0] ∧ ([0] : List (Fin 3)) ≠ [] ∧
      (∃ k ≥ 1, ∀ a c, 0 < (inc zetaSubst ^ k) a c) ∧
      Irreducible ((inc zetaSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      ((inc zetaSubst).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3 ∧
      ∃ (β : ℝ) (ℓ v : Fin 3 → ℝ),
        Psc.PerronExistence.PerronData ((inc zetaSubst).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧
          ¬ IsPisot β ∧ ∃ z : ℂ, ((inc zetaSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 ∧
            z ≠ β ∧ 1 < ‖z‖ := by
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc zetaSubst zeta_prim
  exact ⟨zetaU_isFixed, zetaU_prefix, List.cons_ne_nil _ _, zeta_prim, zeta_irreducible,
    Psc.Degree4Floor.natDegree_charpoly _, β, ℓ, v, hP, zeta_not_isPisot hP.left_pos hP.left,
    zeta_root_outside hP.pos hP.isRoot⟩

/-- **Corollary B (i) for the specimen**: for every one-sided fixed point `u` of
`0 ↦ 01, 1 ↦ 2, 2 ↦ 00` and every nonempty prefix `W` of `u`, `bpa-W` does not terminate
(from `corB_infinite_cubic`). -/
theorem zeta_IW_infinite {u : ℕ → Fin 3} {W : List (Fin 3)} (hfix : IsFixed zetaSubst u)
    (hW : PrefixOf u W) (hWne : W ≠ []) : (IW zetaSubst u W).Infinite := by
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc zetaSubst zeta_prim
  exact corB_infinite_cubic zeta_prim zeta_irreducible (Psc.Degree4Floor.natDegree_charpoly _)
    hP.left_pos hP.left (zeta_not_isPisot hP.left_pos hP.left) hfix hW hWne

/-- **The audit's negative control, instantiated**: the `bpa-0` of the fixed point
`zetaU = σ^ω(0)` does not terminate. -/
theorem zetaU_IW_infinite : (IW zetaSubst zetaU [0]).Infinite :=
  zeta_IW_infinite zetaU_isFixed zetaU_prefix (List.cons_ne_nil _ _)

/-- **The same, from the any-alphabet `corB_infinite`**, with no degree hypothesis: the
non-Perron root of modulus `> 1` (`Psc.BPrimeCore.zeta_root_outside`) is the witness. -/
theorem zetaU_IW_infinite_of_root : (IW zetaSubst zetaU [0]).Infinite := by
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc zetaSubst zeta_prim
  obtain ⟨z, hz, hzβ, hz1⟩ := zeta_root_outside hP.pos hP.isRoot
  exact corB_infinite zeta_prim zeta_irreducible hP.left_pos hP.left hz hzβ hz1 zetaU_isFixed
    zetaU_prefix (List.cons_ne_nil _ _)

/-- **The same, from `corB_infinite_of_not_isPisotOrSalem`**: the Perron root is neither
Pisot nor Salem (`zeta_not_isPisotOrSalem`). -/
theorem zetaU_IW_infinite_of_not_isPisotOrSalem : (IW zetaSubst zetaU [0]).Infinite := by
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc zetaSubst zeta_prim
  exact corB_infinite_of_not_isPisotOrSalem zeta_prim zeta_irreducible hP.left_pos hP.left
    (zeta_not_isPisotOrSalem hP.left_pos hP.left) zetaU_isFixed zetaU_prefix
    (List.cons_ne_nil _ _)

/-- **The audit's negative control, with `I(0)` read literally**: Sirvent–Solomyak's
recursion (3.1) for `bpa-0` of `zetaU` never closes up (`corB_infinite_cubic_ss`). -/
theorem zetaU_ssLevel_infinite : (⋃ n, ssLevel zetaSubst zetaU [0] n).Infinite := by
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc zetaSubst zeta_prim
  exact corB_infinite_cubic_ss zeta_prim zeta_irreducible
    (Psc.Degree4Floor.natDegree_charpoly _) hP.left_pos hP.left
    (zeta_not_isPisot hP.left_pos hP.left) zetaU_isFixed zetaU_prefix (List.cons_ne_nil _ _)

end Zeta

/-! ### Control (b): irreducibility in the nonvanishing step -/

section Reducible

/-- The primitive substitution `0 ↦ 0001`, `1 ↦ 0111`, with incidence matrix
`[[3,1],[1,3]]` (`Psc.BPrimeCore.ctrlM`). -/
def ctrlSubst : Fin 2 → List (Fin 2) := ![[0, 0, 0, 1], [0, 1, 1, 1]]

/-- `ctrlSubst` realizes `Psc.BPrimeCore.ctrlM`: its rational incidence matrix is
`[[3,1],[1,3]]`. -/
theorem ctrlSubst_inc : (inc ctrlSubst).map (Nat.cast : ℕ → ℚ) = Psc.BPrimeCore.ctrlM := by
  have h : inc ctrlSubst = Matrix.of ![![3, 1], ![1, 3]] := by decide
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Psc.BPrimeCore.ctrlM]

/-- **Negative control: irreducibility cannot be dropped from audit step 4**, realized by
a substitution.  `0 ↦ 0001, 1 ↦ 0111` is primitive with reducible `χ_M = (X - 2)(X - 4)`,
and the nonempty word `W = 01` has Parikh vector `(1, 1)`, killed by the left eigenvector
`q = (1, -1)` of the non-Perron root `2 > 1`: the coefficient `q · w` that the spectral step
divides by vanishes (`Psc.BPrimeCore.irreducibility_needed`).  This is not a counterexample
to Proposition B′: `01` is not a prefix of the fixed point `σ^ω(0)`, and no `I(W)` of this
substitution is computed here. -/
theorem reducible_control :
    (∃ k ≥ 1, ∀ a c, 0 < (inc ctrlSubst ^ k) a c) ∧
      ¬ Irreducible ((inc ctrlSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      ([0, 1] : List (Fin 2)) ≠ [] ∧ (![1, -1] : Fin 2 → ℚ) ≠ 0 ∧
      (![1, -1] : Fin 2 → ℚ) ᵥ* (inc ctrlSubst).map (Nat.cast : ℕ → ℚ) = (2 : ℚ) • ![1, -1] ∧
      (![1, -1] : Fin 2 → ℚ) ⬝ᵥ Psc.BPrimeCore.parikhCast [0, 1] = 0 := by
  obtain ⟨-, hirr, heig, hdot, -, hne⟩ := Psc.BPrimeCore.irreducibility_needed
  have hw : (Psc.BPrimeCore.parikhCast ([0, 1] : List (Fin 2)) : Fin 2 → ℚ) = ![1, 1] := by
    ext i
    fin_cases i <;> simp [Psc.BPrimeCore.parikhCast, Psc.ParikhIntertwiner.parikh]
  rw [ctrlSubst_inc, hw]
  exact ⟨⟨1, le_rfl, fun a c => by fin_cases a <;> fin_cases c <;> decide +kernel⟩, hirr,
    List.cons_ne_nil _ _, hne, heig, hdot⟩

end Reducible

/-! ### Control (c): a Pisot instance meeting every hypothesis except finiteness -/

section Tribonacci

open Psc.Descendants (tribSubst)

/-- The incidence matrix `[[1,1,1],[1,0,0],[0,1,0]]` of Tribonacci `0 ↦ 01, 1 ↦ 02, 2 ↦ 0`
(`Psc.Descendants.tribSubst`). -/
theorem trib_inc : inc tribSubst = Matrix.of ![![1, 1, 1], ![1, 0, 0], ![0, 1, 0]] := by
  decide

/-- **Primitivity**: `M³ > 0`. -/
theorem trib_primitive : ∀ a c, 0 < (inc tribSubst ^ 3) a c := fun a c => by
  rw [trib_inc]; fin_cases a <;> fin_cases c <;> decide +kernel

/-- Primitivity of Tribonacci in the form of the hypotheses. -/
theorem trib_prim : ∃ k ≥ 1, ∀ a c, 0 < (inc tribSubst ^ k) a c := ⟨3, by norm_num, trib_primitive⟩

/-- `χ_M = X³ - X² - X - 1` over every commutative ring. -/
theorem trib_charpoly (K : Type*) [CommRing K] :
    ((inc tribSubst).map (Nat.cast : ℕ → K)).charpoly = X ^ 3 - X ^ 2 - X - 1 := by
  rw [Psc.Cyclicity.charpoly_fin_three, trib_inc]
  simp [Matrix.trace_fin_three, Matrix.det_fin_three, Psc.Cyclicity.wedge2,
    Psc.Cyclicity.pairFst, Psc.Cyclicity.pairSnd]
  ring

/-- `χ_M` is irreducible over `ℚ` (rational root test, `Psc.BPrimeCore.irreducible_cubic`:
`±1` are not roots). -/
theorem trib_irreducible : Irreducible ((inc tribSubst).map (Nat.cast : ℕ → ℚ)).charpoly := by
  rw [trib_charpoly]
  convert Psc.BPrimeCore.irreducible_cubic (-1) (-1) (-1) (by decide) using 1
  simp
  ring1

/-- The Tribonacci fixed point `σ^ω(0) = 0102010…`: the limit word grown from
`0 <+: σ(0) = 01` (`Psc.BPrimeBinding.seedLimit`). -/
noncomputable def tribU : ℕ → Fin 3 :=
  Psc.BPrimeBinding.seedLimit tribSubst [0] (by decide) (by decide) (by decide)

/-- `tribU` is a one-sided fixed point. -/
theorem tribU_isFixed : IsFixed tribSubst tribU := Psc.BPrimeBinding.isFixed_seedLimit _ _ _ _ _

/-- `0` is a prefix of `tribU`. -/
theorem tribU_prefix : PrefixOf tribU [0] := Psc.BPrimeBinding.prefixOf_seedLimit _ _ _ _ _

/-- **The Tribonacci polynomial is Pisot at its real root `β > 1`**: every other complex
root `z` has `‖z‖ < 1`.  A real root `x ≠ β` is impossible (`x ≤ 1` gives
`x³ - x² - x - 1 < 0`, and two real roots `> 1` would make
`x² + xβ + β² - x - β - 1 = 0`), so `z` is non-real; then `z` and `z̄` are the two roots other
than `β` (`Psc.Degree4Floor.exists_other_roots`), and `β ‖z‖² = β z z̄ = det M = 1`
(`Psc.SectorBridge.det_eq_mul_roots`). -/
theorem trib_norm_lt {β : ℝ} (hβ1 : 1 < β)
    (hβ : ((inc tribSubst).map (Nat.cast : ℕ → ℝ)).charpoly.eval β = 0) {z : ℂ}
    (hz : ((inc tribSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) :
    ‖z‖ < 1 := by
  set MQ := (inc tribSubst).map (Nat.cast : ℕ → ℚ)
  have hev : ∀ w : ℂ, aeval w MQ.charpoly = w ^ 3 - w ^ 2 - w - 1 := fun w => by
    rw [trib_charpoly]; simp
  rw [trib_charpoly] at hβ hz
  simp only [eval_sub, eval_pow, eval_X, eval_one] at hβ hz
  have him : z.im ≠ 0 := by
    intro him
    have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
    have hx : z.re ^ 3 - z.re ^ 2 - z.re - 1 = 0 := by
      have h := hz
      rw [hzr] at h
      exact_mod_cast h
    have hxβ : z.re ≠ β := fun h => hzβ (by rw [hzr, h])
    have hx1 : 1 < z.re := by
      by_contra h
      push Not at h
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h) (sq_nonneg (z.re + 1)),
        sq_nonneg z.re]
    have hq : z.re ^ 2 + z.re * β + β ^ 2 - (z.re + β) - 1 = 0 := by
      have h : (z.re - β) * (z.re ^ 2 + z.re * β + β ^ 2 - (z.re + β) - 1) = 0 := by
        linear_combination hx - hβ
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hxβ)
    nlinarith [mul_pos (sub_pos.2 hx1) (sub_pos.2 hβ1)]
  have hconj : starRingEnd ℂ z ^ 3 - starRingEnd ℂ z ^ 2 - starRingEnd ℂ z - 1 = 0 := by
    simpa using congrArg (starRingEnd ℂ) hz
  have hne1 : starRingEnd ℂ z ≠ z := fun h => him (Complex.conj_eq_iff_im.1 h)
  have hne2 : starRingEnd ℂ z ≠ β := fun h => hzβ (by
    have h' := congrArg (starRingEnd ℂ) h
    rwa [Complex.conj_ofReal, Complex.conj_conj] at h')
  have hβC : aeval (β : ℂ) MQ.charpoly = 0 := by rw [hev]; exact_mod_cast hβ
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, hall⟩ :=
    Psc.Degree4Floor.exists_other_roots MQ trib_irreducible hβC
  have hdet := Psc.SectorBridge.det_eq_mul_roots MQ hβC hα hγ hβα hβγ hαγ
  have hdet1 : MQ.det = 1 := by simp [MQ, trib_inc, Matrix.det_fin_three]
  rw [hdet1, Rat.cast_one] at hdet
  have hprod : (β : ℂ) * (z * starRingEnd ℂ z) = 1 := by
    rcases hall z (by rw [hev]; exact hz) with h | h | h
    · exact absurd h hzβ
    · rcases hall _ (by rw [hev]; exact hconj) with h' | h' | h'
      · exact absurd h' hne2
      · exact absurd (h'.trans h.symm) hne1
      · rw [h', h]; linear_combination -hdet
    · rcases hall _ (by rw [hev]; exact hconj) with h' | h' | h'
      · exact absurd h' hne2
      · rw [h', h]; linear_combination -hdet
      · exact absurd (h'.trans h.symm) hne1
  have hn : β * ‖z‖ ^ 2 = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hprod
    exact_mod_cast hprod
  by_contra h
  push Not at h
  have h2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
  nlinarith

/-- **The Perron root of Tribonacci is a Pisot number** (proved directly, without any
statement about its `bpa`). -/
theorem trib_isPisot {β : ℝ} {ℓ : Fin 3 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) : IsPisot β := by
  have hroot := isRoot_of_pos_left_eigen tribSubst hℓ hℓM
  have hβ1 : 1 < β := Psc.BPrimeCore.one_lt_perron tribSubst trib_prim hℓ hℓM
  exact isPisot_of tribSubst trib_irreducible hβ1 hroot fun _ hz hzβ =>
    trib_norm_lt hβ1 hroot hz hzβ

/-- **Positive control: every hypothesis of `bprime_cubic_isPisot` except finiteness** holds
for Tribonacci at its fixed point `tribU` with `W = 0` (fixed point, prefix, `W ≠ []`,
`M³ > 0`, irreducible cubic `χ_M`), and the conclusion holds: the Perron root is a Pisot
number (`trib_isPisot`).  Whether `I(0)` is finite (the termination of this `bpa-0`) is not
checked in Lean. -/
theorem trib_control :
    IsFixed tribSubst tribU ∧ PrefixOf tribU [0] ∧ ([0] : List (Fin 3)) ≠ [] ∧
      (∃ k ≥ 1, ∀ a c, 0 < (inc tribSubst ^ k) a c) ∧
      Irreducible ((inc tribSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      ((inc tribSubst).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3 ∧
      ∃ (β : ℝ) (ℓ v : Fin 3 → ℝ),
        Psc.PerronExistence.PerronData ((inc tribSubst).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧
          IsPisot β := by
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc tribSubst trib_prim
  exact ⟨tribU_isFixed, tribU_prefix, List.cons_ne_nil _ _, trib_prim, trib_irreducible,
    Psc.Degree4Floor.natDegree_charpoly _, β, ℓ, v, hP, trib_isPisot hP.left_pos hP.left⟩

/-- **Why control (c) is Tribonacci and not the plastic substitution**: the plastic
substitution `0 ↦ 1, 1 ↦ 2, 2 ↦ 01` (`Psc.Degree2Sector.plasticSubst`) has no one-sided
fixed point, since no image begins with its own letter (a fixed point `u` has `σ(u 0)` as a
prefix).  Its prefix-seeded `bpa-W` is outside the scope of `bprime` (only periodic points
exist, the audit's "passing to its fixing power"). -/
theorem plastic_not_isFixed (u : ℕ → Fin 3) : ¬ IsFixed Psc.Degree2Sector.plasticSubst u := by
  intro hfix
  have hw : Psc.BPrimeBinding.win u 0 1 = [u 0] := by simp [Psc.BPrimeBinding.win]
  have h1 := hfix 1
  rw [hw] at h1
  have h := Psc.BPrimeBinding.prefixOf_iff_getElem.1 h1 0
  revert h
  generalize u 0 = a
  fin_cases a <;> simp [subst, Psc.Degree2Sector.plasticSubst]

end Tribonacci

/-! ### Control (d): the full hypothesis set of `bprime`, finiteness included, is satisfiable -/

section OneLetter

open Psc.BPrimeCore (oneSubst)

/-- Every word over one letter is a prefix of `0^∞`. -/
theorem prefixOf_fin_one (x : List (Fin 1)) : PrefixOf (fun _ => (0 : Fin 1)) x :=
  List.ext_getElem (by simp) fun _ _ _ => Subsingleton.elim _ _

/-- Over one letter the only irreducible balanced block is `(0, 0)`: two balanced words
have equal length, hence are equal, and a block of length `≥ 2` would reduce at `1`. -/
theorem isBlock_fin_one {T : List (Fin 1) × List (Fin 1)} (hT : Psc.Reduction.IsBlock T) :
    T = ([0], [0]) := by
  obtain ⟨h1, h2, h3⟩ := hT
  have hcount : ∀ l : List (Fin 1), l.count 0 = l.length := fun l =>
    List.count_eq_length.2 fun b _ => Subsingleton.elim _ _
  have hlen : T.1.length = T.2.length := by rw [← hcount, ← hcount]; exact h2 0
  have heq : ∀ l l' : List (Fin 1), l.length = l'.length → l = l' := fun l l' h =>
    List.ext_getElem h fun _ _ _ => Subsingleton.elim _ _
  have hle : T.1.length ≤ 1 := by
    by_contra hgt
    push Not at hgt
    exact h3 1 one_pos hgt fun a => by
      rw [heq (T.1.take 1) (T.2.take 1) (by simp [hlen])]
  have h1len : T.1.length = 1 := by
    have : T.1.length ≠ 0 := fun h => h1 (List.length_eq_zero_iff.1 h)
    omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h1len
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 (hlen ▸ h1len)
  rw [Prod.ext_iff, ha, hb, Subsingleton.elim a 0, Subsingleton.elim b 0]
  exact ⟨rfl, rfl⟩

/-- **Positive control: every hypothesis of `bprime` holds at once**, the finiteness of
`I(W)` included, for `σ = (0 ↦ 00)` (`Psc.BPrimeCore.oneSubst`), its fixed point `0^∞` and
`W = 0`: `I(0) ⊆ {(0, 0)}` (`isBlock_fin_one`).  The conclusion is empty here, since `χ_M =
X - 2` has no root other than `β = 2`.  On two letters, `Psc.BPrimeBinding.per_control`
(`0 ↦ 01, 1 ↦ 01`, reducible `χ_M`) meets every hypothesis of B′ except irreducibility, and
control (e) (Fibonacci) meets all of them with a nonempty conclusion. -/
theorem one_letter_control :
    IsFixed oneSubst (fun _ => (0 : Fin 1)) ∧ PrefixOf (fun _ => (0 : Fin 1)) [0] ∧
      ([0] : List (Fin 1)) ≠ [] ∧ (∃ k ≥ 1, ∀ a c, 0 < (inc oneSubst ^ k) a c) ∧
      Irreducible ((inc oneSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (IW oneSubst (fun _ => (0 : Fin 1)) [0]).Finite := by
  obtain ⟨-, hprim, hirr, -, -⟩ := Psc.BPrimeCore.one_letter_consistent
  refine ⟨fun N => prefixOf_fin_one _, prefixOf_fin_one _, List.cons_ne_nil _ _, hprim, hirr,
    (Set.finite_singleton (([0], [0]) : List (Fin 1) × List (Fin 1))).subset fun T hT => ?_⟩
  exact isBlock_fin_one (Psc.BPrimeBinding.IW_isBlock T hT)

end OneLetter

/-! ### Control (e): Fibonacci, every hypothesis of `bprime` with an irreducible `χ_M` -/

section Fibonacci

open Psc.Descendants (fibSubst)
open Psc.BPrimeBinding (fibU fibU_isFixed fibU_prefix fib_primitive fib_terminates)

/-- The incidence matrix `[[1,1],[1,0]]` of Fibonacci `0 ↦ 01, 1 ↦ 0`
(`Psc.Descendants.fibSubst`). -/
theorem fib_inc : inc fibSubst = Matrix.of ![![1, 1], ![1, 0]] := by decide

/-- `χ_M = X² - X - 1` over every nontrivial commutative ring. -/
theorem fib_charpoly (K : Type*) [CommRing K] [Nontrivial K] :
    ((inc fibSubst).map (Nat.cast : ℕ → K)).charpoly = X ^ 2 - X - 1 := by
  rw [Matrix.charpoly_fin_two, fib_inc]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]
  ring1

/-- `χ_M` is irreducible over `ℚ`: a rational root `x` would make `(2x - 1)² = 5` a
rational square, which `5` is not (`decide +kernel`). -/
theorem fib_irreducible : Irreducible ((inc fibSubst).map (Nat.cast : ℕ → ℚ)).charpoly := by
  rw [fib_charpoly]
  have hdeg : (X ^ 2 - X - 1 : ℚ[X]).natDegree = 2 := by compute_degree!
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) fun x hx => ?_
  have h5 : IsSquare (5 : ℚ) := ⟨2 * x - 1, by
    simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_one] at hx
    linear_combination (-4 : ℚ) * hx⟩
  exact absurd h5 (by decide +kernel)

/-- **The conclusion of B′ is not empty on Fibonacci**: for a real root `β` of `χ_M`, the
conjugate `1 - β` (sum of the roots `= tr M = 1`) is a root of `χ_M` different from `β`
(`β = 1/2` is not a root). -/
theorem fib_conj {β : ℝ} (hβ : ((inc fibSubst).map (Nat.cast : ℕ → ℝ)).charpoly.eval β = 0) :
    ((inc fibSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval ((1 - β : ℝ) : ℂ) = 0 ∧
      ((1 - β : ℝ) : ℂ) ≠ β := by
  rw [fib_charpoly] at hβ ⊢
  simp only [eval_sub, eval_pow, eval_X, eval_one] at hβ ⊢
  have hβC : (β : ℂ) ^ 2 - β - 1 = 0 := by exact_mod_cast hβ
  refine ⟨by push_cast; linear_combination hβC, fun h => ?_⟩
  have h' : 1 - β = β := Complex.ofReal_injective h
  have : β = 1 / 2 := by linarith
  rw [this] at hβ
  norm_num at hβ

/-- **Positive control with content: every hypothesis of `bprime` holds on Fibonacci**, with
an irreducible `χ_M` and the finiteness of `I(W)` included: `0 ↦ 01, 1 ↦ 0`, its fixed
point `fibU`, `W = 0`; `M² > 0`, `χ_M = X² - X - 1` irreducible, and `I(0)` finite
(`Psc.BPrimeBinding.fib_terminates`).  The Perron root `β` has the conjugate root
`1 - β ≠ β`, so the conclusion of `bprime` is not empty (`fib_bprime`). -/
theorem fib_control :
    IsFixed fibSubst fibU ∧ PrefixOf fibU [0] ∧ ([0] : List (Fin 2)) ≠ [] ∧
      (∃ k ≥ 1, ∀ a c, 0 < (inc fibSubst ^ k) a c) ∧
      Irreducible ((inc fibSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (IW fibSubst fibU [0]).Finite ∧
      ∃ (β : ℝ) (ℓ v : Fin 2 → ℝ),
        Psc.PerronExistence.PerronData ((inc fibSubst).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧
          ((inc fibSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval ((1 - β : ℝ) : ℂ) = 0 ∧
            ((1 - β : ℝ) : ℂ) ≠ β := by
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc fibSubst fib_primitive
  exact ⟨fibU_isFixed, fibU_prefix, List.cons_ne_nil _ _, fib_primitive, fib_irreducible,
    fib_terminates.2, β, ℓ, v, hP, fib_conj hP.isRoot⟩

/-- **Proposition B′ applied on Fibonacci**: from the termination of `bpa-0`
(`Psc.BPrimeBinding.fib_terminates`), `bprime` places the conjugate `1 - β` of the Perron
root in the closed unit disc. -/
theorem fib_bprime {β : ℝ} {ℓ : Fin 2 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) : ‖((1 - β : ℝ) : ℂ)‖ ≤ 1 :=
  have hc := fib_conj (isRoot_of_pos_left_eigen fibSubst hℓ hℓM)
  bprime fibU_isFixed fibU_prefix (List.cons_ne_nil _ _) fib_primitive fib_irreducible
    fib_terminates.2 hℓ hℓM hc.1 hc.2

/-- **"So `β` is Pisot or Salem", on Fibonacci**, through `bprime_isPisotOrSalem`. -/
theorem fib_isPisotOrSalem {β : ℝ} {ℓ : Fin 2 → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc fibSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ) : IsPisotOrSalem β :=
  bprime_isPisotOrSalem fibU_isFixed fibU_prefix (List.cons_ne_nil _ _) fib_primitive
    fib_irreducible fib_terminates.2 hℓ hℓM

end Fibonacci

end Psc.BPrime
