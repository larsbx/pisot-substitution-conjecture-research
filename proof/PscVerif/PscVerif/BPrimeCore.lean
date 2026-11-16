/-
# Proposition B′: the analytic and algebraic core (audit steps 2–6)

`docs/c4-general-structure-2026-11-06.md` §3, **Proposition B′** (termination forces the
conjugates into the disc) and **Corollary B** (i);
`docs/c4-bprime-independent-proof-audit-2026-11-07.md`, "Independent proof" steps 2–6, the
assumption inventory, and acceptance-matrix items P0.2 (bounded-block cancellation, with the
off-by-one at each block end), P1.4 (algebraic cyclicity) and P1.5 (averaging and growth);
`docs/c4-bprime-machine-verification-priority-2026-11-07.md`, derivation items 2–6.
`proof/bpa/BpaPrefixBridge.lean` (`PscVerif.BpaPrefixBridge.shift_factor_identity`) is
restated here as `shift_factor_identity`; `proof/quint/BpaCutBound.qnt` is the bounded
one-coordinate model of the cut bound that `cut_bound` and `cut_bound_of_blocks` replace by
the unbounded multi-letter statement; `tools/audit_bpa_bprime.py` is the numerical control
for the specimen `0 ↦ 01, 1 ↦ 2, 2 ↦ 00` of the last sections.

Setting.  An alphabet `α` (a `Fintype` with decidable equality where needed), an infinite
word `u : ℕ → α`, its prefix Parikh vector `P u k a = |u[0,k)|_a` (values in `ℤ`), the
discrepancy `D u t k = P k - (P (t + k) - P t)` between the prefixes of `u` and of its shift
`Sᵗ u`, the cut-gap predicate `CutGaps u t L` (from every position a common cut, a zero of
every coordinate of `D u t`, within `L` letters), a substitution `s : α → List α`
(`σ = subst s`) with incidence matrix `M = Psc.Incidence.inc s` (cast to `ℤ`, `ℚ`, `ℝ`, `ℂ`),
a word `W` with Parikh vector `w = parikhCast W` (the cast of
`Psc.ParikhIntertwiner.parikh W`), and the lengths `t n = len s W n = |σⁿ(W)|`.

## Proved here, in full

* **(a) Cut bound** (audit step 2, P0.2): `shift_factor_identity`, `D_eq_factor`
  (`D u t k = P t - (P (k + t) - P k)`); `D_zero` (`D u t 0 = 0` holds automatically);
  `D_succ`, `D_add` (a balanced aligned block carries a cut to a cut); `abs_D_sub_le` (each
  coordinate of `D` moves by at most one per letter); **`cut_bound`** (`CutGaps u t L` gives
  `|D u t k a| ≤ L` for all `k`, `a`); `block_bound` (between cuts `j ≤ k ≤ j'`:
  `|D| ≤ min (k - j) (j' - k)`, `2 |D| ≤ j' - j`); **`exists_cut_of_blocks`**,
  `cutGaps_of_blocks` and **`cut_bound_of_blocks`** (aligned blocks of length `≤ L`, cuts
  `c 0 = 0 < c 1 < ⋯`: a cut lies in `[k, k + L)` and `|D| < L`, strictly, since `D`
  vanishes at each block end).
* **(b) Fixed-point lengths**: `IsPrefixOf`; `P_length_of_prefix`; `parikh_iterate`
  (`p(σⁿ W) = Mⁿ p(W)`, the iterate of `Psc.ParikhIntertwiner.parikh_subst`),
  `count_iterate_cast`, `sum_count_eq_length`, `length_iterate_cast` (`t n` is the
  coordinate sum of `Mⁿ w`); **`P_iterate`** (`σⁿ(W)` a prefix of `u` gives
  `P u (t n) = Mⁿ w`); `isPrefixOf_limit` (the limit word of `Psc.FixedPointLimit` with
  `p = 1` meets the hypothesis).
* **(c) Averaging without frequencies** (replaces audit step 3): `window_sum_swap`
  (`Σ_{k<K} (P (k+t) - P k) = Σ_{j<t} (P (K+j) - P j)`); **`avg_bound`**
  (`|K · P t - t · P K| ≤ K L + t²` coordinatewise, from `|D u t ·| ≤ L`; with
  `P (t n) = Mⁿ w` this is `|K · Mⁿ w - t n · P K| ≤ K L + (t n)²`); `vecMul_pow_eigen`;
  **`eigen_window_bound`** (for `q ᵥ* M = z • q` over `ℂ` and `K = t m`:
  `‖t m zⁿ q(w) - t n zᵐ q(w)‖ ≤ (t m L + (t n)²) ‖q‖₁`).  No letter frequencies, Cesàro
  limits or uniform convergence enter.
* **(d) Growth and strict dominance**: **`len_growth`** (`ℓ > 0`, `ℓ M = β ℓ`, `W ≠ []`:
  `t m ≥ c βᵐ` with `c > 0`); `one_lt_perron` (`β > 1` on two or more letters for primitive
  `M`; irreducibility is not needed); **`norm_lt_perron`** (primitive `M`: every complex root
  `z ≠ β` of `χ_M` has `‖z‖ < β`, from `Psc.PerronExistence.norm_le_of_pos_left_eigen` and the
  Wielandt equality case `Psc.CocycleSpectrum.primitive_extremal` with `S = N = M`; the sign
  `-1` is excluded because `Mᵏ` and `Mᵏ⁺¹` have positive diagonals and one exponent is odd).
* **(e) Cyclicity for every alphabet size** (audit step 4, P1.4): **`krylov_span_eq_top`**
  (rational `M` with irreducible `χ_M`, `w ≠ 0`: `span_ℚ {Mⁿ w} = ℚ^α`; the span is invariant,
  `χ(M|_U) ∣ χ_M` by `Psc.SectorBridge.charpoly_restrict_dvd`, monic of degree `dim U ≥ 1`,
  hence `χ_M`; this generalizes `Psc.Cyclicity.invariant_eq_bot_or_top` beyond `3 × 3`);
  **`dotProduct_ne_zero_of_left_eigen`** (over any field `K ⊇ ℚ`, every nonzero left
  eigenvector `q` has `q · w ≠ 0`).
* **(f) Spectral exclusion** (audit step 5): `norm_le_one_of_bounded` (`‖zⁿ c‖ ≤ C` for all
  `n` with `c ≠ 0` forces `‖z‖ ≤ 1`); `orbit_limit_bound` (the limit `m → ∞` at fixed `n`);
  **`eigen_orbit_bound`** (`‖z‖ⁿ ‖q · w‖ ≤ L ‖q‖₁` for every `n`, from (b)–(d) and a
  discrepancy bound `|D| ≤ L`).
* **(g) Cubic boundary** (audit step 6): `aeval_ratCast_ne_zero`; **`norm_ne_one_of_cubic`**
  (a monic irreducible rational cubic has no complex root of modulus `1`: a real one is `±1`;
  a non-real `z` has `z z̄ = 1`, so the third root is `-f(0) ∈ ℚ`).  Integrality is not used.
* **The abstract B′ core**: **`bprime_core_of_discrepancy`** (prefix property of `σⁿ(W)`
  for every `n`, `W ≠ []`, `Mᵏ > 0` with `k ≥ 1`, irreducible `χ_M` over `ℚ`, a positive
  left eigenvector for `β`, and `|D u (t n) k a| ≤ L` at every level: every complex root
  `z ≠ β` of `χ_M` has `‖z‖ ≤ 1`); **`bprime_core`** (the same with the cut input
  `∀ n, CutGaps u (t n) L` of audit step 1, through `cut_bound`); `bprime_core_of_blocks`
  (aligned blocks of length `≤ L`); `bprime_core_perron_of_discrepancy`,
  `bprime_core_perron` (the Perron data supplied by `Psc.PerronExistence.perron_inc`);
  **`bprime_core_cubic_of_discrepancy`**, **`bprime_core_cubic`**,
  `bprime_core_cubic_perron` (`natDegree χ_M = 3`: `1 < β` and every complex root `z ≠ β`
  has `‖z‖ < 1`).
* **Controls**: `irreducibility_needed` (negative: `M = [[3,1],[1,3]] > 0`, `w = (1,1)`,
  `q = (1,-1)` with `q M = 2 q` and `q · w = 0`; `χ_M` is reducible, so (e) cannot drop
  irreducibility); `degree_three_needed` (negative: `X² + 1` is monic irreducible with the
  root `i` on the unit circle, so (g) needs degree three among arbitrary monic irreducible
  rational polynomials; `X² + 1` is not the `χ_M` of a primitive substitution, so this is no
  control of B′ itself); the audit specimen
  `zetaSubst = (0 ↦ 01, 1 ↦ 2, 2 ↦ 00)`: `zeta_inc`, `zeta_primitive` (`M⁴ > 0`, `M³` not),
  `zeta_charpoly` (`X³ - X² - 2`), `irreducible_cubic` (the rational root test for a monic
  integer cubic, a finite check by `decide`), `zeta_irreducible`, `zeta_root_outside` (the
  Perron root is `< 2`, so a non-Perron root has modulus `> 1`), `zeta_fixed_point` (the prefix
  hypothesis is satisfiable), **`zeta_unbounded_discrepancy`** (for every `u` with the
  prefix property, every `W ≠ []` and every `L`, `|D u (t n) k a| ≤ L` fails somewhere) and
  **`zeta_no_uniform_cuts`** (so does the cut hypothesis of `bprime_core`); and the positive
  control `one_letter_consistent` (`0 ↦ 00`, `u = 0^∞`, `W = 0`, `L = 0`, `β = 2`: the whole
  hypothesis set of `bprime_core` holds at once).

## Hypotheses and their roles

* prefix property `∀ n, IsPrefixOf (σⁿ W) u`: identifies `P u (t n)` with `Mⁿ w` at the two
  levels `n`, `m` of (c).  This is the first use of the fixed point in the audit's inventory;
  the second (the substituted reductions are shifts of the same `u`) lives inside the cut
  hypothesis and is not formalized here;
* `W ≠ []`: `w ≠ 0`, used by cyclicity (e) and growth (d);
* primitivity `∃ k ≥ 1, Mᵏ > 0`: strict dominance `‖z‖ < β` (d), and the Perron data of
  `bprime_core_perron`;
* irreducibility of `χ_M` over `ℚ`: `q · w ≠ 0` (e); `eigen_orbit_bound` does not use it;
* the discrepancy bound `∀ n k a, |D u (t n) k a| ≤ L`, which is all the proof uses, or the
  stronger cut hypothesis `∀ n, CutGaps u (t n) L`: the only place where termination of
  `bpa-W` enters; `L` is uniform in `n`.

Deviation from the audit (it makes the argument weaker in hypotheses): step 3 is replaced by
the window-sum exchange `window_sum_swap`; letter frequencies are never constructed, and the
vanishing `q(f) = 0` of step 5 is replaced by strict dominance `‖z‖ < β` and growth.

Interface with the sibling module `PscVerif/BPrimeBinding.lean` (audit step 1), which is
not imported here: its `prefixParikh`, `gapD`, `BoundedGaps`, `tn` and the per-index form of
`PrefixOf` have the bodies of `P`, `D`, `CutGaps`, `len` and `IsPrefixOf`, so its
termination output `∀ n, BoundedGaps u (tn s W n) L` is the hypothesis `hgap` of
`bprime_core` by unfolding, and its `prefixOf_iterate` (for a fixed point `u` in its sense
`IsFixed` with prefix `W`) is the hypothesis `hpre`.  The composed statement is not stated
in this module: it is `Psc.BPrime.bprime` (`PscVerif/BPrime.lean`, which imports both).

## Not proved here

* Audit step 1 / acceptance P0.3: that a finite Sirvent–Solomyak `I(W)` (formula (3.1), with
  all children and coincidences) yields the cut hypothesis with `L = max |x|` over its
  states, i.e. the full aligned reduction of `(u, S^{t n} u)`.  The cut hypothesis is assumed
  here; it is `Psc.BPrimeBinding.boundedGaps_of_finite_primitive`, stated in the form
  consumed here as `Psc.BPrime.cutGaps_of_finite`.
* The passage from "`u` is a one-sided fixed point and `W` a nonempty prefix" to the
  prefix hypothesis `∀ n, IsPrefixOf (σⁿ W) u`: this module assumes the latter (the sibling
  module's `prefixOf_iterate` proves it for its `IsFixed`; `Psc.BPrime.isPrefixOf_iterate`
  states it in the form `hpre`).  Nor is it proved that such a
  fixed point exists in general, or the passage from periodic points to a fixing power
  (only the limit of a chain `W <+: σ W` is handled, by `isPrefixOf_limit`).
* That `β` is a Pisot number in the full sense: the cubic theorems conclude `1 < β` and the
  strict disc bound; that `χ_M` (monic, integer, irreducible over `ℚ`) is the minimal
  polynomial of `β` is not restated here (it is `Psc.BPrime.minpoly_eq_charpoly`, and
  `Psc.BPrime.bprime_cubic_isPisot` concludes `IsPisot β`).
* Corollary B (ii), (iii) (they rest on R3 and R2), the pure-discrete-spectrum half of
  Sirvent–Solomyak Remark 2, novelty or priority, and any statement about C4, A1′, BH or PSC.
* Strict exclusion of the unit circle outside degree three: only `‖z‖ ≤ 1` is proved in
  degree two (where the strict bound follows by hand, the conjugate being real and
  irrational) and in degree `≥ 4` (the Salem case); `degree_three_needed` records that the
  abstract lemma (g) uses the degree.
-/
import PscVerif.Incidence
import PscVerif.ParikhIntertwiner
import PscVerif.FixedPointLimit
import PscVerif.PerronExistence
import PscVerif.CocycleSpectrum
import PscVerif.SectorBridge
import PscVerif.GaloisOrbit
import PscVerif.Degree4Floor

namespace Psc.BPrimeCore

open Matrix Finset Polynomial Psc.Binomial Psc.Incidence

variable {α : Type*} [DecidableEq α]

/-! ### (a) Prefix Parikh vectors, the discrepancy `D`, and the cut bound -/

/-- The prefix Parikh vector of an infinite word: `P u k a = |u[0,k)|_a`. -/
def P (u : ℕ → α) (k : ℕ) (a : α) : ℤ := ∑ i ∈ range k, if u i = a then 1 else 0

/-- The discrepancy between the prefixes of length `k` of `u` and of its shift by
`t`: `D u t k = P k - (P (t + k) - P t)`. -/
def D (u : ℕ → α) (t k : ℕ) (a : α) : ℤ := P u k a - (P u (t + k) a - P u t a)

@[simp] theorem P_zero (u : ℕ → α) (a : α) : P u 0 a = 0 := by simp [P]

theorem P_succ (u : ℕ → α) (k : ℕ) (a : α) :
    P u (k + 1) a = P u k a + if u k = a then 1 else 0 := by
  unfold P; rw [sum_range_succ]

theorem P_add (u : ℕ → α) (k j : ℕ) (a : α) :
    P u (k + j) a = P u k a + ∑ i ∈ range j, if u (k + i) = a then 1 else 0 := by
  unfold P; rw [sum_range_add]

theorem indicator_nonneg (p : Prop) [Decidable p] : (0 : ℤ) ≤ if p then 1 else 0 := by
  split_ifs <;> norm_num

theorem indicator_le_one (p : Prop) [Decidable p] : (if p then 1 else 0 : ℤ) ≤ 1 := by
  split_ifs <;> norm_num

theorem sum_indicator_bounds (f : ℕ → Prop) [DecidablePred f] (j : ℕ) :
    0 ≤ (∑ i ∈ range j, if f i then (1 : ℤ) else 0) ∧
      (∑ i ∈ range j, if f i then (1 : ℤ) else 0) ≤ j := by
  refine ⟨sum_nonneg fun i _ => indicator_nonneg _, ?_⟩
  calc (∑ i ∈ range j, if f i then (1 : ℤ) else 0) ≤ ∑ _i ∈ range j, (1 : ℤ) :=
        sum_le_sum fun i _ => indicator_le_one _
    _ = j := by simp

/-- `0 ≤ P u (k + j) a - P u k a ≤ j`: a factor of length `j` contains between `0`
and `j` letters `a`. -/
theorem P_add_sub_bounds (u : ℕ → α) (k j : ℕ) (a : α) :
    0 ≤ P u (k + j) a - P u k a ∧ P u (k + j) a - P u k a ≤ j := by
  rw [P_add, add_sub_cancel_left]
  exact sum_indicator_bounds (fun i => u (k + i) = a) j

theorem P_bounds (u : ℕ → α) (k : ℕ) (a : α) : 0 ≤ P u k a ∧ P u k a ≤ k := by
  simpa using P_add_sub_bounds u 0 k a

/-- The coordinates of a prefix Parikh vector add up to the prefix length. -/
theorem sum_P [Fintype α] (u : ℕ → α) (k : ℕ) : ∑ a, P u k a = k := by
  unfold P
  rw [sum_comm]
  simp

/-- **The shift/factor identity** (`proof/bpa/BpaPrefixBridge.lean`,
`PscVerif.BpaPrefixBridge.shift_factor_identity`, restated here so that the
library carries it; audit step 2).  For any prefix count with values in an abelian
group, the discrepancy between the prefixes of the two tracks equals the
discrepancy between two factors of length `t`. -/
theorem shift_factor_identity {V : Type*} [AddCommGroup V] (Q : ℕ → V) (t k : ℕ) :
    Q k - (Q (t + k) - Q t) = Q t - (Q (k + t) - Q k) := by
  rw [Nat.add_comm t k]
  abel

/-- `D u t k = P t - (P (k + t) - P k)`: the factor form of the discrepancy. -/
theorem D_eq_factor (u : ℕ → α) (t k : ℕ) (a : α) :
    D u t k a = P u t a - (P u (k + t) a - P u k a) :=
  shift_factor_identity (fun k => P u k a) t k

@[simp] theorem D_zero (u : ℕ → α) (t : ℕ) (a : α) : D u t 0 a = 0 := by simp [D]

/-- One step changes `D` by `[u k = a] - [u (t + k) = a]`. -/
theorem D_succ (u : ℕ → α) (t k : ℕ) (a : α) :
    D u t (k + 1) a =
      D u t k a + ((if u k = a then 1 else 0) - if u (t + k) = a then 1 else 0) := by
  simp only [D, ← Nat.add_assoc, P_succ]
  ring

/-- Extension of `D` across a pair of aligned factors of length `l`: a balanced block
(equal Parikh vectors of `u[j, j + l)` and `u[t + j, t + j + l)`) carries a cut at
`j` to a cut at `j + l`. -/
theorem D_add (u : ℕ → α) (t j l : ℕ) (a : α) :
    D u t (j + l) a = D u t j a + ((P u (j + l) a - P u j a) -
      (P u (t + j + l) a - P u (t + j) a)) := by
  simp only [D, Nat.add_assoc]
  ring

/-- **Lipschitz bound**: each coordinate of `D` moves by at most one per letter. -/
theorem abs_D_sub_le (u : ℕ → α) (t : ℕ) (a : α) {k k' : ℕ} (h : k ≤ k') :
    |D u t k' a - D u t k a| ≤ k' - k := by
  induction k', h using Nat.le_induction with
  | base => simp
  | succ k' hk ih =>
    rw [D_succ]
    have h1 := indicator_nonneg (u k' = a)
    have h2 := indicator_le_one (u k' = a)
    have h3 := indicator_nonneg (u (t + k') = a)
    have h4 := indicator_le_one (u (t + k') = a)
    rw [abs_le] at ih ⊢
    push_cast
    constructor <;> linarith [ih.1, ih.2]

/-- **The cut-gap hypothesis** at shift `t`: from every position `k`, a common cut of
`(u, Sᵗ u)` (a zero of every coordinate of `D u t`) is reached within `L` letters.  This
is the output of audit step 1 that `bprime_core` consumes; the sibling module
`PscVerif/BPrimeBinding.lean` (not imported here) states the same body as
`BoundedGaps u t L`.  `D u t 0 = 0` is the theorem `D_zero`, not a conjunct. -/
def CutGaps (u : ℕ → α) (t L : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' ≤ k + L ∧ ∀ a, D u t k' a = 0

/-- **The cut bound** (audit step 2; acceptance matrix P0 item 2).  If from every
position `k` a common cut (`D = 0`) is reached within `L` letters, then every
coordinate of `D` is bounded by `L`, at every position. -/
theorem cut_bound (u : ℕ → α) (t L : ℕ) (hgap : CutGaps u t L) (k : ℕ) (a : α) :
    |D u t k a| ≤ L := by
  obtain ⟨k', hk, hk', h0⟩ := hgap k
  have := abs_D_sub_le u t a hk
  rw [h0 a, zero_sub, abs_neg] at this
  exact this.trans (by omega)

/-- **The block bound**: between two cuts `j ≤ k ≤ j'`, `|D k| ≤ min (k - j) (j' - k)`,
so `2 |D k| ≤ j' - j`.  The bound vanishes at both ends of the block. -/
theorem block_bound (u : ℕ → α) (t : ℕ) (a : α) {j j' k : ℕ} (hj : D u t j a = 0)
    (hj' : D u t j' a = 0) (hjk : j ≤ k) (hkj : k ≤ j') :
    |D u t k a| ≤ k - j ∧ |D u t k a| ≤ j' - k ∧ 2 * |D u t k a| ≤ j' - j := by
  have h1 := abs_D_sub_le u t a hjk
  have h2 := abs_D_sub_le u t a hkj
  rw [hj, sub_zero] at h1
  rw [hj', zero_sub, abs_neg] at h2
  exact ⟨h1, h2, by linarith⟩

/-- **Cuts from a block decomposition, with the off-by-one at each block end.**  If
`c 0 = 0 < c 1 < ⋯` are common cuts and consecutive cuts are at most `L` apart
(aligned blocks of length `≤ L`), then from every `k` a cut is reached within
`L - 1` letters: `k ≤ k' < k + L`. -/
theorem exists_cut_of_blocks (u : ℕ → α) (t L : ℕ) (c : ℕ → ℕ) (hc : StrictMono c)
    (hc0 : c 0 = 0) (hcL : ∀ i, c (i + 1) ≤ c i + L) (hcut : ∀ i a, D u t (c i) a = 0)
    (k : ℕ) : ∃ k', k ≤ k' ∧ k' < k + L ∧ ∀ a, D u t k' a = 0 := by
  have hL : 1 ≤ L := by
    have h1 : c 0 < c 1 := hc zero_lt_one
    have h2 : c 1 ≤ c 0 + L := hcL 0
    omega
  have hex : ∃ i, k < c i := ⟨k + 1, lt_of_lt_of_le (Nat.lt_succ_self k) (hc.id_le _)⟩
  set i₀ := Nat.find hex with hi₀
  have hk : k < c i₀ := Nat.find_spec hex
  have hi0 : i₀ ≠ 0 := by intro h; rw [h, hc0] at hk; omega
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hle : c i ≤ k := not_lt.1 (Nat.find_min hex (by omega : i < i₀))
  rw [hi] at hk
  by_cases he : c i = k
  · exact ⟨c i, he.ge, by omega, hcut i⟩
  · exact ⟨c (i + 1), hk.le, by have := hcL i; omega, hcut (i + 1)⟩

/-- **The cut bound for aligned blocks of length `≤ L`**: `|D| < L` (strict, because
`D` vanishes at the end of each block). -/
theorem cut_bound_of_blocks (u : ℕ → α) (t L : ℕ) (c : ℕ → ℕ) (hc : StrictMono c)
    (hc0 : c 0 = 0) (hcL : ∀ i, c (i + 1) ≤ c i + L) (hcut : ∀ i a, D u t (c i) a = 0)
    (k : ℕ) (a : α) : |D u t k a| < L := by
  obtain ⟨k', hk, hk', h0⟩ := exists_cut_of_blocks u t L c hc hc0 hcL hcut k
  have := abs_D_sub_le u t a hk
  rw [h0 a, zero_sub, abs_neg] at this
  exact this.trans_lt (by omega)

/-- Aligned blocks of length `≤ L` give the cut-gap hypothesis `CutGaps u t L` (with one
letter to spare, `exists_cut_of_blocks`). -/
theorem cutGaps_of_blocks (u : ℕ → α) (t L : ℕ) (c : ℕ → ℕ) (hc : StrictMono c)
    (hc0 : c 0 = 0) (hcL : ∀ i, c (i + 1) ≤ c i + L) (hcut : ∀ i a, D u t (c i) a = 0) :
    CutGaps u t L := fun k => by
  obtain ⟨k', h1, h2, h3⟩ := exists_cut_of_blocks u t L c hc hc0 hcL hcut k
  exact ⟨k', h1, h2.le, h3⟩

/-! ### (b) Fixed-point lengths -/

/-- A finite word `x` is a prefix of the infinite word `u`. -/
def IsPrefixOf (x : List α) (u : ℕ → α) : Prop := ∀ i (h : i < x.length), x[i] = u i

theorem count_map_range (u : ℕ → α) (k : ℕ) (a : α) :
    (((List.range k).map u).count a : ℤ) = P u k a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.count_append, P_succ, ← ih]
    simp [List.count_singleton]

/-- The prefix Parikh vector at the length of a prefix is the Parikh vector of
that prefix. -/
theorem P_length_of_prefix {x : List α} {u : ℕ → α} (h : IsPrefixOf x u) (a : α) :
    P u x.length a = x.count a := by
  have hx : x = (List.range x.length).map u :=
    List.ext_getElem (by simp) fun i h₁ _ => by simp [h i h₁]
  conv_rhs => rw [hx]
  rw [count_map_range]

/-- The length `t n = |σⁿ(W)|`. -/
def len (s : α → List α) (W : List α) (n : ℕ) : ℕ := ((subst s)^[n] W).length

/-- `p(σⁿ W) = Mⁿ p(W)`: the `n`-th iterate of the Parikh intertwining
`Psc.ParikhIntertwiner.parikh_subst` (`p(σ W) = M p(W)`). -/
theorem parikh_iterate [Fintype α] (s : α → List α) (n : ℕ) (W : List α) :
    Psc.ParikhIntertwiner.parikh ((subst s)^[n] W) =
      inc s ^ n *ᵥ Psc.ParikhIntertwiner.parikh W := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Psc.ParikhIntertwiner.parikh_subst, ih, mulVec_mulVec,
      ← pow_succ']

/-- The Parikh vector `w = p(W)` (`Psc.ParikhIntertwiner.parikh`), cast to any `NatCast`
type. -/
def parikhCast {K : Type*} [NatCast K] (W : List α) : α → K :=
  fun c => (Psc.ParikhIntertwiner.parikh W c : K)

/-- `parikh_iterate` cast to any commutative semiring, coordinatewise:
`|σⁿ W|_a = (Mⁿ w)_a` with `M = inc s` and `w = p(W)`. -/
theorem count_iterate_cast [Fintype α] {K : Type*} [CommSemiring K] (s : α → List α)
    (n : ℕ) (W : List α) (a : α) :
    (((subst s)^[n] W).count a : K) =
      ((inc s).map (Nat.cast : ℕ → K) ^ n *ᵥ parikhCast W) a := by
  rw [show ((subst s)^[n] W).count a = Psc.ParikhIntertwiner.parikh ((subst s)^[n] W) a from rfl,
    parikh_iterate, show (inc s).map (Nat.cast : ℕ → K) =
    (inc s).map (Nat.castRingHom K) from rfl, ← Matrix.map_pow]
  simp [mulVec, dotProduct, parikhCast]

/-- **(b) Fixed-point lengths.**  If `σⁿ(W)` is a prefix of `u`, then
`P u |σⁿ W| = Mⁿ w` (over `ℤ`). -/
theorem P_iterate [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α} {n : ℕ}
    (h : IsPrefixOf ((subst s)^[n] W) u) (a : α) :
    P u ((subst s)^[n] W).length a =
      ((inc s).map (Nat.cast : ℕ → ℤ) ^ n *ᵥ parikhCast W) a := by
  rw [P_length_of_prefix h, count_iterate_cast]

/-- The letter counts of a word add up to its length (`Multiset.sum_count_eq_card`). -/
theorem sum_count_eq_length [Fintype α] (x : List α) : ∑ a, x.count a = x.length := by
  simpa using Multiset.sum_count_eq_card (s := univ) (m := (x : Multiset α))
    fun a _ => mem_univ a

/-- The length of `σⁿ(W)` is the coordinate sum of `Mⁿ w`. -/
theorem length_iterate_cast [Fintype α] {K : Type*} [CommSemiring K] (s : α → List α)
    (n : ℕ) (W : List α) :
    (((subst s)^[n] W).length : K) =
      ∑ a, ((inc s).map (Nat.cast : ℕ → K) ^ n *ᵥ parikhCast W) a := by
  simp_rw [← count_iterate_cast]
  rw [← Nat.cast_sum, sum_count_eq_length]

/-- The limit word of `Psc.FixedPointLimit` (with `p = 1`) has every `σⁿ(W)` as a
prefix: the hypothesis of `P_iterate` holds for it. -/
theorem isPrefixOf_limit (s : α → List α) {W : List α} (hW : W <+: subst s W)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[1 * n] W).length) (n : ℕ) :
    IsPrefixOf ((subst s)^[n] W) (Psc.FixedPointLimit.limit s W 1 hgrow) := by
  intro i h
  have hW' : W <+: (subst s)^[1] W := by simpa using hW
  have h' : i < ((subst s)^[1 * n] W).length := by rwa [one_mul]
  rw [Psc.FixedPointLimit.limit_spec s hW' hgrow n i h']
  simp [List.get_eq_getElem, one_mul]

/-! ### (c) Averaging without frequencies -/

/-- Exchange of the two window sums: for any prefix count `Q`,
`Σ_{k<K} (Q (k+t) - Q k) = Σ_{j<t} (Q (K+j) - Q j)` (both are the sum of the
increments `Q (k+j+1) - Q (k+j)` over `k < K`, `j < t`). -/
theorem window_sum_swap {V : Type*} [AddCommGroup V] (Q : ℕ → V) (K t : ℕ) :
    ∑ k ∈ range K, (Q (k + t) - Q k) = ∑ j ∈ range t, (Q (K + j) - Q j) := by
  have h1 : ∀ k, Q (k + t) - Q k = ∑ j ∈ range t, (Q (k + (j + 1)) - Q (k + j)) := fun k => by
    have := Finset.sum_range_sub (fun j => Q (k + j)) t
    simp only [add_zero] at this
    exact this.symm
  have h2 : ∀ j, Q (K + j) - Q j = ∑ k ∈ range K, (Q (k + 1 + j) - Q (k + j)) := fun j => by
    have := Finset.sum_range_sub (fun k => Q (k + j)) K
    simp only [zero_add] at this
    exact this.symm
  rw [sum_congr rfl fun k _ => h1 k, sum_comm, sum_congr rfl fun j _ => h2 j]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [show k + 1 + j = k + (j + 1) by omega]

/-- **Averaging without frequencies** (replaces audit step 3).  If every coordinate
of `D u t ·` is bounded by `L`, then for every `K`,
`|K · P t - t · P K| ≤ K L + t²` coordinatewise.  Sum the factor form of `D` over
`k < K`, exchange the window sums (`window_sum_swap`), and compare each
`P (K + j) - P j` with `P K` (an error of at most `j < t`). -/
theorem avg_bound (u : ℕ → α) (t K L : ℕ) (a : α) (hD : ∀ k, |D u t k a| ≤ L) :
    |(K : ℤ) * P u t a - t * P u K a| ≤ K * L + t * t := by
  have hsumD : ∑ k ∈ range K, D u t k a =
      K * P u t a - ∑ j ∈ range t, (P u (K + j) a - P u j a) := by
    rw [← window_sum_swap (fun k => P u k a) K t]
    simp only [D_eq_factor]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hE : ∑ j ∈ range t, (P u (K + j) a - P u j a) =
      t * P u K a + ∑ j ∈ range t, (P u (K + j) a - P u K a - P u j a) := by
    have e : ∀ j, P u (K + j) a - P u j a = P u K a + (P u (K + j) a - P u K a - P u j a) :=
      fun j => by ring
    rw [sum_congr rfl fun j _ => e j, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hEb : ∀ j ∈ range t, |P u (K + j) a - P u K a - P u j a| ≤ t := by
    intro j hj
    have hjt : (j : ℤ) ≤ t := by have := mem_range.1 hj; omega
    have h1 := P_add_sub_bounds u K j a
    have h2 := P_bounds u j a
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have key : (K : ℤ) * P u t a - t * P u K a =
      ∑ k ∈ range K, D u t k a + ∑ j ∈ range t, (P u (K + j) a - P u K a - P u j a) := by
    rw [hsumD, hE]; ring
  rw [key]
  calc _ ≤ |∑ k ∈ range K, D u t k a| + |∑ j ∈ range t, (P u (K + j) a - P u K a - P u j a)| :=
        abs_add_le _ _
    _ ≤ ∑ k ∈ range K, |D u t k a| + ∑ j ∈ range t, |P u (K + j) a - P u K a - P u j a| :=
        add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k ∈ range K, (L : ℤ) + ∑ _j ∈ range t, (t : ℤ) :=
        add_le_add (sum_le_sum fun k _ => hD k) (sum_le_sum hEb)
    _ = K * L + t * t := by simp


/-- Powers of a left eigenvector: `q ᵥ* Aⁿ = zⁿ • q` (any commutative ring; the real
case is `Psc.PerronExistence.vecMul_pow_of_left_eigen`). -/
theorem vecMul_pow_eigen [Fintype α] {R : Type*} [CommRing R] (A : Matrix α α R) (q : α → R)
    (z : R) (hq : q ᵥ* A = z • q) (n : ℕ) : q ᵥ* A ^ n = z ^ n • q := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← vecMul_vecMul, hq, smul_vecMul, ih, smul_smul, pow_succ']

/-- `P u (t n) = Mⁿ w` cast to any commutative ring. -/
theorem P_iterate_cast [Fintype α] {R : Type*} [CommRing R] (s : α → List α) {u : ℕ → α}
    {W : List α} {n : ℕ} (h : IsPrefixOf ((subst s)^[n] W) u) (a : α) :
    (P u (len s W n) a : R) = ((inc s).map (Nat.cast : ℕ → R) ^ n *ᵥ parikhCast W) a := by
  rw [len, P_length_of_prefix h, Int.cast_natCast]
  exact count_iterate_cast s n W a

/-- **(c) The eigenvalue form of the averaging bound.**  Let `σⁿ(W)` be a prefix of `u`
for every `n`, and let `D u (t n) ·` be bounded by `L` at every level `t n = |σⁿ W|`.
For a complex left eigenvector `q ᵥ* M = z • q`, with `K = t m`:
`‖t m zⁿ q(w) - t n zᵐ q(w)‖ ≤ (t m L + (t n)²) ‖q‖₁`. -/
theorem eigen_window_bound [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α}
    (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u) {L : ℕ}
    (hD : ∀ n k a, |D u (len s W n) k a| ≤ L) {q : α → ℂ} {z : ℂ}
    (hq : q ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = z • q) (n m : ℕ) :
    ‖(len s W m : ℂ) * z ^ n * (q ⬝ᵥ parikhCast W) -
        (len s W n : ℂ) * z ^ m * (q ⬝ᵥ parikhCast W)‖ ≤
      ((len s W m : ℝ) * L + (len s W n : ℝ) ^ 2) * ∑ a, ‖q a‖ := by
  set t := len s W n
  set K := len s W m
  set Mc := (inc s).map (Nat.cast : ℕ → ℂ)
  set v : α → ℤ := fun a => (K : ℤ) * P u t a - t * P u K a with hv
  have hvb : ∀ a, |v a| ≤ K * L + t * t := fun a => avg_bound u t K L a fun k => hD n k a
  have hdot : ∀ j, q ⬝ᵥ (Mc ^ j *ᵥ parikhCast W) = z ^ j * (q ⬝ᵥ parikhCast W) := fun j => by
    rw [dotProduct_mulVec, vecMul_pow_eigen _ _ _ hq, smul_dotProduct, smul_eq_mul]
  have hvc : (fun a => ((v a : ℤ) : ℂ)) = (K : ℂ) • (Mc ^ n *ᵥ parikhCast W) -
      (t : ℂ) • (Mc ^ m *ᵥ parikhCast W) := by
    funext a
    simp only [hv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [P_iterate_cast s (hpre n), P_iterate_cast s (hpre m)]
  have hlhs : (K : ℂ) * z ^ n * (q ⬝ᵥ parikhCast W) - (t : ℂ) * z ^ m * (q ⬝ᵥ parikhCast W) =
      q ⬝ᵥ fun a => ((v a : ℤ) : ℂ) := by
    rw [hvc, dotProduct_sub, dotProduct_smul, dotProduct_smul, hdot, hdot, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [hlhs]
  calc ‖q ⬝ᵥ fun a => ((v a : ℤ) : ℂ)‖ ≤ ∑ a, ‖q a‖ * ‖((v a : ℤ) : ℂ)‖ := by
        simp only [dotProduct]
        exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun a _ => norm_mul _ _))
    _ ≤ ∑ a, ‖q a‖ * ((K : ℝ) * L + (t : ℝ) ^ 2) := by
        refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Complex.norm_intCast]
        have := hvb a
        have h' : ((|v a| : ℤ) : ℝ) ≤ ((K * L + t * t : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at h'
        nlinarith [h']
    _ = ((K : ℝ) * L + (t : ℝ) ^ 2) * ∑ a, ‖q a‖ := by rw [← sum_mul]; ring

/-! ### (d) Growth and strict dominance -/

/-- **Growth of `t m`.**  If `ℓ > 0` is a left eigenvector of `M` for `β` and `W ≠ []`,
then `t m ≥ c βᵐ` with `c = ℓ · w / Σ ℓ > 0`: `ℓ · Mᵐ w = βᵐ ℓ · w` and `ℓ · v ≤ (Σ ℓ) Σ v`
for `v = Mᵐ w ≥ 0`, whose coordinate sum is `t m`. -/
theorem len_growth [Fintype α] (s : α → List α) {W : List α} (hW : W ≠ []) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ∃ c : ℝ, 0 < c ∧ ∀ m, c * β ^ m ≤ len s W m := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil W hW
  have hw0 : ∀ a, 0 ≤ (parikhCast W : α → ℝ) a := fun a => Nat.cast_nonneg _
  have hwne : (parikhCast W : α → ℝ) ≠ 0 := fun h => by
    have := congrFun h x
    simp only [parikhCast, Psc.ParikhIntertwiner.parikh, Pi.zero_apply, Nat.cast_eq_zero,
      List.count_eq_zero] at this
    exact this hx
  have hdot : 0 < ℓ ⬝ᵥ parikhCast W := Psc.PerronExistence.dotProduct_pos_of_nonneg hℓ hw0 hwne
  have hΛ : 0 < ∑ a, ℓ a := Finset.sum_pos (fun a _ => hℓ a) ⟨x, mem_univ x⟩
  refine ⟨(ℓ ⬝ᵥ parikhCast W) / ∑ a, ℓ a, div_pos hdot hΛ, fun m => ?_⟩
  have hv0 : ∀ a, 0 ≤ ((inc s).map (Nat.cast : ℕ → ℝ) ^ m *ᵥ parikhCast W) a := fun a => by
    rw [← count_iterate_cast]; exact Nat.cast_nonneg _
  have h1 : ℓ ⬝ᵥ ((inc s).map (Nat.cast : ℕ → ℝ) ^ m *ᵥ parikhCast W) =
      β ^ m * (ℓ ⬝ᵥ parikhCast W) := by
    rw [dotProduct_mulVec, vecMul_pow_eigen _ _ _ hℓM, smul_dotProduct, smul_eq_mul]
  have h2 : ℓ ⬝ᵥ ((inc s).map (Nat.cast : ℕ → ℝ) ^ m *ᵥ parikhCast W) ≤
      (∑ a, ℓ a) * len s W m := by
    rw [len, length_iterate_cast (K := ℝ), Finset.mul_sum]
    exact sum_le_sum fun a _ => mul_le_mul_of_nonneg_right
      (single_le_sum (fun b _ => (hℓ b).le) (mem_univ a)) (hv0 a)
  rw [div_mul_eq_mul_div, div_le_iff₀ hΛ, mul_comm (ℓ ⬝ᵥ parikhCast W), ← h1, mul_comm]
  exact h2

/-- **The Perron root exceeds one** on at least two letters (no irreducibility used):
`βᵏ ℓ_j = Σ_i ℓ_i (Mᵏ)_{ij} ≥ Σ_i ℓ_i > ℓ_j` since `Mᵏ ≥ 1` entrywise. -/
theorem one_lt_perron [Fintype α] [Nontrivial α] (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) : 1 < β := by
  obtain ⟨k, hk1, hk⟩ := hprim
  set Mr := (inc s).map (Nat.cast : ℕ → ℝ)
  obtain ⟨j⟩ := (inferInstance : Nonempty α)
  obtain ⟨i', hi'⟩ := exists_ne j
  have hβ0 : 0 ≤ β := by
    have h := congrFun hℓM j
    simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    have : 0 ≤ β * ℓ j := h ▸ sum_nonneg fun i _ => mul_nonneg (hℓ i).le (Nat.cast_nonneg _)
    exact nonneg_of_mul_nonneg_left this (hℓ j)
  have hpow := congrFun (vecMul_pow_eigen Mr ℓ β hℓM k) j
  have hMk : ∀ a c, (1 : ℝ) ≤ (Mr ^ k) a c := fun a c => by
    rw [show Mr = (inc s).map (Nat.castRingHom ℝ) from rfl, ← Matrix.map_pow, map_apply]
    exact Nat.one_le_cast.2 (hk a c)
  simp only [vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hpow
  have hsum : ∑ i, ℓ i ≤ ∑ i, ℓ i * (Mr ^ k) i j :=
    sum_le_sum fun i _ => le_mul_of_one_le_right (hℓ i).le (hMk i j)
  have hgt : ℓ j < ∑ i, ℓ i := by
    rw [← Finset.add_sum_erase _ _ (mem_univ j)]
    have : 0 < ∑ i ∈ univ.erase j, ℓ i :=
      Finset.sum_pos (fun i _ => hℓ i) ⟨i', mem_erase.2 ⟨hi', mem_univ _⟩⟩
    linarith
  by_contra hβ
  push Not at hβ
  have : β ^ k ≤ 1 := pow_le_one₀ hβ0 hβ
  nlinarith [hℓ j]

/-- **Strict dominance** for a primitive incidence matrix: every complex root `z ≠ β`
of `χ_M` has `‖z‖ < β`.  `‖z‖ ≤ β` is `Psc.PerronExistence.norm_le_of_pos_left_eigen`;
in the equality case `Psc.CocycleSpectrum.primitive_extremal` (Wielandt, with
`S = N = M`) gives `z = ±β` and `M = ± D M D` with `D` a diagonal sign matrix; the sign
`-1` would make `(Mⁿ)ᵢᵢ = -(Mⁿ)ᵢᵢ` for odd `n`, but `Mᵏ` and `Mᵏ⁺¹` have positive
diagonal. -/
theorem norm_lt_perron [Fintype α] (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) {β : ℝ} {ℓ : α → ℝ}
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) : ‖z‖ < β := by
  obtain ⟨k, hk1, hk⟩ := (Psc.PerronExistence.inc_cast_primitive s hprim).2
  set N := (inc s).map (Nat.cast : ℕ → ℝ)
  have hN : ∀ i j, 0 ≤ N i j := (Psc.PerronExistence.inc_cast_primitive s hprim).1
  have hNC : N.map ((↑) : ℝ → ℂ) = (inc s).map (Nat.cast : ℕ → ℂ) := by ext; simp [N]
  have hle : ‖z‖ ≤ β :=
    Psc.PerronExistence.norm_le_of_pos_left_eigen N hN ℓ hℓ β hℓM z (by rw [hNC]; exact hz)
  refine lt_of_le_of_ne hle fun heq => hzβ ?_
  obtain ⟨x, hx0, hx⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot _ z hz
  have hSC := Psc.CocycleSpectrum.stronglyConnected_of_pow_pos N hN hk1 hk
  obtain ⟨σ, hσ, hzσ, Dg, hDg, hrel⟩ := Psc.CocycleSpectrum.primitive_extremal N hSC ℓ hℓ β hℓM
    N (fun i j => by rw [abs_of_nonneg (hN i j)]) ⟨k, hk⟩ x hx0 z heq (by rw [hNC]; exact hx)
  rcases hσ with rfl | rfl
  · simpa using hzσ
  exfalso
  have hD2 : ∀ i, Dg i * Dg i = 1 := fun i => by rcases hDg i with h | h <;> simp [h]
  have hpow : ∀ n i j, (N ^ n) i j = (-1) ^ n * Dg i * (N ^ n) i j * Dg j := by
    intro n
    induction n with
    | zero =>
      intro i j
      by_cases h : i = j
      · subst h; simp [hD2 i]
      · simp [Matrix.one_apply_ne h]
    | succ n ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h1 := ih i l
      have h2 := hrel l j
      linear_combination ((-1) ^ n * Dg i * (N ^ n) i l * Dg l) * h2 + N l j * h1 +
        ((-1) ^ (n + 1) * Dg i * (N ^ n) i l * N l j * Dg j) * hD2 l
  obtain ⟨i, -⟩ := Function.ne_iff.1 hx0
  have hcol : ∃ l, 0 < N l i := by
    by_contra hc
    push Not at hc
    have h0 : ∀ l, N l i = 0 := fun l => le_antisymm (hc l) (hN l i)
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk1
    have := hk i i
    rw [pow_succ, Matrix.mul_apply] at this
    simp [h0] at this
  obtain ⟨l₀, hl₀⟩ := hcol
  have hk1' : 0 < (N ^ (k + 1)) i i := by
    rw [pow_succ, Matrix.mul_apply]
    exact (mul_pos (hk i l₀) hl₀).trans_le (Finset.single_le_sum
      (f := fun l => (N ^ k) i l * N l i) (fun l _ => mul_nonneg (hk i l).le (hN l i))
      (Finset.mem_univ l₀))
  have hodd : ∃ n, Odd n ∧ 0 < (N ^ n) i i := by
    rcases Nat.even_or_odd k with he | ho
    · exact ⟨k + 1, he.add_one, hk1'⟩
    · exact ⟨k, ho, hk i i⟩
  obtain ⟨n, hn, hpos⟩ := hodd
  have h := hpow n i i
  rw [hn.neg_one_pow] at h
  have : (N ^ n) i i = 0 := by
    linear_combination (1 / 2 : ℝ) * h - (1 / 2 : ℝ) * (N ^ n) i i * hD2 i
  exact hpos.ne' this

/-! ### (e) Cyclicity for a general alphabet -/

/-- **Krylov spanning** (audit step 4; acceptance matrix P1 item 4).  For a rational
matrix with irreducible characteristic polynomial, every nonzero `w` is cyclic:
`span_ℚ {Mⁿ w} = ℚ^α`.  The span `U` is `M`-invariant, so `χ(M|_U) ∣ χ_M`
(`Psc.SectorBridge.charpoly_restrict_dvd`); `χ(M|_U)` is monic of degree `dim U ≥ 1`,
hence equal to `χ_M`, and `dim U = |α|`.  (Generalizes
`Psc.Cyclicity.invariant_eq_bot_or_top` beyond `3 × 3`.) -/
theorem krylov_span_eq_top [Fintype α] (M : Matrix α α ℚ) (hM : Irreducible M.charpoly)
    (w : α → ℚ) (hw : w ≠ 0) :
    Submodule.span ℚ (Set.range fun n : ℕ => (M ^ n) *ᵥ w) = ⊤ := by
  set U := Submodule.span ℚ (Set.range fun n : ℕ => (M ^ n) *ᵥ w)
  have hinv : ∀ v ∈ U, Matrix.toLin' M v ∈ U := by
    have : U ≤ U.comap (Matrix.toLin' M) := by
      rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      show Matrix.toLin' M (M ^ n *ᵥ w) ∈ U
      rw [Matrix.toLin'_apply, mulVec_mulVec, ← pow_succ']
      exact Submodule.subset_span ⟨n + 1, rfl⟩
    exact fun v hv => this hv
  obtain ⟨h, hh⟩ := Psc.SectorBridge.charpoly_restrict_dvd (Matrix.toLin' M) U hinv
  rw [Matrix.charpoly_toLin'] at hh
  set g := ((Matrix.toLin' M).restrict hinv).charpoly
  have hgm : g.Monic := LinearMap.charpoly_monic _
  have hgdeg : g.natDegree = Module.finrank ℚ U := LinearMap.charpoly_natDegree _
  rcases hM.isUnit_or_isUnit hh with hu | hu
  · have h0 : Module.finrank ℚ U = 0 := by rw [← hgdeg, hgm.eq_one_of_isUnit hu, natDegree_one]
    have hwU : w ∈ U := Submodule.subset_span ⟨0, by simp⟩
    rw [Submodule.finrank_eq_zero.1 h0, Submodule.mem_bot] at hwU
    exact absurd hwU hw
  · have hdeg : M.charpoly.natDegree = g.natDegree := by
      rw [hh, natDegree_mul hgm.ne_zero hu.ne_zero, natDegree_eq_zero_of_isUnit hu, add_zero]
    rw [Matrix.charpoly_natDegree_eq_dim, hgdeg] at hdeg
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, hdeg]

/-- **Every nonzero left eigenvector sees `w`.**  Over any field `K ⊇ ℚ`, a nonzero
`q` with `q ᵥ* M = z • q` has `q · w ≠ 0`: otherwise `q · Mⁿ w = zⁿ (q · w) = 0` for all
`n`, so `q` vanishes on the Krylov span, which is everything (`krylov_span_eq_top`). -/
theorem dotProduct_ne_zero_of_left_eigen [Fintype α] {K : Type*} [Field K] [Algebra ℚ K]
    (M : Matrix α α ℚ) (hM : Irreducible M.charpoly) (w : α → ℚ) (hw : w ≠ 0) (q : α → K)
    (hq0 : q ≠ 0) (z : K) (hq : q ᵥ* M.map (algebraMap ℚ K) = z • q) :
    q ⬝ᵥ (fun a => algebraMap ℚ K (w a)) ≠ 0 := by
  intro h0
  let f : (α → ℚ) →ₗ[ℚ] K :=
    { toFun := fun v => q ⬝ᵥ fun a => algebraMap ℚ K (v a)
      map_add' := fun v v' => by
        simp only [Pi.add_apply, map_add]
        rw [← dotProduct_add]; rfl
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, dotProduct,
          Algebra.smul_def, Finset.mul_sum]
        exact sum_congr rfl fun a _ => by ring }
  have hf : ∀ n : ℕ, f (M ^ n *ᵥ w) = 0 := by
    intro n
    show q ⬝ᵥ (fun a => algebraMap ℚ K ((M ^ n *ᵥ w) a)) = 0
    have e : (fun a => algebraMap ℚ K ((M ^ n *ᵥ w) a)) =
        (M.map (algebraMap ℚ K)) ^ n *ᵥ fun a => algebraMap ℚ K (w a) := by
      funext a
      rw [RingHom.map_mulVec, Matrix.map_pow]
      rfl
    rw [e, dotProduct_mulVec, vecMul_pow_eigen _ _ _ hq, smul_dotProduct, h0, smul_zero]
  have hle : Submodule.span ℚ (Set.range fun n : ℕ => M ^ n *ᵥ w) ≤ LinearMap.ker f :=
    Submodule.span_le.2 (by rintro _ ⟨n, rfl⟩; exact hf n)
  rw [krylov_span_eq_top M hM w hw, top_le_iff] at hle
  apply hq0
  funext a
  have h0a : f (Pi.single a 1) = 0 := by rw [← LinearMap.mem_ker, hle]; trivial
  have hfa : f (Pi.single a 1) = q a := by
    show ∑ b, q b * algebraMap ℚ K ((Pi.single a (1 : ℚ) : α → ℚ) b) = q a
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, map_zero, mul_zero])
      (fun h => absurd (mem_univ a) h), Pi.single_eq_same, map_one, mul_one]
  rw [← hfa, h0a]; rfl

/-- The matrix `[[3,1],[1,3]]` of the negative control. -/
def ctrlM : Matrix (Fin 2) (Fin 2) ℚ := !![3, 1; 1, 3]

/-- **Negative control: irreducibility cannot be dropped in (e).**  `M = [[3,1],[1,3]]`
is positive, `w = (1,1) ≠ 0`, and `q = (1,-1) ≠ 0` is a left eigenvector for `2` with
`q · w = 0`; `χ_M = (X - 2)(X - 4)` is reducible (it has the rational root `2`). -/
theorem irreducibility_needed :
    (∀ i j, 0 < ctrlM i j) ∧ ¬ Irreducible ctrlM.charpoly ∧
      (![1, -1] : Fin 2 → ℚ) ᵥ* ctrlM = (2 : ℚ) • ![1, -1] ∧
      (![1, -1] : Fin 2 → ℚ) ⬝ᵥ ![1, 1] = 0 ∧ (![1, 1] : Fin 2 → ℚ) ≠ 0 ∧
      (![1, -1] : Fin 2 → ℚ) ≠ 0 := by
  have heig : (![1, -1] : Fin 2 → ℚ) ᵥ* ctrlM = (2 : ℚ) • ![1, -1] := by
    ext i; fin_cases i <;> simp [ctrlM, vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num
  have hne : (![1, -1] : Fin 2 → ℚ) ≠ 0 := fun h => by
    have := congrFun h 0; simp at this
  refine ⟨fun i j => by fin_cases i <;> fin_cases j <;> simp [ctrlM], fun hirr => ?_, heig,
    by simp [dotProduct, Fin.sum_univ_two], fun h => by have := congrFun h 0; simp at this, hne⟩
  have hroot := Psc.ConcentrationAlgebra.isRoot_of_left_eigen ctrlM 2 _ hne heig
  have h1 := degree_eq_one_of_irreducible_of_root hirr hroot
  have h2 : ctrlM.charpoly.degree = 2 := by
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]; rfl
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ### (f) Spectral exclusion -/

/-- **Bounded orbit forces the closed disc** (audit step 5): if `‖zⁿ c‖ ≤ C` for all `n`
and `c ≠ 0`, then `‖z‖ ≤ 1`. -/
theorem norm_le_one_of_bounded {z c : ℂ} (hc : c ≠ 0) {C : ℝ}
    (h : ∀ n : ℕ, ‖z ^ n * c‖ ≤ C) : ‖z‖ ≤ 1 := by
  by_contra h1
  push Not at h1
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / ‖c‖) h1
  rw [div_lt_iff₀ hc'] at hn
  have := h n
  rw [norm_mul, norm_pow] at this
  linarith

/-- **The limit `m → ∞` at fixed `n`** (audit step 5, without frequencies).  From the
two-level bound `‖t m zⁿ c - t n zᵐ c‖ ≤ (t m L + (t n)²) S`, growth `t m ≥ C₀ βᵐ` with
`β > 1`, and `‖z‖ < β`: divide by `t m` and let `m → ∞`; the error terms are
`O(β⁻ᵐ)` and `O((‖z‖/β)ᵐ)`. -/
theorem orbit_limit_bound (t : ℕ → ℕ) {z c : ℂ} {β C₀ L S : ℝ} (hβ : 1 < β) (hC₀ : 0 < C₀)
    (ht : ∀ m, C₀ * β ^ m ≤ t m) (hz : ‖z‖ < β) (hS : 0 ≤ S)
    (hb : ∀ n m, ‖(t m : ℂ) * z ^ n * c - (t n : ℂ) * z ^ m * c‖ ≤
      ((t m : ℝ) * L + (t n : ℝ) ^ 2) * S) (n : ℕ) :
    ‖z‖ ^ n * ‖c‖ ≤ L * S := by
  set X := ‖z‖ ^ n * ‖c‖
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  set A := (t n : ℝ) ^ 2 * S
  set B := (t n : ℝ) * ‖c‖
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) hS
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hstep : ∀ m, X ≤ L * S + (A / C₀ * (1 / β) ^ m + B / C₀ * (‖z‖ / β) ^ m) := by
    intro m
    have htm : 0 < (t m : ℝ) := lt_of_lt_of_le (mul_pos hC₀ (pow_pos hβ0 m)) (ht m)
    have h1 : (t m : ℝ) * X ≤ ((t m : ℝ) * L + (t n : ℝ) ^ 2) * S + B * ‖z‖ ^ m := by
      have e1 : ‖(t m : ℂ) * z ^ n * c‖ = (t m : ℝ) * X := by
        simp [X, norm_pow, mul_assoc]
      have e2 : ‖(t n : ℂ) * z ^ m * c‖ = B * ‖z‖ ^ m := by
        simp [B, norm_pow]; ring
      have := norm_le_insert' ((t m : ℂ) * z ^ n * c) ((t n : ℂ) * z ^ m * c)
      rw [e1, e2] at this
      linarith [hb n m]
    have h2 : (t m : ℝ) * (X - L * S) ≤ A + B * ‖z‖ ^ m := by nlinarith
    have h3 : X - L * S ≤ (A + B * ‖z‖ ^ m) / (t m : ℝ) := by
      rw [le_div_iff₀ htm]; linarith
    have h4 : (A + B * ‖z‖ ^ m) / (t m : ℝ) ≤ (A + B * ‖z‖ ^ m) / (C₀ * β ^ m) :=
      div_le_div_of_nonneg_left (add_nonneg hA (mul_nonneg hB (pow_nonneg (norm_nonneg _) _)))
        (mul_pos hC₀ (pow_pos hβ0 m)) (ht m)
    have h5 : (A + B * ‖z‖ ^ m) / (C₀ * β ^ m) =
        A / C₀ * (1 / β) ^ m + B / C₀ * (‖z‖ / β) ^ m := by
      rw [div_pow, div_pow, one_pow]
      field_simp
    linarith
  have hlim : Filter.Tendsto (fun m : ℕ => L * S + (A / C₀ * (1 / β) ^ m + B / C₀ * (‖z‖ / β) ^ m))
      Filter.atTop (nhds (L * S + (A / C₀ * 0 + B / C₀ * 0))) := by
    refine tendsto_const_nhds.add (Filter.Tendsto.add (tendsto_const_nhds.mul ?_)
      (tendsto_const_nhds.mul ?_))
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hβ0).2 hβ)
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hβ0).2 hz)
  have := ge_of_tendsto' hlim hstep
  simpa using this

/-- **(f) The orbit bound** (audit step 5 with (a)–(d) in place of frequencies).  Let `σⁿ(W)`
be a prefix of `u` for every `n`, `W ≠ []`, `|D u (t n) ·| ≤ L` at every level, `ℓ > 0` a
left eigenvector of `M` for `β > 1`, and `q` a complex left eigenvector of `M` for `z` with
`‖z‖ < β`.  Then `‖z‖ⁿ ‖q · w‖ ≤ L ‖q‖₁` for every `n`.  No irreducibility is used. -/
theorem eigen_orbit_bound [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α} (hW : W ≠ [])
    (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u) {L : ℕ}
    (hD : ∀ n k a, |D u (len s W n) k a| ≤ L) {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) (hβ1 : 1 < β) {q : α → ℂ} {z : ℂ}
    (hq : q ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = z • q) (hz : ‖z‖ < β) (n : ℕ) :
    ‖z‖ ^ n * ‖q ⬝ᵥ parikhCast W‖ ≤ L * ∑ a, ‖q a‖ := by
  obtain ⟨c, hc, ht⟩ := len_growth s hW hℓ hℓM
  exact orbit_limit_bound (len s W) hβ1 hc ht hz (sum_nonneg fun a _ => norm_nonneg (q a))
    (eigen_window_bound s hpre hD hq) n

/-! ### (g) The cubic boundary -/

/-- A rational polynomial that is irreducible of degree `3` has no rational complex root. -/
theorem aeval_ratCast_ne_zero {f : ℚ[X]} (hf : Irreducible f) (hdeg : f.natDegree = 3) (r : ℚ) :
    aeval (r : ℂ) f ≠ 0 := by
  intro h
  have hr : f.IsRoot r := by
    rw [IsRoot.def, ← coe_aeval_eq_eval]
    apply (algebraMap ℚ ℂ).injective
    rw [map_zero, ← h, ← aeval_algebraMap_apply ℂ r f]
    rfl
  have h1 := degree_eq_one_of_irreducible_of_root hf hr
  rw [degree_eq_natDegree hf.ne_zero, hdeg] at h1
  exact absurd h1 (by decide)

/-- **The cubic boundary** (audit step 6).  A monic irreducible rational cubic has no
complex root of modulus `1`: a real one would be `±1`, a rational root; a non-real one
`z` comes with `z̄ ≠ z`, `z z̄ = 1`, so the third root is `-f(0)`, again rational. -/
theorem norm_ne_one_of_cubic {f : ℚ[X]} (hf : Irreducible f) (hm : f.Monic)
    (hdeg : f.natDegree = 3) {z : ℂ} (hz : aeval z f = 0) : ‖z‖ ≠ 1 := by
  intro h1
  by_cases him : z.im = 0
  · have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
    rcases Psc.Wielandt.eq_one_or_neg_one_of_real z.re hzr h1 with h | h
    · exact aeval_ratCast_ne_zero hf hdeg 1 (by rw [Rat.cast_one, ← h]; exact hz)
    · exact aeval_ratCast_ne_zero hf hdeg (-1) (by rw [Rat.cast_neg, Rat.cast_one, ← h]; exact hz)
  · set g := f.map (algebraMap ℚ ℂ) with hg
    have hg0 : g ≠ 0 := map_ne_zero hf.ne_zero
    have hmem : ∀ y : ℂ, y ∈ g.roots ↔ aeval y f = 0 := fun y => by
      rw [mem_roots hg0, IsRoot.def, hg, eval_map_algebraMap]
    have hconj : starRingEnd ℂ z ≠ z := fun h => him (Complex.conj_eq_iff_im.1 h)
    have hcard : g.roots.card = 3 := by
      rw [IsAlgClosed.card_roots_eq_natDegree, hg, natDegree_map, hdeg]
    obtain ⟨r₁, hr₁⟩ := Multiset.exists_cons_of_mem ((hmem z).2 hz)
    have hc1 : starRingEnd ℂ z ∈ r₁ := by
      have := (hmem _).2 (Psc.GaloisOrbit.aeval_conj_eq_zero hz)
      rw [hr₁, Multiset.mem_cons] at this
      exact this.resolve_left hconj
    obtain ⟨r₂, hr₂⟩ := Multiset.exists_cons_of_mem hc1
    have hc2 : r₂.card = 1 := by
      rw [hr₁, hr₂, Multiset.card_cons, Multiset.card_cons] at hcard; omega
    obtain ⟨μ, hμ⟩ := Multiset.card_eq_one.1 hc2
    have hroots : g.roots = z ::ₘ starRingEnd ℂ z ::ₘ {μ} := by rw [hr₁, hr₂, hμ]
    have hμroot : aeval μ f = 0 := (hmem μ).1 (by rw [hroots]; simp)
    have hzz : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
    have hcoeff := (IsAlgClosed.splits g).coeff_zero_eq_prod_roots_of_monic (hm.map _)
    rw [hroots, hg, natDegree_map, hdeg, coeff_map] at hcoeff
    simp only [Multiset.prod_cons, Multiset.prod_singleton] at hcoeff
    have hμeq : μ = ((-f.coeff 0 : ℚ) : ℂ) := by
      rw [Rat.cast_neg, ← eq_ratCast (algebraMap ℚ ℂ), hcoeff]
      linear_combination (-μ) * hzz
    exact aeval_ratCast_ne_zero hf hdeg _ (hμeq ▸ hμroot)

/-- **Negative control: the degree hypothesis of (g) is needed.**  `X² + 1` is monic and
irreducible over `ℚ` and has the root `i` of modulus `1`. -/
theorem degree_three_needed :
    (X ^ 2 + 1 : ℚ[X]).Monic ∧ Irreducible (X ^ 2 + 1 : ℚ[X]) ∧
      aeval Complex.I (X ^ 2 + 1 : ℚ[X]) = 0 ∧ ‖Complex.I‖ = 1 := by
  have hdeg : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by
    rw [show (X ^ 2 + 1 : ℚ[X]) = X ^ 2 + C 1 by simp, natDegree_X_pow_add_C]
  refine ⟨by monicity!, irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide)
    fun x hx => ?_, by simp, Complex.norm_I⟩
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at hx
  nlinarith [sq_nonneg x]

/-! ### The abstract B′ core -/

/-- **The abstract B′ core, bounded-discrepancy form** (audit steps 3–5).  Let `s` be a
substitution of a finite alphabet with primitive incidence matrix `M` (`Mᵏ > 0`, `k ≥ 1`)
and irreducible `χ_M` over `ℚ`; let `ℓ > 0` be a left eigenvector of `M` for `β` (the
Perron root, `Psc.PerronExistence`).  Let `u` be an infinite word having `σⁿ(W)` as a
prefix for every `n`, with `W ≠ []`, and suppose that the discrepancy of `(u, Sᵗⁿ u)` is
bounded by `L` at every level `t n = |σⁿ W|`: `|D u (t n) k a| ≤ L` for all `n`, `k`, `a`.
Then every complex root `z ≠ β` of `χ_M` has `‖z‖ ≤ 1`.  This is the form the proof uses;
`bprime_core` derives the bound from cuts.

Proof: if `β ≤ 1` this is `‖z‖ ≤ β` (`one_lt_perron` shows `β > 1` on two or more letters).
Otherwise take a left eigenvector `q` for `z`; `q · w ≠ 0` (cyclicity, (e)); `‖z‖ < β`
(strict dominance, (d)); `eigen_orbit_bound` ((b), (c), `len_growth`, the limit `m → ∞`)
gives `‖zⁿ (q · w)‖ ≤ L ‖q‖₁` for all `n`, hence `‖z‖ ≤ 1` (f). -/
theorem bprime_core_of_discrepancy [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α}
    (hW : W ≠ []) (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) (L : ℕ)
    (hD : ∀ n k a, |D u (len s W n) k a| ≤ L)
    {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) : ‖z‖ ≤ 1 := by
  have hN := (Psc.PerronExistence.inc_cast_primitive s hprim).1
  have hNC : ((inc s).map (Nat.cast : ℕ → ℝ)).map ((↑) : ℝ → ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by ext; simp
  by_cases hβ1 : β ≤ 1
  · exact (Psc.PerronExistence.norm_le_of_pos_left_eigen _ hN ℓ hℓ β hℓM z
      (by rw [hNC]; exact hz)).trans hβ1
  push Not at hβ1
  obtain ⟨q, hq0, hq⟩ : ∃ q : α → ℂ, q ≠ 0 ∧ q ᵥ* (inc s).map (Nat.cast : ℕ → ℂ) = z • q := by
    obtain ⟨q, hq0, hq⟩ := Psc.ConcentrationAlgebra.exists_eigenvector_of_isRoot
      ((inc s).map (Nat.cast : ℕ → ℂ))ᵀ z (by rw [Matrix.charpoly_transpose]; exact hz)
    exact ⟨q, hq0, by rw [← Matrix.mulVec_transpose]; exact hq⟩
  have hMQ : ((inc s).map (Nat.cast : ℕ → ℚ)).map (algebraMap ℚ ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by ext; simp
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil W hW
  have hwQ : (parikhCast W : α → ℚ) ≠ 0 := fun h => by
    have := congrFun h x
    simp only [parikhCast, Psc.ParikhIntertwiner.parikh, Pi.zero_apply, Nat.cast_eq_zero,
      List.count_eq_zero] at this
    exact this hx
  have hqw : q ⬝ᵥ parikhCast W ≠ 0 := by
    have := dotProduct_ne_zero_of_left_eigen _ hirr (parikhCast W) hwQ q hq0 z
      (by rw [hMQ]; exact hq)
    have e : (fun a => algebraMap ℚ ℂ ((parikhCast W : α → ℚ) a)) =
        (parikhCast W : α → ℂ) := by
      funext a; simp [parikhCast]
    rwa [e] at this
  exact norm_le_one_of_bounded hqw fun n => by
    rw [norm_mul, norm_pow]
    exact eigen_orbit_bound s hW hpre hD hℓ hℓM hβ1 hq (norm_lt_perron s hprim hℓ hℓM hz hzβ) n

/-- **The abstract B′ core** (audit steps 2–5): the hypotheses of
`bprime_core_of_discrepancy`, with the output of audit step 1 in place of the discrepancy
bound: at every level `t n = |σⁿ W|` the pair `(u, Sᵗⁿ u)` has a common cut within `L`
letters of every position (`CutGaps`, with one `L` for all `n`).  `cut_bound` turns this
into `|D| ≤ L`.  Every complex root `z ≠ β` of `χ_M` has `‖z‖ ≤ 1`. -/
theorem bprime_core [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α} (hW : W ≠ [])
    (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) (L : ℕ)
    (hgap : ∀ n, CutGaps u (len s W n) L)
    {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) : ‖z‖ ≤ 1 :=
  bprime_core_of_discrepancy s hW hpre hprim hirr L (fun n => cut_bound u _ L (hgap n)) hℓ hℓM
    hz hzβ

/-- **B′ core, block form**: the same conclusion when, at every level `t n`, the pair
`(u, Sᵗⁿ u)` is cut into aligned blocks of length at most `L`
(`cutGaps_of_blocks`). -/
theorem bprime_core_of_blocks [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α}
    (hW : W ≠ []) (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) (L : ℕ)
    (hcuts : ∀ n, ∃ c : ℕ → ℕ, StrictMono c ∧ c 0 = 0 ∧ (∀ i, c (i + 1) ≤ c i + L) ∧
      ∀ i a, D u (len s W n) (c i) a = 0)
    {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) {z : ℂ}
    (hz : ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0) (hzβ : z ≠ β) : ‖z‖ ≤ 1 :=
  bprime_core s hW hpre hprim hirr L (fun n => by
    obtain ⟨c, hc, hc0, hcL, hcut⟩ := hcuts n
    exact cutGaps_of_blocks u _ L c hc hc0 hcL hcut) hℓ hℓM hz hzβ

/-- **B′ core, bounded-discrepancy form, with the Perron data supplied**
(`Psc.PerronExistence.perron_inc`): there is a Perron root `β` (with `PerronData`, so
`β = ρ(M)` is a root of `χ_M` and its left eigenline is positive) such that every other
complex root of `χ_M` lies in the closed unit disc. -/
theorem bprime_core_perron_of_discrepancy [Fintype α] (s : α → List α) {u : ℕ → α}
    {W : List α} (hW : W ≠ []) (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) (L : ℕ)
    (hD : ∀ n k a, |D u (len s W n) k a| ≤ L) :
    ∃ (β : ℝ) (ℓ v : α → ℝ),
      Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧
        ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β → ‖z‖ ≤ 1 := by
  have : Nonempty α := ⟨W.head hW⟩
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc s hprim
  exact ⟨β, ℓ, v, hP, fun z hz hzβ =>
    bprime_core_of_discrepancy s hW hpre hprim hirr L hD hP.left_pos hP.left hz hzβ⟩

/-- **B′ core with the Perron data supplied**, cut form. -/
theorem bprime_core_perron [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α}
    (hW : W ≠ []) (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly) (L : ℕ)
    (hgap : ∀ n, CutGaps u (len s W n) L) :
    ∃ (β : ℝ) (ℓ v : α → ℝ),
      Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧
        ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β → ‖z‖ ≤ 1 :=
  bprime_core_perron_of_discrepancy s hW hpre hprim hirr L fun n => cut_bound u _ L (hgap n)

/-- **B′ on an irreducible cubic, bounded-discrepancy form** (audit step 6).  When `χ_M`
is an irreducible cubic, `β > 1` (`one_lt_perron`, since `|α| = natDegree χ_M = 3`) and
every complex root `z ≠ β` of `χ_M` has `‖z‖ < 1` (`bprime_core_of_discrepancy` and
`norm_ne_one_of_cubic`).  The Lean conclusion is exactly these two facts; reading them as
"`β` is a Pisot number" also uses that `β` is a root of `χ_M` (`PerronData.isRoot` in
`bprime_core_cubic_perron`) and that `χ_M`, monic with integer coefficients and irreducible
over `ℚ`, is its minimal polynomial, which are not restated here. -/
theorem bprime_core_cubic_of_discrepancy [Fintype α] (s : α → List α) {u : ℕ → α}
    {W : List α} (hW : W ≠ []) (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3) (L : ℕ)
    (hD : ∀ n k a, |D u (len s W n) k a| ≤ L)
    {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    1 < β ∧ ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1 := by
  have hcard : Fintype.card α = 3 := by rw [← hdeg, Matrix.charpoly_natDegree_eq_dim]
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  refine ⟨one_lt_perron s hprim hℓ hℓM, fun z hz hzβ => ?_⟩
  have hMQ : ((inc s).map (Nat.cast : ℕ → ℚ)).map (algebraMap ℚ ℂ) =
      (inc s).map (Nat.cast : ℕ → ℂ) := by ext; simp
  have hzQ : aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 := by
    rw [aeval_def, ← eval_map, ← Matrix.charpoly_map, hMQ]
    exact hz
  exact lt_of_le_of_ne (bprime_core_of_discrepancy s hW hpre hprim hirr L hD hℓ hℓM hz hzβ)
    (norm_ne_one_of_cubic hirr (Matrix.charpoly_monic _) hdeg hzQ)

/-- **B′ on an irreducible cubic** (audit step 6), cut form: `β > 1` and every complex
root `z ≠ β` of `χ_M` has `‖z‖ < 1`. -/
theorem bprime_core_cubic [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α}
    (hW : W ≠ []) (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3) (L : ℕ)
    (hgap : ∀ n, CutGaps u (len s W n) L)
    {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    1 < β ∧ ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1 :=
  bprime_core_cubic_of_discrepancy s hW hpre hprim hirr hdeg L
    (fun n => cut_bound u _ L (hgap n)) hℓ hℓM

/-- **B′ on an irreducible cubic, Perron data supplied**: the Perron root `β` of `M`
(`PerronData`: a root of `χ_M`, `β = ρ(M)`, positive eigenvectors) satisfies `β > 1`, and
every other complex root of `χ_M` lies strictly inside the unit disc. -/
theorem bprime_core_cubic_perron [Fintype α] (s : α → List α) {u : ℕ → α} {W : List α}
    (hW : W ≠ []) (hpre : ∀ n, IsPrefixOf ((subst s)^[n] W) u)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hdeg : ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly.natDegree = 3) (L : ℕ)
    (hgap : ∀ n, CutGaps u (len s W n) L) :
    ∃ (β : ℝ) (ℓ v : α → ℝ),
      Psc.PerronExistence.PerronData ((inc s).map (Nat.cast : ℕ → ℝ)) β ℓ v ∧ 1 < β ∧
        ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β → ‖z‖ < 1 := by
  have : Nonempty α := ⟨W.head hW⟩
  obtain ⟨β, ℓ, v, hP, -, -⟩ := Psc.PerronExistence.perron_inc s hprim
  exact ⟨β, ℓ, v, hP, bprime_core_cubic s hW hpre hprim hirr hdeg L hgap hP.left_pos hP.left⟩

/-! ### Control: the audit specimen `0 ↦ 01`, `1 ↦ 2`, `2 ↦ 00` -/

section Specimen

/-- The audit's non-Pisot specimen `0 ↦ 01`, `1 ↦ 2`, `2 ↦ 00`. -/
def zetaSubst : Fin 3 → List (Fin 3) := ![[0, 1], [2], [0, 0]]

/-- Its incidence matrix `[[1,0,2],[1,0,0],[0,1,0]]`. -/
theorem zeta_inc : inc zetaSubst = Matrix.of ![![1, 0, 2], ![1, 0, 0], ![0, 1, 0]] := by
  decide

/-- **Primitivity**: `M⁴ > 0`, while `M³` has a zero entry (the audit's `M⁵ > 0` is true
but not the least exponent). -/
theorem zeta_primitive :
    (∀ a c, 0 < (inc zetaSubst ^ 4) a c) ∧ ¬ ∀ a c, 0 < (inc zetaSubst ^ 3) a c :=
  ⟨fun a c => by rw [zeta_inc]; fin_cases a <;> fin_cases c <;> decide +kernel,
    fun h => absurd (h 2 1) (by rw [zeta_inc]; decide +kernel)⟩

/-- `χ_M = X³ - X² - 2` over every commutative ring. -/
theorem zeta_charpoly (K : Type*) [CommRing K] :
    ((inc zetaSubst).map (Nat.cast : ℕ → K)).charpoly = X ^ 3 - X ^ 2 - 2 := by
  rw [Psc.Cyclicity.charpoly_fin_three, zeta_inc]
  simp [Matrix.trace_fin_three, Matrix.det_fin_three, Psc.Cyclicity.wedge2,
    Psc.Cyclicity.pairFst, Psc.Cyclicity.pairSnd]
  exact map_ofNat C 2

/-- **The rational root test for a monic integer cubic.**  `X³ + a X² + b X + c` is
irreducible over `ℚ` when no integer `n` with `|n| ≤ |c|` is a root: a cubic is reducible
only with a rational root, and a rational root of a monic integer polynomial is an integer
dividing the constant term (`exists_integer_of_is_root_of_monic`).  The finite check is
decidable, so specimens discharge it by `decide`. -/
theorem irreducible_cubic (a b c : ℤ)
    (h : ∀ n ∈ Finset.Icc (-(c.natAbs : ℤ)) c.natAbs, n ^ 3 + a * n ^ 2 + b * n + c ≠ 0) :
    Irreducible (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)) := by
  have hc : c ≠ 0 := fun hc => h 0 (by simp [hc]) (by simp [hc])
  have hdeg : (X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ)).natDegree = 3 := by
    compute_degree!
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide)
  intro x hx
  have hmon : (X ^ 3 + C a * X ^ 2 + C b * X + C c : ℤ[X]).Monic := by monicity!
  have hx' : aeval x (X ^ 3 + C a * X ^ 2 + C b * X + C c : ℤ[X]) = 0 := by
    simpa [IsRoot.def] using hx
  obtain ⟨n, rfl, hn⟩ := exists_integer_of_is_root_of_monic hmon hx'
  have h0 : (X ^ 3 + C a * X ^ 2 + C b * X + C c : ℤ[X]).coeff 0 = c := by simp
  rw [h0] at hn
  refine h n ?_ ?_
  · have hb : n.natAbs ≤ c.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hc)
      (Int.natAbs_dvd_natAbs.mpr hn)
    rw [Finset.mem_Icc]
    omega
  · have : ((n ^ 3 + a * n ^ 2 + b * n + c : ℤ) : ℚ) = 0 := by simpa using hx'
    exact_mod_cast this

/-- `χ_M` is irreducible over `ℚ` (rational root test, `irreducible_cubic`: no integer `n`
with `|n| ≤ 2` is a root). -/
theorem zeta_irreducible : Irreducible ((inc zetaSubst).map (Nat.cast : ℕ → ℚ)).charpoly := by
  rw [zeta_charpoly]
  convert irreducible_cubic (-1) 0 (-2) (by decide) using 1
  simp [map_ofNat]
  ring1

/-- The Perron root `β` of the specimen lies below `2`, so the two other roots have
`‖α‖ ‖γ‖ = 2 / β > 1`: one of them lies outside the closed unit disc. -/
theorem zeta_root_outside {β : ℝ} (hβ0 : 0 < β)
    (hβ : ((inc zetaSubst).map (Nat.cast : ℕ → ℝ)).charpoly.eval β = 0) :
    ∃ z : ℂ, ((inc zetaSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 ∧ z ≠ β ∧ 1 < ‖z‖ := by
  rw [zeta_charpoly] at hβ
  simp only [eval_sub, eval_pow, eval_X, eval_ofNat] at hβ
  have hβ2 : β < 2 := by nlinarith [sq_nonneg β]
  set MQ := (inc zetaSubst).map (Nat.cast : ℕ → ℚ)
  have hev : ∀ z : ℂ, aeval z MQ.charpoly = z ^ 3 - z ^ 2 - 2 := fun z => by
    rw [zeta_charpoly]; simp [map_ofNat]
  have hevC : ∀ z : ℂ,
      ((inc zetaSubst).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = z ^ 3 - z ^ 2 - 2 := fun z => by
    rw [zeta_charpoly]; simp
  have hβC : aeval (β : ℂ) MQ.charpoly = 0 := by
    rw [hev]; exact_mod_cast hβ
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ :=
    Psc.Degree4Floor.exists_other_roots MQ zeta_irreducible hβC
  have hdet := Psc.SectorBridge.det_eq_mul_roots MQ hβC hα hγ hβα hβγ hαγ
  have hdet2 : MQ.det = 2 := by
    simp [MQ, zeta_inc, Matrix.det_fin_three]
  rw [hdet2] at hdet
  have hn : ‖((2 : ℚ) : ℂ)‖ = ‖(β : ℂ) * α * γ‖ := by rw [hdet]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ0] at hn
  have hn2 : (2 : ℝ) = β * ‖α‖ * ‖γ‖ := by simpa using hn
  by_contra hcon
  push Not at hcon
  have hα1 := hcon α (by rw [hevC, ← hev]; exact hα) (Ne.symm hβα)
  have hγ1 := hcon γ (by rw [hevC, ← hev]; exact hγ) (Ne.symm hβγ)
  have : ‖α‖ * ‖γ‖ ≤ 1 := by
    calc ‖α‖ * ‖γ‖ ≤ 1 * 1 := mul_le_mul hα1 hγ1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  nlinarith [norm_nonneg α, norm_nonneg γ]

/-- **The prefix hypothesis is satisfiable**: with `W = 0` (`0 <+: σ 0 = 01`), the limit
word of `Psc.FixedPointLimit` has every `σⁿ(0)` as a prefix. -/
theorem zeta_fixed_point : ∃ u : ℕ → Fin 3, ∀ n, IsPrefixOf ((subst zetaSubst)^[n] [0]) u := by
  have hW : ([0] : List (Fin 3)) <+: subst zetaSubst [0] := ⟨[1], by decide⟩
  have hgrow := Psc.FixedPointLimit.grow_of_nonerasing zetaSubst (by decide) (p := 1)
    (u := [0]) (by simpa using hW) (by decide)
  exact ⟨_, isPrefixOf_limit zetaSubst hW hgrow⟩

/-- **Control: Corollary B (i) at the level of this module, for the specimen,
bounded-discrepancy form.**  For every infinite word `u` having every `σⁿ(W)` as a prefix
(`W ≠ []`) and every `L`, the discrepancy of `(u, S^{t n} u)` exceeds `L` somewhere at some
level `t n`.  All other hypotheses of `bprime_core_of_discrepancy` hold (`zeta_primitive`,
`zeta_irreducible`, `zeta_fixed_point`), so the theorem is not vacuous here. -/
theorem zeta_unbounded_discrepancy {u : ℕ → Fin 3} {W : List (Fin 3)} (hW : W ≠ [])
    (hpre : ∀ n, IsPrefixOf ((subst zetaSubst)^[n] W) u) (L : ℕ) :
    ¬ ∀ n k a, |D u (len zetaSubst W n) k a| ≤ L := by
  intro hD
  obtain ⟨β, ℓ, v, hP, hall⟩ := bprime_core_perron_of_discrepancy zetaSubst hW hpre
    ⟨4, by norm_num, zeta_primitive.1⟩ zeta_irreducible L hD
  obtain ⟨z, hz, hzβ, hz1⟩ := zeta_root_outside hP.pos hP.isRoot
  exact absurd (hall z hz hzβ) (not_le.2 hz1)

/-- **Control: Corollary B (i), cut form.**  For the specimen, every `u` with the prefix
property, every `W ≠ []` and every `L`, the cut hypothesis of `bprime_core` fails: at some
level `t n` some position is more than `L` letters from the next common cut.  (That a
terminating `bpa-W` would give such an `L` is audit step 1, not proved here; the composed
non-termination statement is `Psc.BPrime.zeta_IW_infinite`.) -/
theorem zeta_no_uniform_cuts {u : ℕ → Fin 3} {W : List (Fin 3)} (hW : W ≠ [])
    (hpre : ∀ n, IsPrefixOf ((subst zetaSubst)^[n] W) u) (L : ℕ) :
    ¬ ∀ n, CutGaps u (len zetaSubst W n) L := fun hgap =>
  zeta_unbounded_discrepancy hW hpre L fun n => cut_bound u _ L (hgap n)

end Specimen

/-! ### Control: the hypotheses of `bprime_core` are jointly satisfiable -/

section Consistency

/-- The one-letter substitution `0 ↦ 00`. -/
def oneSubst : Fin 1 → List (Fin 1) := fun _ => [0, 0]

/-- **Joint satisfiability** of the full hypothesis set of `bprime_core`, on one letter:
`σ = (0 ↦ 00)`, `u = 0^∞`, `W = 0`, `L = 0`, `β = 2`, `ℓ = 1`.  Every `σⁿ(0)` is a prefix of
`u`, `M = (2)` is primitive with `χ_M = X - 2` irreducible, every position is a common cut
at every level, and `ℓ M = 2 ℓ`.  (The conclusion of `bprime_core` is empty here: `χ_M`
has no root other than `β`.  `zeta_unbounded_discrepancy` is the non-vacuity control on
three letters.) -/
theorem one_letter_consistent :
    (∀ n, IsPrefixOf ((subst oneSubst)^[n] [0]) fun _ => (0 : Fin 1)) ∧
      (∃ k ≥ 1, ∀ a c, 0 < (inc oneSubst ^ k) a c) ∧
      Irreducible ((inc oneSubst).map (Nat.cast : ℕ → ℚ)).charpoly ∧
      (∀ n, CutGaps (fun _ => (0 : Fin 1)) (len oneSubst [0] n) 0) ∧
      (fun _ => (1 : ℝ)) ᵥ* (inc oneSubst).map (Nat.cast : ℕ → ℝ) = (2 : ℝ) • fun _ => 1 := by
  have hP : ∀ (m : ℕ) (a : Fin 1), P (fun _ => (0 : Fin 1)) m a = m := fun m a => by
    simp [P, Subsingleton.elim (0 : Fin 1) a]
  refine ⟨fun n i h => Subsingleton.elim _ _,
    ⟨1, le_rfl, fun a c => by fin_cases a; fin_cases c; decide +kernel⟩, ?_,
    fun n k => ⟨k, le_rfl, le_rfl, fun a => ?_⟩, ?_⟩
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin, Nat.cast_one]
  · simp only [D, hP]
    omega
  · ext j
    simp [vecMul, dotProduct, inc, oneSubst]

end Consistency

end Psc.BPrimeCore
