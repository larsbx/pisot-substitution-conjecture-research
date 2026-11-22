import Mathlib

/-!
# A shifted radix recurrence with monotone coefficients has one cycle

Integer sequences `w`, with digit data `(a, d, e)`, satisfying

* `0 < w (i+2) + θ w (i+1) + 2α w i < 1 + 2α`, `θ = 2α + 2α²`, `θ < 1`;
* `d (i+2) + e (i+3) = k w (i+2) + 2 w (i+1) + 2 w i - w (i+3)`;
* the child relation of the substitution `0 ↦ 1, 1 ↦ 0 1^k 2, 2 ↦ 001`

eventually repeat `1, 0, 0` with every type and digit equal to one. No
periodicity is assumed.

The proof has no analysis in it. Put `R (i+1) = R i + 3 w i - 1`. The real
inequality says that `w (i+2) + θ w (i+1) + 2α w i` is a convex combination
of three tail sums shifted by less than `1 + 2α`; this confines `R (i+3)`
to the interval spanned by `R i, R (i+1), R (i+2)`. The windows are nested
integer intervals, so they are eventually constant, and then two of the
three residue classes of `R` are frozen at the ends of the interval. The
digit relation excludes every frozen pattern but one.

Source decision: `docs/c4-zero-fibre-anchor-proof-2026-11-22.md`.
-/

namespace Psc.ShiftedRadixCycle

/-- The digit data of one inflation step: parent type `a`, child type
`a'`, the number `d'` of `0`s and the number `e'` of `1`s before the child
in the image of the parent. -/
def Child (k a a' d' e' : ℤ) : Prop :=
  (a = 0 ∧ a' = 1 ∧ d' = 0 ∧ e' = 0) ∨
  (a = 1 ∧ a' = 0 ∧ d' = 0 ∧ e' = 0) ∨
  (a = 1 ∧ a' = 1 ∧ d' = 1 ∧ 0 ≤ e' ∧ e' < k) ∨
  (a = 1 ∧ a' = 2 ∧ d' = 1 ∧ e' = k) ∨
  (a = 2 ∧ a' = 0 ∧ d' = 0 ∧ e' = 0) ∨
  (a = 2 ∧ a' = 0 ∧ d' = 1 ∧ e' = 0) ∨
  (a = 2 ∧ a' = 1 ∧ d' = 2 ∧ e' = 0)

/-- Three times the partial sums of `w`, detrended by the index. -/
def R (w : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | i + 1 => R w i + 3 * w i - 1

theorem R_succ (w : ℕ → ℤ) (i : ℕ) : R w (i + 1) = R w i + 3 * w i - 1 := rfl

theorem R_succ₂ (w : ℕ → ℤ) (i : ℕ) : R w (i + 2) = R w (i + 1) + 3 * w (i + 1) - 1 := rfl

theorem R_succ₃ (w : ℕ → ℤ) (i : ℕ) : R w (i + 3) = R w (i + 2) + 3 * w (i + 2) - 1 := rfl

/-- The convexity step. With `x, y, z` three consecutive values, the
detrended triple sum is not below all of `0`, the detrended single value
and the detrended pair sum, and not above all of them. -/
theorem window {α : ℝ} (hα : 0 < α) (hθ : 2 * α + 2 * α ^ 2 < 1) (x y z : ℤ)
    (h0 : 0 < (z : ℝ) + (2 * α + 2 * α ^ 2) * y + 2 * α * x)
    (h1 : (z : ℝ) + (2 * α + 2 * α ^ 2) * y + 2 * α * x < 1 + 2 * α) :
    (0 ≤ 3 * (x + y + z) - 3 ∨ 3 * x - 1 ≤ 3 * (x + y + z) - 3 ∨
        3 * (x + y) - 2 ≤ 3 * (x + y + z) - 3) ∧
      (3 * (x + y + z) - 3 ≤ 0 ∨ 3 * (x + y + z) - 3 ≤ 3 * x - 1 ∨
        3 * (x + y + z) - 3 ≤ 3 * (x + y) - 2) := by
  have hp1 : 0 < 1 - (2 * α + 2 * α ^ 2) := by linarith
  have hp2 : 0 < 2 * α ^ 2 := by positivity
  have hp3 : 0 < 2 * α := by positivity
  constructor
  · by_contra h
    have hz : z ≤ 0 := by omega
    have hyz : y + z ≤ 0 := by omega
    have hC : x + y + z ≤ 0 := by omega
    have hz' : (z : ℝ) ≤ 0 := by exact_mod_cast hz
    have hyz' : (y : ℝ) + z ≤ 0 := by exact_mod_cast hyz
    have hC' : (x : ℝ) + y + z ≤ 0 := by exact_mod_cast hC
    nlinarith [mul_nonneg hp1.le (neg_nonneg.mpr hz'), mul_nonneg hp2.le (neg_nonneg.mpr hyz'),
      mul_nonneg hp3.le (neg_nonneg.mpr hC')]
  · by_contra h
    have hz : 1 ≤ z := by omega
    have hyz : 1 ≤ y + z := by omega
    have hC : 2 ≤ x + y + z := by omega
    have hz' : (0 : ℝ) ≤ z - 1 := by exact_mod_cast sub_nonneg.mpr hz
    have hyz' : (0 : ℝ) ≤ (y : ℝ) + z - 1 := by
      have : (1 : ℝ) ≤ ((y + z : ℤ) : ℝ) := by exact_mod_cast hyz
      push_cast at this; linarith
    have hC' : (0 : ℝ) ≤ (x : ℝ) + y + z - 2 := by
      have : (2 : ℝ) ≤ ((x + y + z : ℤ) : ℝ) := by exact_mod_cast hC
      push_cast at this; linarith
    nlinarith [mul_nonneg hp1.le hz', mul_nonneg hp2.le hyz', mul_nonneg hp3.le hC']

/-- The real inequality at every index. -/
def Bounded (α : ℝ) (w : ℕ → ℤ) : Prop :=
  ∀ i, 0 < (w (i + 2) : ℝ) + (2 * α + 2 * α ^ 2) * w (i + 1) + 2 * α * w i ∧
    (w (i + 2) : ℝ) + (2 * α + 2 * α ^ 2) * w (i + 1) + 2 * α * w i < 1 + 2 * α

/-- Least and greatest value of `R` on three consecutive indices. -/
def lo (w : ℕ → ℤ) (i : ℕ) : ℤ := min (R w i) (min (R w (i + 1)) (R w (i + 2)))

def hi (w : ℕ → ℤ) (i : ℕ) : ℤ := max (R w i) (max (R w (i + 1)) (R w (i + 2)))

theorem lo_spec (w : ℕ → ℤ) (i : ℕ) :
    lo w i ≤ R w i ∧ lo w i ≤ R w (i + 1) ∧ lo w i ≤ R w (i + 2) ∧
      (lo w i = R w i ∨ lo w i = R w (i + 1) ∨ lo w i = R w (i + 2)) := by
  unfold lo
  rcases le_total (R w (i + 1)) (R w (i + 2)) with h | h <;>
    rcases le_total (R w i) (R w (i + 1)) with h' | h' <;>
    rcases le_total (R w i) (R w (i + 2)) with h'' | h'' <;>
    simp [h, h', h''] <;> omega

theorem lo_spec_succ (w : ℕ → ℤ) (i : ℕ) :
    lo w (i + 1) ≤ R w (i + 1) ∧ lo w (i + 1) ≤ R w (i + 2) ∧ lo w (i + 1) ≤ R w (i + 3) ∧
      (lo w (i + 1) = R w (i + 1) ∨ lo w (i + 1) = R w (i + 2) ∨ lo w (i + 1) = R w (i + 3)) :=
  lo_spec w (i + 1)

theorem hi_spec (w : ℕ → ℤ) (i : ℕ) :
    R w i ≤ hi w i ∧ R w (i + 1) ≤ hi w i ∧ R w (i + 2) ≤ hi w i ∧
      (hi w i = R w i ∨ hi w i = R w (i + 1) ∨ hi w i = R w (i + 2)) := by
  unfold hi
  rcases le_total (R w (i + 1)) (R w (i + 2)) with h | h <;>
    rcases le_total (R w i) (R w (i + 1)) with h' | h' <;>
    rcases le_total (R w i) (R w (i + 2)) with h'' | h'' <;>
    simp [h, h', h''] <;> omega

theorem hi_spec_succ (w : ℕ → ℤ) (i : ℕ) :
    R w (i + 1) ≤ hi w (i + 1) ∧ R w (i + 2) ≤ hi w (i + 1) ∧ R w (i + 3) ≤ hi w (i + 1) ∧
      (hi w (i + 1) = R w (i + 1) ∨ hi w (i + 1) = R w (i + 2) ∨ hi w (i + 1) = R w (i + 3)) :=
  hi_spec w (i + 1)

section Windows

variable {α : ℝ} {w : ℕ → ℤ}

theorem R_window (hα : 0 < α) (hθ : 2 * α + 2 * α ^ 2 < 1) (hE : Bounded α w) (i : ℕ) :
    lo w i ≤ R w (i + 3) ∧ R w (i + 3) ≤ hi w i := by
  have h := window hα hθ (w i) (w (i + 1)) (w (i + 2)) (hE i).1 (hE i).2
  have e1 := R_succ w i
  have e2 := R_succ₂ w i
  have e3 := R_succ₃ w i
  have hl := lo_spec w i
  have hh := hi_spec w i
  omega

theorem nested_succ (hα : 0 < α) (hθ : 2 * α + 2 * α ^ 2 < 1) (hE : Bounded α w) (i : ℕ) :
    lo w i ≤ lo w (i + 1) ∧ hi w (i + 1) ≤ hi w i := by
  have h := R_window hα hθ hE i
  have hl := lo_spec w i
  have hh := hi_spec w i
  have hl' := lo_spec_succ w i
  have hh' := hi_spec_succ w i
  omega

theorem nested (hα : 0 < α) (hθ : 2 * α + 2 * α ^ 2 < 1) (hE : Bounded α w) {i j : ℕ}
    (hij : i ≤ j) : lo w i ≤ lo w j ∧ hi w j ≤ hi w i := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨le_rfl, le_rfl⟩
  | succ j _ ih =>
    have h := nested_succ hα hθ hE j
    exact ⟨ih.1.trans h.1, h.2.trans ih.2⟩

theorem lo_le_hi (w : ℕ → ℤ) (i : ℕ) : lo w i ≤ hi w i :=
  (lo_spec w i).1.trans (hi_spec w i).1

/-- Nested integer intervals are eventually constant. -/
theorem eventually_constant (hα : 0 < α) (hθ : 2 * α + 2 * α ^ 2 < 1) (hE : Bounded α w) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → lo w i = lo w i₀ ∧ hi w i = hi w i₀ := by
  obtain ⟨_, ⟨i₀, rfl⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    (Set.range fun i => (hi w i - lo w i).toNat) ⟨_, 0, rfl⟩
  refine ⟨i₀, fun i hi' => ?_⟩
  have h := nested hα hθ hE hi'
  have hm := hmin _ ⟨i, rfl⟩
  have h1 := lo_le_hi w i
  have h2 := lo_le_hi w i₀
  simp only at hm
  omega

/-- After the windows stop moving, the least value recurs with period three. -/
theorem lo_recurs {i₀ : ℕ} (hc : ∀ i, i₀ ≤ i → lo w i = lo w i₀ ∧ hi w i = hi w i₀)
    {b : ℕ} (hb : i₀ ≤ b) (h : R w b = lo w i₀) : R w (b + 3) = lo w i₀ := by
  have h1 := (hc (b + 1) (by omega)).1
  have e1 := R_succ w b
  have e2 := R_succ₂ w b
  have hl := lo_spec_succ w b
  omega

theorem hi_recurs {i₀ : ℕ} (hc : ∀ i, i₀ ≤ i → lo w i = lo w i₀ ∧ hi w i = hi w i₀)
    {b : ℕ} (hb : i₀ ≤ b) (h : R w b = hi w i₀) : R w (b + 3) = hi w i₀ := by
  have h1 := (hc (b + 1) (by omega)).2
  have e1 := R_succ w b
  have e2 := R_succ₂ w b
  have hh := hi_spec_succ w b
  omega

theorem lo_recurs_mul {i₀ : ℕ} (hc : ∀ i, i₀ ≤ i → lo w i = lo w i₀ ∧ hi w i = hi w i₀)
    {b : ℕ} (hb : i₀ ≤ b) (h : R w b = lo w i₀) (j : ℕ) : R w (b + 3 * j) = lo w i₀ := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [show b + 3 * (j + 1) = b + 3 * j + 3 by ring]
    exact lo_recurs hc (by omega) ih

theorem hi_recurs_mul {i₀ : ℕ} (hc : ∀ i, i₀ ≤ i → lo w i = lo w i₀ ∧ hi w i = hi w i₀)
    {b : ℕ} (hb : i₀ ≤ b) (h : R w b = hi w i₀) (j : ℕ) : R w (b + 3 * j) = hi w i₀ := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [show b + 3 * (j + 1) = b + 3 * j + 3 by ring]
    exact hi_recurs hc (by omega) ih

/-- The two frozen patterns. In the first the greatest value follows the
least one; in the second it precedes it. -/
def PatternI (w : ℕ → ℤ) (b₀ : ℕ) (g : ℤ) : Prop :=
  ∀ j, w (b₀ + 3 * j) = g ∧ w (b₀ + 3 * j + 1) ≤ 0 ∧ w (b₀ + 3 * j + 2) ≤ 0 ∧
    w (b₀ + 3 * j) + w (b₀ + 3 * j + 1) + w (b₀ + 3 * j + 2) = 1

def PatternII (w : ℕ → ℤ) (b₀ : ℕ) (γ : ℤ) : Prop :=
  ∀ j, 1 ≤ w (b₀ + 3 * j) ∧ 1 ≤ w (b₀ + 3 * j + 1) ∧ w (b₀ + 3 * j + 2) = γ ∧
    w (b₀ + 3 * j) + w (b₀ + 3 * j + 1) + w (b₀ + 3 * j + 2) = 1

theorem frozen (hα : 0 < α) (hθ : 2 * α + 2 * α ^ 2 < 1) (hE : Bounded α w) :
    ∃ b₀ : ℕ, (∃ g : ℤ, 1 ≤ g ∧ PatternI w b₀ g) ∨ (∃ γ : ℤ, γ ≤ -1 ∧ PatternII w b₀ γ) := by
  obtain ⟨i₀, hc⟩ := eventually_constant hα hθ hE
  have hmin : ∃ b, i₀ ≤ b ∧ R w b = lo w i₀ := by
    rcases (lo_spec w i₀).2.2.2 with h | h | h
    · exact ⟨i₀, le_rfl, h.symm⟩
    · exact ⟨i₀ + 1, by omega, h.symm⟩
    · exact ⟨i₀ + 2, by omega, h.symm⟩
  obtain ⟨b, hb, hRb⟩ := hmin
  have hlo := fun j => lo_recurs_mul hc hb hRb j
  have hwin := hc b hb
  have e1 := R_succ w b
  have e2 := R_succ₂ w b
  have e3 := R_succ₃ w b
  have hl := lo_spec w b
  have hh := hi_spec w b
  have hb3 := lo_recurs hc hb hRb
  have hcase : R w (b + 1) = hi w i₀ ∨ R w (b + 2) = hi w i₀ := by omega
  refine ⟨b, ?_⟩
  rcases hcase with h | h
  · left
    have hhi := fun j => hi_recurs_mul hc (by omega : i₀ ≤ b + 1) h j
    refine ⟨w b, by omega, fun j => ?_⟩
    have a0 := hlo j
    have a1 := hhi j
    have a3 := hlo (j + 1)
    have hw := hc (b + 3 * j) (by omega)
    have f1 := R_succ w (b + 3 * j)
    have f2 := R_succ₂ w (b + 3 * j)
    have f3 := R_succ₃ w (b + 3 * j)
    have gl := lo_spec w (b + 3 * j)
    have gh := hi_spec w (b + 3 * j)
    rw [show b + 1 + 3 * j = b + 3 * j + 1 by ring] at a1
    rw [show b + 3 * (j + 1) = b + 3 * j + 3 by ring] at a3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · right
    have hhi := fun j => hi_recurs_mul hc (by omega : i₀ ≤ b + 2) h j
    refine ⟨w (b + 2), by omega, fun j => ?_⟩
    have a0 := hlo j
    have a2 := hhi j
    have a3 := hlo (j + 1)
    have hw := hc (b + 3 * j) (by omega)
    have f1 := R_succ w (b + 3 * j)
    have f2 := R_succ₂ w (b + 3 * j)
    have f3 := R_succ₃ w (b + 3 * j)
    have gl := lo_spec w (b + 3 * j)
    have gh := hi_spec w (b + 3 * j)
    rw [show b + 2 + 3 * j = b + 3 * j + 2 by ring] at a2
    rw [show b + 3 * (j + 1) = b + 3 * j + 3 by ring] at a3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end Windows

section Digits

variable {k : ℤ}

theorem child_bounds {a a' d' e' : ℤ} (h : Child k a a' d' e') (hk : 0 ≤ k) :
    0 ≤ d' ∧ d' ≤ 2 ∧ 0 ≤ e' ∧ e' ≤ k := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_d_two {a a' d' e' : ℤ} (h : Child k a a' d' e') : d' = 2 → a = 2 := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_into_two {a a' d' e' : ℤ} (h : Child k a a' d' e') :
    a' = 2 → a = 1 ∧ d' = 1 ∧ e' = k := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_of_two {a a' d' e' : ℤ} (h : Child k a a' d' e') :
    a = 2 → e' = 0 ∧ (a' = 0 ∨ (a' = 1 ∧ d' = 2)) := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_e_eq {a a' d' e' : ℤ} (h : Child k a a' d' e') (hk : 2 ≤ k) :
    e' = k → a' = 2 := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_d_zero {a a' d' e' : ℤ} (h : Child k a a' d' e') :
    d' = 0 → e' = 0 ∧ (a' = 0 ∨ (a' = 1 ∧ a = 0)) := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_of_zero {a a' d' e' : ℤ} (h : Child k a a' d' e') :
    a = 0 → a' = 1 ∧ d' = 0 ∧ e' = 0 := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_into_zero {a a' d' e' : ℤ} (h : Child k a a' d' e') :
    a' = 0 → d' ≤ 1 ∧ e' = 0 := by
  rcases h with h | h | h | h | h | h | h <;> omega

theorem child_e_pos {a a' d' e' : ℤ} (h : Child k a a' d' e') :
    1 ≤ e' → a = 1 ∧ d' = 1 ∧ ((a' = 1 ∧ e' < k) ∨ (a' = 2 ∧ e' = k)) := by
  rcases h with h | h | h | h | h | h | h <;> omega

variable {a d e w : ℕ → ℤ}

/-- The digit data along a sequence: the child relation and the identity
`d + e = k w + 2 w' + 2 w'' - w⁺` forced by the incidence matrix. -/
def Digits (k : ℤ) (a d e w : ℕ → ℤ) : Prop :=
  (∀ i, Child k (a i) (a (i + 1)) (d (i + 1)) (e (i + 1))) ∧
    ∀ i, d (i + 2) + e (i + 3) = k * w (i + 2) + 2 * w (i + 1) + 2 * w i - w (i + 3)

/-- The pattern in which the greatest value precedes the least one does
not occur. -/
theorem patternII_false (hk : 2 ≤ k) (hD : Digits k a d e w) {b : ℕ} {γ : ℤ}
    (hγ : γ ≤ -1) (h : PatternII w b γ) : False := by
  obtain ⟨hC, hn⟩ := hD
  have p0 : 1 ≤ w b ∧ 1 ≤ w (b + 1) ∧ w (b + 2) = γ ∧ w b + w (b + 1) + w (b + 2) = 1 := h 0
  have p1 : 1 ≤ w (b + 3) ∧ 1 ≤ w (b + 4) ∧ w (b + 5) = γ ∧
      w (b + 3) + w (b + 4) + w (b + 5) = 1 := h 1
  have p2 : 1 ≤ w (b + 6) ∧ 1 ≤ w (b + 7) ∧ w (b + 8) = γ ∧
      w (b + 6) + w (b + 7) + w (b + 8) = 1 := h 2
  have n2 : d (b + 2) + e (b + 3) = k * w (b + 2) + 2 * w (b + 1) + 2 * w b - w (b + 3) := hn b
  have n3 : d (b + 3) + e (b + 4) =
      k * w (b + 3) + 2 * w (b + 2) + 2 * w (b + 1) - w (b + 4) := hn (b + 1)
  have n4 : d (b + 4) + e (b + 5) =
      k * w (b + 4) + 2 * w (b + 3) + 2 * w (b + 2) - w (b + 5) := hn (b + 2)
  have n5 : d (b + 5) + e (b + 6) =
      k * w (b + 5) + 2 * w (b + 4) + 2 * w (b + 3) - w (b + 6) := hn (b + 3)
  have n6 : d (b + 6) + e (b + 7) =
      k * w (b + 6) + 2 * w (b + 5) + 2 * w (b + 4) - w (b + 7) := hn (b + 4)
  have n7 : d (b + 7) + e (b + 8) =
      k * w (b + 7) + 2 * w (b + 6) + 2 * w (b + 5) - w (b + 8) := hn (b + 5)
  have c1 : Child k (a (b + 1)) (a (b + 2)) (d (b + 2)) (e (b + 2)) := hC (b + 1)
  have c2 : Child k (a (b + 2)) (a (b + 3)) (d (b + 3)) (e (b + 3)) := hC (b + 2)
  have c3 : Child k (a (b + 3)) (a (b + 4)) (d (b + 4)) (e (b + 4)) := hC (b + 3)
  have c4 : Child k (a (b + 4)) (a (b + 5)) (d (b + 5)) (e (b + 5)) := hC (b + 4)
  have c5 : Child k (a (b + 5)) (a (b + 6)) (d (b + 6)) (e (b + 6)) := hC (b + 5)
  have c6 : Child k (a (b + 6)) (a (b + 7)) (d (b + 7)) (e (b + 7)) := hC (b + 6)
  have c7 : Child k (a (b + 7)) (a (b + 8)) (d (b + 8)) (e (b + 8)) := hC (b + 7)
  have hk0 : (0 : ℤ) ≤ k := by omega
  have b1 := child_bounds c1 hk0
  have b2 := child_bounds c2 hk0
  have b3 := child_bounds c3 hk0
  have b4 := child_bounds c4 hk0
  have b5 := child_bounds c5 hk0
  have b6 := child_bounds c6 hk0
  have b7 := child_bounds c7 hk0
  have hk3 : k ≤ 3 := by
    by_contra hk4
    have hprod : 0 ≤ (k - 4) * (-γ - 1) := mul_nonneg (by omega) (by omega)
    have e2 : k * w (b + 2) = k * γ := by rw [p0.2.2.1]
    nlinarith [p0.2.2.2, p1.1, b1.1, b2.2.2.1]
  obtain rfl | rfl : k = 2 ∨ k = 3 := by omega
  · have hγ2 : γ = -1 ∨ γ = -2 := by omega
    rcases hγ2 with rfl | rfl
    · have hsplit : (d (b + 4) = 1 ∧ e (b + 5) = 2) ∨ (d (b + 4) = 2 ∧ e (b + 5) = 1) := by
        omega
      rcases hsplit with ⟨-, he⟩ | ⟨hd, -⟩
      · have a5 := child_e_eq c4 hk he
        have o5 := child_of_two c5 a5
        have i4 := child_into_two c4 a5
        rcases o5.2 with a6 | ⟨-, d6⟩
        · have z6 := child_of_zero c6 a6
          omega
        · omega
      · have a3 := child_d_two c3 hd
        have i2 := child_into_two c2 a3
        omega
    · have he : e (b + 5) = 2 := by omega
      have hd : d (b + 7) = 2 := by omega
      have a5 := child_e_eq c4 hk he
      have o5 := child_of_two c5 a5
      have a6 := child_d_two c6 hd
      have i5 := child_into_two c5 a6
      omega
  · have hd : d (b + 5) = 0 := by omega
    have z4 := child_d_zero c4 hd
    omega

/-- In the other pattern the frozen value is one. -/
theorem patternI_one (hk : 2 ≤ k) (hD : Digits k a d e w) {b : ℕ} {g : ℤ}
    (hg : 1 ≤ g) (h : PatternI w b g) : g = 1 := by
  obtain ⟨hC, hn⟩ := hD
  have p0 : w b = g ∧ w (b + 1) ≤ 0 ∧ w (b + 2) ≤ 0 ∧ w b + w (b + 1) + w (b + 2) = 1 := h 0
  have p1 : w (b + 3) = g ∧ w (b + 4) ≤ 0 ∧ w (b + 5) ≤ 0 ∧
      w (b + 3) + w (b + 4) + w (b + 5) = 1 := h 1
  have p2 : w (b + 6) = g ∧ w (b + 7) ≤ 0 ∧ w (b + 8) ≤ 0 ∧
      w (b + 6) + w (b + 7) + w (b + 8) = 1 := h 2
  have p3 : w (b + 9) = g ∧ w (b + 10) ≤ 0 ∧ w (b + 11) ≤ 0 ∧
      w (b + 9) + w (b + 10) + w (b + 11) = 1 := h 3
  have n3 : d (b + 3) + e (b + 4) =
      k * w (b + 3) + 2 * w (b + 2) + 2 * w (b + 1) - w (b + 4) := hn (b + 1)
  have n5 : d (b + 5) + e (b + 6) =
      k * w (b + 5) + 2 * w (b + 4) + 2 * w (b + 3) - w (b + 6) := hn (b + 3)
  have n6 : d (b + 6) + e (b + 7) =
      k * w (b + 6) + 2 * w (b + 5) + 2 * w (b + 4) - w (b + 7) := hn (b + 4)
  have n7 : d (b + 7) + e (b + 8) =
      k * w (b + 7) + 2 * w (b + 6) + 2 * w (b + 5) - w (b + 8) := hn (b + 5)
  have n8 : d (b + 8) + e (b + 9) =
      k * w (b + 8) + 2 * w (b + 7) + 2 * w (b + 6) - w (b + 9) := hn (b + 6)
  have n9 : d (b + 9) + e (b + 10) =
      k * w (b + 9) + 2 * w (b + 8) + 2 * w (b + 7) - w (b + 10) := hn (b + 7)
  have n10 : d (b + 10) + e (b + 11) =
      k * w (b + 10) + 2 * w (b + 9) + 2 * w (b + 8) - w (b + 11) := hn (b + 8)
  have c2 : Child k (a (b + 2)) (a (b + 3)) (d (b + 3)) (e (b + 3)) := hC (b + 2)
  have c3 : Child k (a (b + 3)) (a (b + 4)) (d (b + 4)) (e (b + 4)) := hC (b + 3)
  have c4 : Child k (a (b + 4)) (a (b + 5)) (d (b + 5)) (e (b + 5)) := hC (b + 4)
  have c5 : Child k (a (b + 5)) (a (b + 6)) (d (b + 6)) (e (b + 6)) := hC (b + 5)
  have c6 : Child k (a (b + 6)) (a (b + 7)) (d (b + 7)) (e (b + 7)) := hC (b + 6)
  have c7 : Child k (a (b + 7)) (a (b + 8)) (d (b + 8)) (e (b + 8)) := hC (b + 7)
  have c8 : Child k (a (b + 8)) (a (b + 9)) (d (b + 9)) (e (b + 9)) := hC (b + 8)
  have c9 : Child k (a (b + 9)) (a (b + 10)) (d (b + 10)) (e (b + 10)) := hC (b + 9)
  have c10 : Child k (a (b + 10)) (a (b + 11)) (d (b + 11)) (e (b + 11)) := hC (b + 10)
  have hk0 : (0 : ℤ) ≤ k := by omega
  have b2 := child_bounds c2 hk0
  have b3 := child_bounds c3 hk0
  have b4 := child_bounds c4 hk0
  have b5 := child_bounds c5 hk0
  have b6 := child_bounds c6 hk0
  have b7 := child_bounds c7 hk0
  have b8 := child_bounds c8 hk0
  have b9 := child_bounds c9 hk0
  have b10 := child_bounds c10 hk0
  have hX : k * w (b + 5) ≤ 2 * w (b + 5) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k - 2 by omega) (show (0 : ℤ) ≤ -w (b + 5) by omega)]
  have hg2 : g ≤ 2 := by omega
  by_contra hg1
  have hg' : g = 2 := by omega
  have e3 : k * w (b + 3) = 2 * k := by rw [p1.1, hg']; ring
  have hk4 : k ≤ 4 := by omega
  obtain rfl | rfl | rfl : k = 2 ∨ k = 3 ∨ k = 4 := by omega
  · have d5 : d (b + 5) = 0 := by omega
    have d8 : d (b + 8) = 0 := by omega
    have h5 : a (b + 5) ≠ 0 := by
      intro h0
      have o := child_of_zero c5 h0
      have e7 : e (b + 7) = 2 := by omega
      have a7 := child_e_eq c6 hk e7
      have j := child_into_two c6 a7
      have u := child_of_two c7 a7
      omega
    have h8 : a (b + 8) ≠ 0 := by
      intro h0
      have o := child_of_zero c8 h0
      have e10 : e (b + 10) = 2 := by omega
      have a10 := child_e_eq c9 hk e10
      have j := child_into_two c9 a10
      have u := child_of_two c10 a10
      omega
    rcases (child_d_zero c7 d8).2 with h | ⟨-, h7⟩
    · exact h8 h
    · have v := child_into_zero c6 h7
      have d6 : d (b + 6) = 2 := by omega
      have a5 := child_d_two c5 d6
      rcases (child_d_zero c4 d5).2 with h | ⟨h, -⟩
      · exact h5 h
      · omega
  · have d6 : d (b + 6) = 2 := by omega
    have a5 := child_d_two c5 d6
    have i4 := child_into_two c4 a5
    omega
  · omega

/-- With the frozen value one, every type and digit is one. -/
theorem patternI_types (hk : 2 ≤ k) (hD : Digits k a d e w) {b : ℕ}
    (h : PatternI w b 1) :
    a (b + 6) = 1 ∧ a (b + 7) = 1 ∧ a (b + 8) = 1 ∧
      d (b + 6) = 1 ∧ d (b + 7) = 1 ∧ d (b + 8) = 1 := by
  obtain ⟨hC, hn⟩ := hD
  have p0 : w b = 1 ∧ w (b + 1) ≤ 0 ∧ w (b + 2) ≤ 0 ∧ w b + w (b + 1) + w (b + 2) = 1 := h 0
  have p1 : w (b + 3) = 1 ∧ w (b + 4) ≤ 0 ∧ w (b + 5) ≤ 0 ∧
      w (b + 3) + w (b + 4) + w (b + 5) = 1 := h 1
  have p2 : w (b + 6) = 1 ∧ w (b + 7) ≤ 0 ∧ w (b + 8) ≤ 0 ∧
      w (b + 6) + w (b + 7) + w (b + 8) = 1 := h 2
  have p3 : w (b + 9) = 1 ∧ w (b + 10) ≤ 0 ∧ w (b + 11) ≤ 0 ∧
      w (b + 9) + w (b + 10) + w (b + 11) = 1 := h 3
  have w3 : w (b + 3) = 1 := p1.1
  have w4 : w (b + 4) = 0 := by omega
  have w6 : w (b + 6) = 1 := p2.1
  have w7 : w (b + 7) = 0 := by omega
  have w8 : w (b + 8) = 0 := by omega
  have n3 : d (b + 3) + e (b + 4) =
      k * w (b + 3) + 2 * w (b + 2) + 2 * w (b + 1) - w (b + 4) := hn (b + 1)
  have n4 : d (b + 4) + e (b + 5) =
      k * w (b + 4) + 2 * w (b + 3) + 2 * w (b + 2) - w (b + 5) := hn (b + 2)
  have n6 : d (b + 6) + e (b + 7) =
      k * w (b + 6) + 2 * w (b + 5) + 2 * w (b + 4) - w (b + 7) := hn (b + 4)
  have n7 : d (b + 7) + e (b + 8) =
      k * w (b + 7) + 2 * w (b + 6) + 2 * w (b + 5) - w (b + 8) := hn (b + 5)
  have n8 : d (b + 8) + e (b + 9) =
      k * w (b + 8) + 2 * w (b + 7) + 2 * w (b + 6) - w (b + 9) := hn (b + 6)
  rw [w3, mul_one] at n3
  rw [w4, mul_zero] at n4
  rw [w6, mul_one] at n6
  rw [w7, mul_zero] at n7
  rw [w8, mul_zero] at n8
  have c2 : Child k (a (b + 2)) (a (b + 3)) (d (b + 3)) (e (b + 3)) := hC (b + 2)
  have c3 : Child k (a (b + 3)) (a (b + 4)) (d (b + 4)) (e (b + 4)) := hC (b + 3)
  have c4 : Child k (a (b + 4)) (a (b + 5)) (d (b + 5)) (e (b + 5)) := hC (b + 4)
  have c5 : Child k (a (b + 5)) (a (b + 6)) (d (b + 6)) (e (b + 6)) := hC (b + 5)
  have c6 : Child k (a (b + 6)) (a (b + 7)) (d (b + 7)) (e (b + 7)) := hC (b + 6)
  have c7 : Child k (a (b + 7)) (a (b + 8)) (d (b + 8)) (e (b + 8)) := hC (b + 7)
  have hk0 : (0 : ℤ) ≤ k := by omega
  have b2 := child_bounds c2 hk0
  have b3 := child_bounds c3 hk0
  have b4 := child_bounds c4 hk0
  have b5 := child_bounds c5 hk0
  have b6 := child_bounds c6 hk0
  have b7 := child_bounds c7 hk0
  have q6 := child_e_eq c6 hk
  have j6 := child_into_two c6
  have u7 := child_of_two c7
  have t5 := child_d_two c5
  have i4 := child_into_two c4
  have z3 := child_d_zero c3
  have v2 := child_into_zero c2
  have s6 := child_e_pos c6
  have s7 := child_e_pos c7
  have hd6 : d (b + 6) = 1 := by omega
  omega

/-- The frozen pattern survives a change of base point. -/
theorem PatternI.shift {b : ℕ} {g : ℤ} (h : PatternI w b g) (j : ℕ) :
    PatternI w (b + 3 * j) g := by
  intro m
  have := h (j + m)
  rwa [show b + 3 * (j + m) = b + 3 * j + 3 * m by ring] at this

end Digits

/-- **The recurrence has one cycle.** Under the real inequality and the
digit relations, the sequence eventually repeats `1, 0, 0`, and every
type and digit is eventually one. -/
theorem eventually_cycle {α : ℝ} {k : ℤ} {a d e w : ℕ → ℤ} (hα : 0 < α)
    (hθ : 2 * α + 2 * α ^ 2 < 1) (hk : 2 ≤ k) (hE : Bounded α w) (hD : Digits k a d e w) :
    ∃ b : ℕ, ∀ j, w (b + 3 * j) = 1 ∧ w (b + 3 * j + 1) = 0 ∧ w (b + 3 * j + 2) = 0 ∧
      a (b + 3 * j) = 1 ∧ a (b + 3 * j + 1) = 1 ∧ a (b + 3 * j + 2) = 1 ∧
      d (b + 3 * j) = 1 ∧ d (b + 3 * j + 1) = 1 ∧ d (b + 3 * j + 2) = 1 := by
  obtain ⟨b₀, ⟨g, hg, h⟩ | ⟨γ, hγ, h⟩⟩ := frozen hα hθ hE
  · have hg1 : g = 1 := patternI_one hk hD hg h
    subst hg1
    refine ⟨b₀ + 6, fun j => ?_⟩
    have hs := h.shift j
    have ht := patternI_types hk hD hs
    have p2 := hs 2
    rw [show b₀ + 6 + 3 * j = b₀ + 3 * j + 6 by ring]
    have q : w (b₀ + 3 * j + 6) = 1 ∧ w (b₀ + 3 * j + 7) ≤ 0 ∧ w (b₀ + 3 * j + 8) ≤ 0 ∧
        w (b₀ + 3 * j + 6) + w (b₀ + 3 * j + 7) + w (b₀ + 3 * j + 8) = 1 := p2
    refine ⟨q.1, ?_, ?_, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2⟩
    · show w (b₀ + 3 * j + 7) = 0
      omega
    · show w (b₀ + 3 * j + 8) = 0
      omega
  · exact (patternII_false hk hD hγ h).elim

/-- Control: the real inequality alone does not force the cycle. At
`α = 1/3` the sequence `1, 1, -1, 1, 1, -1, …` satisfies it at every
index and never takes the value zero. Its window has range four; only
the digit relations exclude it. -/
theorem bounded_alone_insufficient :
    ∃ w : ℕ → ℤ, Bounded (1 / 3) w ∧ ∀ i, w i ≠ 0 := by
  refine ⟨fun i => if i % 3 = 2 then -1 else 1, fun i => ?_, fun i => ?_⟩
  · have h : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h with h | h | h
    · have h1 : (i + 1) % 3 = 1 := by omega
      have h2 : (i + 2) % 3 = 2 := by omega
      simp only [h, h1, h2]
      norm_num
    · have h1 : (i + 1) % 3 = 2 := by omega
      have h2 : (i + 2) % 3 = 0 := by omega
      simp only [h, h1, h2]
      norm_num
    · have h1 : (i + 1) % 3 = 0 := by omega
      have h2 : (i + 2) % 3 = 1 := by omega
      simp only [h, h1, h2]
      norm_num
  · simp only
    split_ifs <;> norm_num

end Psc.ShiftedRadixCycle
