/-
# Theorem FC1 (1), (2): the vertex-set inclusion and the gap bound on the geometric property (F)

`docs/c4-geometric-f-class-2026-11-16.md` §2 (states, the prototile state map `f`, vertex
states, property (F), Lemma 2 `f_{σ^m} = f^m`, Lemma 3 (1), (2), (4)) and §3 (Theorem FC1,
items 1 and 2; the proof steps "Relative states", (E), (C), (Fin), (N), (G)).  The note
records Theorem FC1 as a proof that is not machine-checked; this module and
`PscVerif.GeometricFStrict` (item 3 and the equivalences) check its combinatorial core, in
abstract form, against the repository's definitions.

**Setting.**  `α` is a finite alphabet with decidable equality and `s : α → List α` a
substitution, `σ = Psc.Binomial.subst s`; `τ = σ^m` is the power substitution
`Psc.Binomial.power s m` (`subst (power s m) = σ^m`, `Psc.Binomial.subst_power`).  `M = incZ s`
is `Psc.Incidence.inc s` cast to `ℤ` (the body of `Psc.OccurrenceGraph.incZ`), acting on
`α → ℤ` by `*ᵥ`.  A right-infinite word is `X : ℕ → α`; it is `τ`-fixed when
`Psc.BPrimeBinding.IsFixed (power s m) X` (the image of every prefix is a prefix); its
prefix Parikh vectors are `Psc.BPrimeBinding.prefixParikh X n` and its windows
`Psc.BPrimeBinding.win X t N`.  The tile lengths are an additive functional
`L : (α → ℤ) →+ ℝ` (the note's `v ↦ ℓ·v`).

**Definitions.**
* `pvec w` (`p(w)` in `ℤ`; `pvec_eq_iff`: equal Parikh vectors are `Psc.Binomial.Equiv1`;
  `prefixParikh_eq_pvec`); `incZ` with `pvec_subst`, `pvec_iterate`, `incZ_power`;
* `LengthData s L β`: `β > 0`, `L (M v) = β L v`, `L` positive on letters;
* `IsState L (j, v)`: `0 ≤ ℓ·v < ℓ_j`; `Step s L x y`: `y = f(x)` (a factorisation
  `σ(j) = P j' S` with `y = (j', M v − p(P))` a state); `StepN s L n x y`: `y = fⁿ(x)`;
* `vertexSet X` (`V_X`), `RelState L X' y x` (`x = s(y)`, the tile of `X'` containing the
  point `y` and `y` seen from its left vertex), `relStates L X X'` (`R`);
* `ContractionData s L ν ρ` (a subadditive even `ν` with `ν (M v) ≤ ρ ν v`, `ρ < 1`, proper
  together with `L`), `PropertyF s L` (no `f`-periodic state has `v ≠ 0`).

**Proved here, in full** (`propext`, `Classical.choice`, `Quot.sound` only):
* the state map is a function on states: `step_unique`, `step_total`, `Step.isState`;
  vertex states are forward invariant (`step_vertex`, `stepN_absorb`);
* **Lemma 2** `f_{σ^m} = f^m`: `step_power_succ`, `step_power_iff`;
* **(E)** `relState_step` (one application of a substitution fixing `X'`), `relState_stepN`
  (`s(M^m y) = f^m(s(y))` for a `σ^m`-fixed word), `relState_stepN_mul`;
  `mulVec_prefixParikh` (`M y_n = y_{φ(n)}`);
* **(C)** `relState_vertex_iff` (`y ∈ V_{X'}` iff `s(y)` is a vertex state),
  `prefixParikh_mem_vertexSet_iff` (a common vertex is a common `Equiv1` cut index);
* **(N), Theorem FC1 (1)**: `inclusion_of_bound` (if every relative state reaches a vertex
  state within `N₀` steps then `M^{mN}(V_X ∪ V_{X'}) ⊆ V_X ∩ V_{X'}` for every `N` with
  `N₀ ≤ mN`) and **`inclusion`** (from (Fin) and (F) on `R`, `m ≥ 1`);
* **(G), Theorem FC1 (2)**: **`gap_bound`** (every window `(t, t + β^{mN} ℓ_max]`, `t ≥ 0`,
  holds the position of a common vertex), `cut_gap_bound` (in letters:
  `(k' − k) ℓ_min ≤ β^{mN} ℓ_max`), `syndetic_cuts`; **`fc1_inclusion_gap`** (items 1, 2);
* **(Fin), Lemma 3**: `contractionData_of_eigenfunctionals` (contraction data from finitely
  many additive functionals `η_i` with `η_i (M v) = λ_i η_i (v)`, `|λ_i| ≤ ρ < 1`, proper
  together with `L`), `desubst`, `vertex_bound` (`ν(y) ≤ D_τ / (1 − ρ^m)` on vertices),
  **`relStates_finite_of_contraction`** ((Fin)), `step_bound`, `stepN_bound` (Lemma 3 (1)),
  **`reaches_vertex_of_propertyF`** and `propertyF_of_reaches_vertex` (Lemma 3 (4)), and
  **`fc1_inclusion_gap_of_contraction`** (items 1, 2 from length data, contraction data
  and (F)).

**Hypotheses and where they enter.**  `LengthData`: `β > 0` and the eigen-equation make `f`
total on states and give (E); positivity on letters makes `f` single-valued, the vertex
positions strictly increasing and unbounded (finite alphabet).  `IsFixed (power s m)`: (E)
and `M^m V_X ⊆ V_X`.  `m ≥ 1`: only to pass from a transient bound `N₀` to `N₀ ≤ mN`, and
`ρ^m < 1`.  (Fin) and (F) are hypotheses of `inclusion`; `ContractionData` discharges (Fin)
and, with `PropertyF`, gives "every state reaches a vertex state".

**Deviations from the note**, each a generalisation or a change of presentation:
* `f` and `s` are relations (`Step`, `RelState`) with proved uniqueness and existence,
  not functions with junk values;
* injectivity of `ℓ` on integer vectors (Lemma 1 (1)) is **not assumed**: a vertex state is
  a state with `v = 0`, and (C) needs only that the vertex positions increase strictly.
  Irreducibility of `χ_M` enters only through `ContractionData.proper` (Lemma 1 (2));
* `β > 1` is not used here (it is used in `PscVerif.GeometricFStrict`: the rays exist,
  noncoincidence); the alphabet is any finite type; `ν` is abstract (for PIP3:
  `Σ_i |η_i·v|` over the contracted eigen-coordinates);
* the gap bound is stated for all positions `t ≥ 0`, which contains "consecutive common
  vertices are at `ℓ`-distance at most `β^{mN} ℓ_max`".

**Not proved here.**  That `ContractionData` holds on PIP3 (Lemma 1 (2) and the Pisot bound):
it is a hypothesis in this module; `PscVerif.GeometricFPisot` proves it, with `β > 1`, from
the standing spectral hypotheses.  No PIP3 specimen is shown to satisfy `PropertyF`: all the
hypotheses hold jointly on Thue–Morse (`PscVerif.GeometricFStrict`) and on Fibonacci
(`PscVerif.GeometricFPisot`), neither of which is PIP3.  The explicit bound "`N₀` is less than
the number of states of the box"; Lemma 1 (1), (3), Lemma 4 (interior periodic addresses,
powers, reversal) and Lemma 5; anything about Theorems FC2, P, FC3, N, Fork.  Universal C4 is
open.
-/
import PscVerif.BPrimeBinding
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

namespace Psc.GeometricF

open Matrix Psc.Binomial Psc.Incidence Psc.BPrimeBinding

variable {α : Type*} [DecidableEq α]

/-! ### Integer Parikh vectors -/

/-- The integer Parikh vector `p(w)` of a finite word: `pvec w a = |w|_a`. -/
def pvec (w : List α) : α → ℤ := fun a => (w.count a : ℤ)

@[simp] theorem pvec_nil : pvec ([] : List α) = 0 := by
  funext a; simp [pvec]

theorem pvec_append (u v : List α) : pvec (u ++ v) = pvec u + pvec v := by
  funext a; simp [pvec]

theorem pvec_cons (a : α) (w : List α) : pvec (a :: w) = pvec [a] + pvec w := by
  rw [← pvec_append]; rfl

/-- Equal Parikh vectors are `Psc.Binomial.Equiv1`. -/
theorem pvec_eq_iff {u v : List α} : pvec u = pvec v ↔ Equiv1 u v := by
  constructor
  · intro h a
    have ha := congrFun h a
    change (u.count a : ℤ) = (v.count a : ℤ) at ha
    exact_mod_cast ha
  · intro h
    funext a
    simp only [pvec, h a]

/-- `Psc.BPrimeBinding.prefixParikh X k` is the Parikh vector of the prefix `X[0, k)`. -/
theorem prefixParikh_eq_pvec (X : ℕ → α) (k : ℕ) : prefixParikh X k = pvec (win X 0 k) := by
  funext a; exact prefixParikh_eq_count X k a

omit [DecidableEq α] in
theorem win_zero_add (X : ℕ → α) (a d : ℕ) : win X 0 (a + d) = win X 0 a ++ win X a d := by
  rw [win_add, Nat.zero_add]

theorem prefixParikh_zero (X : ℕ → α) : prefixParikh X 0 = 0 := by
  funext a; simp [prefixParikh]

theorem prefixParikh_succ' (X : ℕ → α) (n : ℕ) :
    prefixParikh X (n + 1) = prefixParikh X n + pvec [X n] := by
  funext a
  show prefixParikh X (n + 1) a = prefixParikh X n a + pvec [X n] a
  rw [prefixParikh_succ]
  by_cases h : X n = a <;> simp [pvec, h]

/-! ### The incidence action on integer vectors -/

section Incidence

variable [Fintype α]

/-- The incidence matrix over `ℤ`: `Psc.Incidence.inc` cast entrywise (the body of
`Psc.OccurrenceGraph.incZ`; over `Fin 3` it is `Psc.OccurrenceTransport.incidenceZ`). -/
abbrev incZ (s : α → List α) : Matrix α α ℤ := (inc s).map (Nat.cast : ℕ → ℤ)

/-- `p(σ w) = M p(w)`. -/
theorem pvec_subst (s : α → List α) (w : List α) : pvec (subst s w) = incZ s *ᵥ pvec w := by
  funext a
  simp [pvec, count_subst, Matrix.mulVec, dotProduct]

theorem incZ_pow (s : α → List α) (k : ℕ) :
    incZ s ^ k = (inc s ^ k).map (Nat.cast : ℕ → ℤ) := by
  have h := map_pow (Nat.castRingHom ℤ).mapMatrix (inc s) k
  simpa [RingHom.mapMatrix_apply] using h.symm

/-- The incidence matrix of the power substitution `Psc.Binomial.power s k` is `Mᵏ`. -/
theorem incZ_power (s : α → List α) (k : ℕ) : incZ (power s k) = incZ s ^ k := by
  rw [incZ_pow]
  ext a c
  simp only [Matrix.map_apply, inc_apply]
  rw [← count_iterate_subst]
  rfl

/-- `p(σᵏ w) = Mᵏ p(w)`. -/
theorem pvec_iterate (s : α → List α) (k : ℕ) (w : List α) :
    pvec ((subst s)^[k] w) = incZ s ^ k *ᵥ pvec w := by
  rw [← subst_power, pvec_subst, incZ_power]

end Incidence

/-! ### The length functional -/

section Length

variable [Fintype α]

/-- **Length data** for a substitution `s`: an additive functional `L` on integer vectors
(the note's `v ↦ ℓ·v`) with `L (M v) = β L v`, `β > 0`, positive on letters. -/
structure LengthData (s : α → List α) (L : (α → ℤ) →+ ℝ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  eigen : ∀ v, L (incZ s *ᵥ v) = β * L v
  pos : ∀ a, 0 < L (pvec [a])

variable {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

theorem LengthData.eigen_pow (h : LengthData s L β) (k : ℕ) (v : α → ℤ) :
    L (incZ s ^ k *ᵥ v) = β ^ k * L v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, ih, h.eigen, pow_succ]
    ring

/-- Length data pass to the power substitution, with `β ^ m`. -/
theorem LengthData.power (h : LengthData s L β) (m : ℕ) : LengthData (power s m) L (β ^ m) :=
  ⟨pow_pos h.beta_pos m, fun v => by rw [incZ_power, h.eigen_pow], h.pos⟩

omit [Fintype α] in
theorem L_pvec_nonneg (hpos : ∀ a, 0 < L (pvec [a])) (w : List α) : 0 ≤ L (pvec w) := by
  induction w with
  | nil => simp
  | cons a w ih => rw [pvec_cons, map_add]; linarith [hpos a]

omit [Fintype α] in
theorem L_pvec_pos (hpos : ∀ a, 0 < L (pvec [a])) {w : List α} (hw : w ≠ []) :
    0 < L (pvec w) := by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hw
  rw [pvec_cons, map_add]
  linarith [hpos a, L_pvec_nonneg hpos t]

omit [Fintype α] in
theorem L_pvec_le {ℓmax : ℝ} (hmax : ∀ a, L (pvec [a]) ≤ ℓmax) (w : List α) :
    L (pvec w) ≤ w.length * ℓmax := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [pvec_cons, map_add, List.length_cons]
    push_cast
    linarith [hmax a]

/-- A substitution with length data is nonerasing. -/
theorem LengthData.nonerasing (hL : LengthData s L β) (a : α) : s a ≠ [] := by
  intro h0
  have h1 := hL.eigen (pvec [a])
  rw [← pvec_subst] at h1
  have h2 : subst s [a] = [] := by simp [subst, h0]
  rw [h2, pvec_nil, map_zero] at h1
  have := mul_pos hL.beta_pos (hL.pos a)
  linarith

end Length

/-! ### States and the prototile state map -/

section States

variable [Fintype α]

/-- A **state** `(j, v)`: a letter `j` and an integer vector `v` with `0 ≤ ℓ·v < ℓ_j`
(the lattice point `v` seen from the left end of a tile of type `j` that contains it). -/
def IsState (L : (α → ℤ) →+ ℝ) (x : α × (α → ℤ)) : Prop :=
  0 ≤ L x.2 ∧ L x.2 < L (pvec [x.1])

/-- **The prototile state map `f`, as a relation**: `Step s L (j, v) (j', v')` iff there is a
factorisation `σ(j) = P j' S` with `v' = M v − p(P)` and `(j', v')` a state, i.e.
`ℓ·p(P) ≤ ℓ·M v < ℓ·p(P) + ℓ_{j'}`.  On states it is a function: `step_unique`,
`step_total`. -/
def Step (s : α → List α) (L : (α → ℤ) →+ ℝ) (x y : α × (α → ℤ)) : Prop :=
  ∃ P S : List α, s x.1 = P ++ y.1 :: S ∧ y.2 = incZ s *ᵥ x.2 - pvec P ∧ IsState L y

/-- `StepN s L n x y`: `y = fⁿ(x)`. -/
def StepN (s : α → List α) (L : (α → ℤ) →+ ℝ) : ℕ → α × (α → ℤ) → α × (α → ℤ) → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, StepN s L n x z ∧ Step s L z y

variable {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

omit [Fintype α] in
/-- The sub-tile of a word that contains a given position is unique. -/
theorem split_unique (hpos : ∀ a, 0 < L (pvec [a])) {P P' S S' : List α} {a a' : α} {t : ℝ}
    (h : P ++ a :: S = P' ++ a' :: S') (h1 : L (pvec P) ≤ t)
    (h2 : t < L (pvec P) + L (pvec [a])) (h1' : L (pvec P') ≤ t)
    (h2' : t < L (pvec P') + L (pvec [a'])) : P = P' ∧ a = a' := by
  have key : P = P' := by
    rcases List.append_eq_append_iff.1 h with ⟨r, hr, hr'⟩ | ⟨r, hr, hr'⟩
    · cases r with
      | nil => simpa using hr.symm
      | cons e r =>
        exfalso
        simp only [List.cons_append, List.cons.injEq] at hr'
        obtain ⟨rfl, -⟩ := hr'
        rw [hr, pvec_append, pvec_cons, map_add, map_add] at h1'
        linarith [L_pvec_nonneg hpos r]
    · cases r with
      | nil => simpa using hr
      | cons e r =>
        exfalso
        simp only [List.cons_append, List.cons.injEq] at hr'
        obtain ⟨rfl, -⟩ := hr'
        rw [hr, pvec_append, pvec_cons, map_add, map_add] at h1
        linarith [L_pvec_nonneg hpos r]
  subst key
  have := List.append_cancel_left h
  simp only [List.cons.injEq] at this
  exact ⟨rfl, this.1⟩

omit [Fintype α] in
/-- Every position of a word lies in a sub-tile. -/
theorem exists_split : ∀ (w : List α) (t : ℝ), 0 ≤ t → t < L (pvec w) →
    ∃ (P : List α) (a : α) (S : List α),
      w = P ++ a :: S ∧ L (pvec P) ≤ t ∧ t < L (pvec P) + L (pvec [a])
  | [], t, h0, ht => by
    simp at ht
    linarith
  | b :: w, t, h0, ht => by
    by_cases hb : t < L (pvec [b])
    · exact ⟨[], b, w, rfl, by simpa using h0, by simpa using hb⟩
    · rw [pvec_cons, map_add] at ht
      obtain ⟨P, a, S, hw, h1, h2⟩ :=
        exists_split w (t - L (pvec [b])) (by linarith) (by linarith)
      refine ⟨b :: P, a, S, by rw [hw]; rfl, ?_, ?_⟩
      · rw [pvec_cons, map_add]; linarith
      · rw [pvec_cons, map_add]; linarith

/-- `f` is single-valued. -/
theorem step_unique (hpos : ∀ a, 0 < L (pvec [a])) {x y y' : α × (α → ℤ)}
    (h : Step s L x y) (h' : Step s L x y') : y = y' := by
  obtain ⟨P, S, hP, hy, hs0, hs1⟩ := h
  obtain ⟨P', S', hP', hy', hs0', hs1'⟩ := h'
  rw [hy, map_sub] at hs0 hs1
  rw [hy', map_sub] at hs0' hs1'
  obtain ⟨rfl, hj⟩ := split_unique hpos (t := L (incZ s *ᵥ x.2)) (hP.symm.trans hP')
    (by linarith) (by linarith) (by linarith) (by linarith)
  exact Prod.ext hj (hy.trans hy'.symm)

/-- `f` is defined on every state (and its values are states by definition). -/
theorem step_total (hL : LengthData s L β) {x : α × (α → ℤ)} (hx : IsState L x) :
    ∃ y, Step s L x y := by
  have h0 : 0 ≤ L (incZ s *ᵥ x.2) := by
    rw [hL.eigen]; exact mul_nonneg hL.beta_pos.le hx.1
  have h1 : L (incZ s *ᵥ x.2) < L (pvec (s x.1)) := by
    have e : pvec (s x.1) = incZ s *ᵥ pvec [x.1] := by
      rw [← pvec_subst]; simp [subst]
    rw [e, hL.eigen, hL.eigen]
    exact mul_lt_mul_of_pos_left hx.2 hL.beta_pos
  obtain ⟨P, a, S, hw, h2, h3⟩ := exists_split (s x.1) _ h0 h1
  refine ⟨(a, incZ s *ᵥ x.2 - pvec P), P, S, hw, rfl, ?_, ?_⟩
  · simp only [map_sub]; linarith
  · simp only [map_sub]; linarith

omit [Fintype α] in
theorem Step.isState {x y : α × (α → ℤ)} [Fintype α] (h : Step s L x y) : IsState L y := by
  obtain ⟨_, _, _, _, hst⟩ := h
  exact hst

/-- **Vertex states are forward invariant**: `f(j, 0) = (g(j), 0)`. -/
theorem step_vertex (hpos : ∀ a, 0 < L (pvec [a])) {x y : α × (α → ℤ)} (h : Step s L x y)
    (hx : x.2 = 0) : y.2 = 0 := by
  obtain ⟨P, S, -, hy, hs0, -⟩ := h
  rw [hx, Matrix.mulVec_zero, zero_sub] at hy
  rw [hy, map_neg] at hs0
  have hP : P = [] := by
    by_contra hne
    linarith [L_pvec_pos hpos hne]
  rw [hy, hP, pvec_nil, neg_zero]

/-! ### Iterates -/

theorem stepN_unique (hpos : ∀ a, 0 < L (pvec [a])) :
    ∀ (n : ℕ) {x y y' : α × (α → ℤ)}, StepN s L n x y → StepN s L n x y' → y = y'
  | 0, _, _, _, h, h' => h.symm.trans h'
  | n + 1, _, _, _, ⟨z, hz, hy⟩, ⟨z', hz', hy'⟩ => by
    have e := stepN_unique hpos n hz hz'
    subst e
    exact step_unique hpos hy hy'

theorem stepN_isState {x : α × (α → ℤ)} (hx : IsState L x) :
    ∀ (n : ℕ) {y : α × (α → ℤ)}, StepN s L n x y → IsState L y
  | 0, _, h => h ▸ hx
  | _ + 1, _, ⟨_, _, hy⟩ => hy.isState

theorem stepN_total (hL : LengthData s L β) {x : α × (α → ℤ)} (hx : IsState L x) :
    ∀ n : ℕ, ∃ y, StepN s L n x y
  | 0 => ⟨x, rfl⟩
  | n + 1 => by
    obtain ⟨z, hz⟩ := stepN_total hL hx n
    obtain ⟨y, hy⟩ := step_total hL (stepN_isState hx n hz)
    exact ⟨y, z, hz, hy⟩

theorem stepN_add {a : ℕ} {x z : α × (α → ℤ)} (h1 : StepN s L a x z) :
    ∀ (b : ℕ) {y : α × (α → ℤ)}, StepN s L b z y → StepN s L (a + b) x y
  | 0, _, h => h ▸ h1
  | b + 1, _, ⟨w, hw, hy⟩ => ⟨w, stepN_add h1 b hw, hy⟩

theorem stepN_split {a : ℕ} {x : α × (α → ℤ)} :
    ∀ (b : ℕ) {y : α × (α → ℤ)}, StepN s L (a + b) x y →
      ∃ z, StepN s L a x z ∧ StepN s L b z y
  | 0, y, h => ⟨y, h, rfl⟩
  | b + 1, _, ⟨w, hw, hy⟩ => by
    obtain ⟨z, hz, hzw⟩ := stepN_split b hw
    exact ⟨z, hz, w, hzw, hy⟩

theorem stepN_vertex (hpos : ∀ a, 0 < L (pvec [a])) {x : α × (α → ℤ)} (hx : x.2 = 0) :
    ∀ (n : ℕ) {y : α × (α → ℤ)}, StepN s L n x y → y.2 = 0
  | 0, _, h => h ▸ hx
  | n + 1, _, ⟨_, hz, hy⟩ => step_vertex hpos hy (stepN_vertex hpos hx n hz)

/-- Once an orbit has reached a vertex state it stays among vertex states. -/
theorem stepN_absorb (hpos : ∀ a, 0 < L (pvec [a])) {n k : ℕ} {x z : α × (α → ℤ)} {a : α}
    (hn : StepN s L n x (a, 0)) (hnk : n ≤ k) (hk : StepN s L k x z) : z.2 = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
  obtain ⟨w, hw, hwz⟩ := stepN_split d hk
  have e := stepN_unique hpos n hn hw
  subst e
  exact stepN_vertex hpos rfl d hwz

/-! ### Lemma 2: `f_{σ^m} = f^m` -/

/-- The composition step of Lemma 2: `f_σ ∘ f_{σ^m} = f_{σ^{m+1}}`. -/
theorem step_power_succ {m : ℕ} {x z w : α × (α → ℤ)} (h1 : Step (power s m) L x z)
    (h2 : Step s L z w) : Step (power s (m + 1)) L x w := by
  obtain ⟨P1, S1, hP1, hz, -⟩ := h1
  obtain ⟨P2, S2, hP2, hw, hst⟩ := h2
  refine ⟨subst s P1 ++ P2, S2 ++ subst s S1, ?_, ?_, hst⟩
  · have e : power s (m + 1) x.1 = subst s (power s m x.1) := by
      show (subst s)^[m + 1] [x.1] = subst s ((subst s)^[m] [x.1])
      rw [Function.iterate_succ_apply']
    rw [e, hP1, subst_append, subst_cons, hP2]
    simp
  · rw [hw, hz, incZ_power, incZ_power, pvec_append, pvec_subst, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, ← pow_succ']
    abel

/-- **Lemma 2**, first half: `fᵐ(x) = y` implies `f_{σ^m}(x) = y`. -/
theorem stepN_to_power {x : α × (α → ℤ)} (hx : IsState L x) :
    ∀ (m : ℕ) {y : α × (α → ℤ)}, StepN s L m x y → Step (power s m) L x y
  | 0, y, h => by
    cases h
    refine ⟨[], [], rfl, ?_, hx⟩
    rw [incZ_power]
    simp
  | m + 1, _, ⟨_, h1, h2⟩ => step_power_succ (stepN_to_power hx m h1) h2

/-- **Lemma 2** (`f_{σ^m} = f^m` on states), second half. -/
theorem power_to_stepN (hL : LengthData s L β) {m : ℕ} {x y : α × (α → ℤ)}
    (hx : IsState L x) (h : Step (power s m) L x y) : StepN s L m x y := by
  obtain ⟨y', hy'⟩ := stepN_total hL hx m
  have e := step_unique hL.pos h (stepN_to_power hx m hy')
  rwa [e]

theorem step_power_iff (hL : LengthData s L β) {m : ℕ} {x y : α × (α → ℤ)}
    (hx : IsState L x) : Step (power s m) L x y ↔ StepN s L m x y :=
  ⟨power_to_stepN hL hx, stepN_to_power hx m⟩

end States

/-! ### Vertices of an infinite word and relative states -/

section Rays

variable [Fintype α]

/-- The **vertex set** `V_X`: the Parikh vectors of the finite prefixes of `X`
(`Psc.BPrimeBinding.prefixParikh`). -/
def vertexSet (X : ℕ → α) : Set (α → ℤ) := Set.range (prefixParikh X)

/-- `RelState L X' y x`: `x = (X'[n], y − y'_n)` is the **relative state** of the point `y`
in the word `X'`: the tile of `X'` that contains `y`, and `y` seen from its left vertex
(`ℓ·y'_n ≤ ℓ·y < ℓ·y'_{n+1}`). -/
def RelState (L : (α → ℤ) →+ ℝ) (X' : ℕ → α) (y : α → ℤ) (x : α × (α → ℤ)) : Prop :=
  ∃ n, x.1 = X' n ∧ x.2 = y - prefixParikh X' n ∧ IsState L x

/-- The set `R` of all relative states of the vertices of `X` in `X'` and of `X'` in `X`. -/
def relStates (L : (α → ℤ) →+ ℝ) (X X' : ℕ → α) : Set (α × (α → ℤ)) :=
  {x | ∃ y ∈ vertexSet X, RelState L X' y x} ∪ {x | ∃ y ∈ vertexSet X', RelState L X y x}

variable {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

omit [Fintype α] in
theorem L_prefixParikh_succ (X : ℕ → α) (n : ℕ) :
    L (prefixParikh X (n + 1)) = L (prefixParikh X n) + L (pvec [X n]) := by
  rw [prefixParikh_succ', map_add]

omit [Fintype α] in
/-- The vertex positions `ℓ·y_n` increase strictly. -/
theorem pos_strictMono (hpos : ∀ a, 0 < L (pvec [a])) (X : ℕ → α) :
    StrictMono fun n => L (prefixParikh X n) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [L_prefixParikh_succ]; linarith [hpos (X n)]

omit [Fintype α] in
theorem L_prefixParikh_nonneg (hpos : ∀ a, 0 < L (pvec [a])) (X : ℕ → α) (n : ℕ) :
    0 ≤ L (prefixParikh X n) := by
  rw [prefixParikh_eq_pvec]; exact L_pvec_nonneg hpos _

/-- A positive lower bound for the tile lengths (finite alphabet). -/
theorem exists_min_len [Nonempty α] (hpos : ∀ a, 0 < L (pvec [a])) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a, δ ≤ L (pvec [a]) := by
  obtain ⟨a₀, h₀⟩ := Finite.exists_min fun a : α => L (pvec [a])
  exact ⟨_, hpos a₀, h₀⟩

omit [Fintype α] in
theorem pos_ge {δ : ℝ} (hδ : ∀ a, δ ≤ L (pvec [a])) (X : ℕ → α) (k d : ℕ) :
    L (prefixParikh X k) + d * δ ≤ L (prefixParikh X (k + d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, L_prefixParikh_succ]
    push_cast
    linarith [hδ (X (k + d))]

/-- Every position `t ≥ 0` lies in exactly one tile of `X`; here: in some tile. -/
theorem exists_tile (hpos : ∀ a, 0 < L (pvec [a])) (X : ℕ → α) {t : ℝ} (ht : 0 ≤ t) :
    ∃ n, L (prefixParikh X n) ≤ t ∧ t < L (prefixParikh X (n + 1)) := by
  have : Nonempty α := ⟨X 0⟩
  obtain ⟨δ, hδ0, hδ⟩ := exists_min_len hpos
  have hex : ∃ n, t < L (prefixParikh X (n + 1)) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t / δ)
    refine ⟨n, ?_⟩
    have h1 := pos_ge hδ X 0 (n + 1)
    rw [prefixParikh_zero, map_zero, Nat.zero_add] at h1
    have h2 : t < n * δ := (div_lt_iff₀ hδ0).1 hn
    push_cast at h1
    linarith
  classical
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hp
  · rw [h0, prefixParikh_zero, map_zero]; exact ht
  · have h3 := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [Nat.sub_add_cancel hp] at h3
    exact not_lt.1 h3

/-- Every point of nonnegative position has a relative state. -/
theorem relState_exists (hpos : ∀ a, 0 < L (pvec [a])) (X' : ℕ → α) {y : α → ℤ}
    (hy : 0 ≤ L y) : ∃ x, RelState L X' y x := by
  obtain ⟨n, h1, h2⟩ := exists_tile hpos X' hy
  rw [L_prefixParikh_succ] at h2
  refine ⟨(X' n, y - prefixParikh X' n), n, rfl, rfl, ?_, ?_⟩
  · simp only [map_sub]; linarith
  · simp only [map_sub]; linarith

omit [Fintype α] in
/-- **(C) Common vertices.**  A point `y` is a vertex of `X'` iff its relative state in `X'`
is a vertex state. -/
theorem relState_vertex_iff (hpos : ∀ a, 0 < L (pvec [a])) {X' : ℕ → α} {y : α → ℤ}
    {x : α × (α → ℤ)} (h : RelState L X' y x) : x.2 = 0 ↔ y ∈ vertexSet X' := by
  obtain ⟨n, hj, hv, hs0, hs1⟩ := h
  constructor
  · intro h0
    exact ⟨n, (sub_eq_zero.1 (hv.symm.trans h0)).symm⟩
  · rintro ⟨k, rfl⟩
    rw [hv, map_sub] at hs0 hs1
    rw [hj] at hs1
    have h5 := L_prefixParikh_succ (L := L) X' n
    have hmono := pos_strictMono hpos X'
    have h1 : n ≤ k := hmono.le_iff_le.1 (by linarith)
    have h2 : k < n + 1 := hmono.lt_iff_lt.1 (by show L _ < L _; linarith)
    have e : k = n := by omega
    rw [hv, e, sub_self]

omit [Fintype α] in
/-- A common vertex is a common cut index: `y_n ∈ V_{X'}` iff the prefixes of length `n` of
`X` and `X'` have equal Parikh vectors. -/
theorem prefixParikh_mem_vertexSet_iff {X X' : ℕ → α} {n : ℕ} :
    prefixParikh X n ∈ vertexSet X' ↔ Equiv1 (win X 0 n) (win X' 0 n) := by
  constructor
  · rintro ⟨k, hk⟩
    rw [prefixParikh_eq_pvec, prefixParikh_eq_pvec, pvec_eq_iff] at hk
    have hlen := hk.length_eq
    simp only [length_win] at hlen
    subst hlen
    exact fun a => (hk a).symm
  · intro h
    exact ⟨n, by rw [prefixParikh_eq_pvec, prefixParikh_eq_pvec, pvec_eq_iff]
                 exact fun a => (h a).symm⟩

/-- `M` maps the vertices of a fixed word to vertices: `M y_n = y_{φ(n)}`. -/
theorem mulVec_prefixParikh {t : α → List α} {X : ℕ → α} (hX : IsFixed t X) (n : ℕ) :
    incZ t *ᵥ prefixParikh X n = prefixParikh X (phi t X n) := by
  rw [prefixParikh_eq_pvec, ← pvec_subst, subst_win_zero hX, ← prefixParikh_eq_pvec]

theorem mulVec_mem_vertexSet {t : α → List α} {X : ℕ → α} (hX : IsFixed t X) {y : α → ℤ}
    (hy : y ∈ vertexSet X) : incZ t *ᵥ y ∈ vertexSet X := by
  obtain ⟨n, rfl⟩ := hy
  exact ⟨_, (mulVec_prefixParikh hX n).symm⟩

/-- **(E) Equivariance**, for one application of a substitution `t` fixing `X'`:
`s(M y) = f(s(y))`. -/
theorem relState_step {t : α → List α} (hL : LengthData t L β) {X' : ℕ → α}
    (hX' : IsFixed t X') {y : α → ℤ} {x : α × (α → ℤ)} (h : RelState L X' y x) :
    ∃ x', Step t L x x' ∧ RelState L X' (incZ t *ᵥ y) x' := by
  obtain ⟨n, hj, hv, hst⟩ := h
  obtain ⟨x', hstep⟩ := step_total hL hst
  refine ⟨x', hstep, ?_⟩
  obtain ⟨P, S, hP, hx', hst'⟩ := hstep
  -- the image of the `n`-th tile, inside `X'`
  have himg : win X' (phi t X' n) (P.length + (1 + S.length)) = P ++ x'.1 :: S := by
    have h := subst_win hX' n 1
    have h1 : win X' n 1 = [X' n] := by simp [win]
    have h2 : subst t [X' n] = P ++ x'.1 :: S := by
      rw [← hj, ← hP]; simp [subst]
    rw [h1, h2] at h
    have hlen : (P ++ x'.1 :: S).length = P.length + (1 + S.length) := by
      simp; omega
    rw [hlen] at h
    exact h.symm
  rw [win_add] at himg
  obtain ⟨hA, hB⟩ := List.append_inj himg (by simp)
  have hletter : X' (phi t X' n + P.length) = x'.1 := by
    have h0 : 0 < (win X' (phi t X' n + P.length) (1 + S.length)).length := by simp
    have h1 := getElem_win X' (phi t X' n + P.length) (1 + S.length) 0 h0
    rw [Nat.add_zero] at h1
    rw [← h1]
    simp [hB]
  have hvec : prefixParikh X' (phi t X' n + P.length) =
      incZ t *ᵥ prefixParikh X' n + pvec P := by
    rw [prefixParikh_eq_pvec, win_add, Nat.zero_add, hA, pvec_append, ← subst_win_zero hX',
      pvec_subst, ← prefixParikh_eq_pvec]
  refine ⟨phi t X' n + P.length, hletter.symm, ?_, hst'⟩
  rw [hx', hv, hvec, Matrix.mulVec_sub]
  abel

/-- **(E) Equivariance**, `τ = σ^m`: `s(M^m y) = f^m(s(y))` for a `σ^m`-fixed word `X'`. -/
theorem relState_stepN (hL : LengthData s L β) {m : ℕ} {X' : ℕ → α}
    (hX' : IsFixed (power s m) X') {y : α → ℤ} {x : α × (α → ℤ)} (h : RelState L X' y x) :
    ∃ x', StepN s L m x x' ∧ RelState L X' (incZ s ^ m *ᵥ y) x' := by
  obtain ⟨x', h1, h2⟩ := relState_step (hL.power m) hX' h
  obtain ⟨_, _, _, hst⟩ := h
  rw [incZ_power] at h2
  exact ⟨x', power_to_stepN hL hst h1, h2⟩

/-- (E) iterated: `s(M^{mN} y) = f^{mN}(s(y))`. -/
theorem relState_stepN_mul (hL : LengthData s L β) {m : ℕ} {X' : ℕ → α}
    (hX' : IsFixed (power s m) X') {y : α → ℤ} {x : α × (α → ℤ)} (h : RelState L X' y x) :
    ∀ N : ℕ, ∃ x', StepN s L (m * N) x x' ∧ RelState L X' (incZ s ^ (m * N) *ᵥ y) x'
  | 0 => ⟨x, rfl, by simpa using h⟩
  | N + 1 => by
    obtain ⟨x₁, h1, h2⟩ := relState_stepN_mul hL hX' h N
    obtain ⟨x₂, h3, h4⟩ := relState_stepN hL hX' h2
    refine ⟨x₂, ?_, ?_⟩
    · rw [Nat.mul_succ]; exact stepN_add h1 m h3
    · rw [Matrix.mulVec_mulVec, ← pow_add, Nat.add_comm, ← Nat.mul_succ] at h4
      exact h4

theorem pow_mulVec_mem_vertexSet {m : ℕ} {X : ℕ → α} (hX : IsFixed (power s m) X)
    {y : α → ℤ} (hy : y ∈ vertexSet X) : ∀ N : ℕ, incZ s ^ (m * N) *ᵥ y ∈ vertexSet X
  | 0 => by simpa using hy
  | N + 1 => by
    have h := mulVec_mem_vertexSet hX (pow_mulVec_mem_vertexSet hX hy N)
    rw [incZ_power, Matrix.mulVec_mulVec, ← pow_add, Nat.add_comm, ← Nat.mul_succ] at h
    exact h

/-! ### Theorem FC1 (1): the inclusion -/

/-- One half of the inclusion: the vertices of `X` are sent into the vertices of `X'`. -/
theorem inclusion_half (hL : LengthData s L β) {m : ℕ} {X X' : ℕ → α}
    (hX' : IsFixed (power s m) X') {N₀ : ℕ}
    (hF : ∀ y ∈ vertexSet X, ∀ x, RelState L X' y x → ∃ n ≤ N₀, ∃ a, StepN s L n x (a, 0))
    {N : ℕ} (hN : N₀ ≤ m * N) {y : α → ℤ} (hy : y ∈ vertexSet X) :
    incZ s ^ (m * N) *ᵥ y ∈ vertexSet X' := by
  have hy0 : 0 ≤ L y := by
    obtain ⟨n, rfl⟩ := hy
    exact L_prefixParikh_nonneg hL.pos X n
  obtain ⟨x, hx⟩ := relState_exists hL.pos X' hy0
  obtain ⟨x', h1, h2⟩ := relState_stepN_mul hL hX' hx N
  obtain ⟨n, hn, a, hna⟩ := hF y hy x hx
  exact (relState_vertex_iff hL.pos h2).1 (stepN_absorb hL.pos hna (hn.trans hN) h1)

/-- **Theorem FC1 (1), uniform form.**  If every relative state reaches a vertex state within
`N₀` applications of `f`, then `M^{mN}(V_X ∪ V_{X'}) ⊆ V_X ∩ V_{X'}` for every `N` with
`N₀ ≤ mN`. -/
theorem inclusion_of_bound (hL : LengthData s L β) {m : ℕ} {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X') {N₀ : ℕ}
    (hF : ∀ x ∈ relStates L X X', ∃ n ≤ N₀, ∃ a, StepN s L n x (a, 0))
    {N : ℕ} (hN : N₀ ≤ m * N) :
    ∀ y ∈ vertexSet X ∪ vertexSet X', incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X' := by
  rintro y (hy | hy)
  · exact ⟨pow_mulVec_mem_vertexSet hX hy N,
      inclusion_half hL hX' (fun y hy x hx => hF x (Or.inl ⟨y, hy, hx⟩)) hN hy⟩
  · exact ⟨inclusion_half hL hX (fun y hy x hx => hF x (Or.inr ⟨y, hy, hx⟩)) hN hy,
      pow_mulVec_mem_vertexSet hX' hy N⟩

/-- **Theorem FC1 (1).**  Let `X`, `X'` be fixed by `σ^m`, `m ≥ 1`.  If (Fin) the set `R` of
relative states is finite and (F) every state of `R` reaches a vertex state under `f`, then
there is `N` with `M^{mN}(V_X ∪ V_{X'}) ⊆ V_X ∩ V_{X'}`. -/
theorem inclusion (hL : LengthData s L β) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    (hFin : (relStates L X X').Finite)
    (hF : ∀ x ∈ relStates L X X', ∃ n a, StepN s L n x (a, 0)) :
    ∃ N, ∀ y ∈ vertexSet X ∪ vertexSet X',
      incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X' := by
  choose! n hn using hF
  obtain ⟨N₀, hN₀⟩ := (hFin.image n).bddAbove
  refine ⟨N₀, inclusion_of_bound hL hX hX' (N₀ := N₀) (fun x hx => ?_) ?_⟩
  · exact ⟨n x, hN₀ ⟨x, hx, rfl⟩, hn x hx⟩
  · exact Nat.le_mul_of_pos_left N₀ hm

/-! ### Theorem FC1 (2): the gap bound -/

/-- **Theorem FC1 (2).**  If `M^{mN} V_X ⊆ V_{X'}`, then every half-open window
`(t, t + β^{mN} ℓ_max]`, `t ≥ 0`, of the length axis contains the position of a common
vertex: consecutive common vertices are at `ℓ`-distance at most `β^{mN} ℓ_max`. -/
theorem gap_bound (hL : LengthData s L β) {m : ℕ} {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) {N : ℕ}
    (hincl : ∀ y ∈ vertexSet X, incZ s ^ (m * N) *ᵥ y ∈ vertexSet X')
    {ℓmax : ℝ} (hmax : ∀ a, L (pvec [a]) ≤ ℓmax) {t : ℝ} (ht : 0 ≤ t) :
    ∃ z ∈ vertexSet X ∩ vertexSet X', t < L z ∧ L z ≤ t + β ^ (m * N) * ℓmax := by
  have hβ : 0 < β ^ (m * N) := pow_pos hL.beta_pos _
  obtain ⟨n, h1, h2⟩ := exists_tile hL.pos X (t := t / β ^ (m * N)) (div_nonneg ht hβ.le)
  have hy : prefixParikh X (n + 1) ∈ vertexSet X := ⟨n + 1, rfl⟩
  refine ⟨incZ s ^ (m * N) *ᵥ prefixParikh X (n + 1),
    ⟨pow_mulVec_mem_vertexSet hX hy N, hincl _ hy⟩, ?_, ?_⟩
  · rw [hL.eigen_pow]
    have := (div_lt_iff₀ hβ).1 h2
    linarith
  · rw [hL.eigen_pow, L_prefixParikh_succ, mul_add]
    have h3 := (le_div_iff₀ hβ).1 h1
    have h4 := mul_le_mul_of_nonneg_left (hmax (X n)) hβ.le
    linarith

/-- **Theorem FC1 (2), in letters**, with explicit constants: after every index `k` there is a
common cut index `k' > k` (equal Parikh vectors of the prefixes of length `k'`) with
`(k' − k) ℓ_min ≤ β^{mN} ℓ_max`. -/
theorem cut_gap_bound (hL : LengthData s L β) {m : ℕ} {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) {N : ℕ}
    (hincl : ∀ y ∈ vertexSet X, incZ s ^ (m * N) *ᵥ y ∈ vertexSet X')
    {δ ℓmax : ℝ} (hδ : ∀ a, δ ≤ L (pvec [a])) (hmax : ∀ a, L (pvec [a]) ≤ ℓmax) (k : ℕ) :
    ∃ k', k < k' ∧ ((k' - k : ℕ) : ℝ) * δ ≤ β ^ (m * N) * ℓmax ∧
      Equiv1 (win X 0 k') (win X' 0 k') := by
  obtain ⟨z, ⟨⟨k', rfl⟩, hz'⟩, h1, h2⟩ :=
    gap_bound hL hX hincl hmax (L_prefixParikh_nonneg hL.pos X k)
  have hlt : k < k' := (pos_strictMono hL.pos X).lt_iff_lt.1 h1
  refine ⟨k', hlt, ?_, prefixParikh_mem_vertexSet_iff.1 hz'⟩
  have h3 := pos_ge hδ X k (k' - k)
  rw [Nat.add_sub_cancel' hlt.le] at h3
  linarith

/-- **Bounded gaps**: the common cut indices of `X` and `X'` are syndetic. -/
theorem syndetic_cuts (hL : LengthData s L β) {m : ℕ} {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) {N : ℕ}
    (hincl : ∀ y ∈ vertexSet X, incZ s ^ (m * N) *ᵥ y ∈ vertexSet X') :
    ∃ G : ℕ, ∀ k, ∃ k', k < k' ∧ k' ≤ k + G ∧ Equiv1 (win X 0 k') (win X' 0 k') := by
  have : Nonempty α := ⟨X 0⟩
  obtain ⟨δ, hδ0, hδ⟩ := exists_min_len hL.pos
  obtain ⟨a₁, h₁⟩ := Finite.exists_max fun a : α => L (pvec [a])
  refine ⟨⌈β ^ (m * N) * L (pvec [a₁]) / δ⌉₊, fun k => ?_⟩
  obtain ⟨k', hlt, hb, he⟩ := cut_gap_bound hL hX hincl hδ h₁ k
  refine ⟨k', hlt, ?_, he⟩
  have h4 : ((k' - k : ℕ) : ℝ) ≤ β ^ (m * N) * L (pvec [a₁]) / δ := (le_div_iff₀ hδ0).2 hb
  have h5 : k' - k ≤ ⌈β ^ (m * N) * L (pvec [a₁]) / δ⌉₊ :=
    Nat.cast_le.1 (h4.trans (Nat.le_ceil _))
  omega

/-- **Theorem FC1, items (1) and (2)**, in abstract form.  Let `X`, `X'` be fixed by `σ^m`,
`m ≥ 1`, let `L` be length data for `σ`, and assume (Fin) the set of relative states is
finite and (F) each of them reaches a vertex state under the prototile state map.  Then
there is `N` such that `M^{mN}(V_X ∪ V_{X'}) ⊆ V_X ∩ V_{X'}`, and every window
`(t, t + β^{mN} ℓ_max]`, `t ≥ 0`, contains the position of a common vertex. -/
theorem fc1_inclusion_gap (hL : LengthData s L β) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    (hFin : (relStates L X X').Finite)
    (hF : ∀ x ∈ relStates L X X', ∃ n a, StepN s L n x (a, 0)) :
    ∃ N, (∀ y ∈ vertexSet X ∪ vertexSet X',
        incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X') ∧
      ∀ ℓmax : ℝ, (∀ a, L (pvec [a]) ≤ ℓmax) → ∀ t : ℝ, 0 ≤ t →
        ∃ z ∈ vertexSet X ∩ vertexSet X', t < L z ∧ L z ≤ t + β ^ (m * N) * ℓmax := by
  obtain ⟨N, hN⟩ := inclusion hL hm hX hX' hFin hF
  exact ⟨N, hN, fun ℓmax hmax t ht =>
    gap_bound hL hX (fun y hy => (hN y (Or.inl hy)).2) hmax ht⟩

end Rays

/-! ### (Fin) from a contraction: Lemma 3 and step (Fin) -/

section Contraction

variable [Fintype α]

/-- **Contraction data** (the Pisot bound): a "stable size" `ν` on integer vectors that is
subadditive, even, contracted by `M` with ratio `ρ < 1`, and proper together with `L`.  For
`σ ∈ PIP3` take `ν v = |η₂·v| + |η₃·v|` (or the max) and `ρ = max (|λ₂|, |λ₃|)`; properness
is Lemma 1 (2) of the note, where irreducibility of `χ_M` enters (`PscVerif.GeometricFPisot`). -/
structure ContractionData (s : α → List α) (L : (α → ℤ) →+ ℝ) (ν : (α → ℤ) → ℝ) (ρ : ℝ) :
    Prop where
  rho_nonneg : 0 ≤ ρ
  rho_lt_one : ρ < 1
  add_le : ∀ v w, ν (v + w) ≤ ν v + ν w
  neg : ∀ v, ν (-v) = ν v
  contract : ∀ v, ν (incZ s *ᵥ v) ≤ ρ * ν v
  proper : ∀ a b : ℝ, {v : α → ℤ | |L v| ≤ a ∧ ν v ≤ b}.Finite

variable {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ} {ν : (α → ℤ) → ℝ} {ρ : ℝ}

/-- **Contraction data from finitely many contracted eigenfunctionals** (the Pisot bound):
additive functionals `η i` with `η i (M v) = λ_i η i (v)`, `|λ_i| ≤ ρ < 1`, which together
with `L` are proper on integer vectors (Lemma 1 (2)), give contraction data with
`ν v = Σ_i |η i (v)|`. -/
theorem contractionData_of_eigenfunctionals {ι : Type*} [Fintype ι]
    (η : ι → (α → ℤ) →+ ℂ) (lam : ι → ℂ) (hη : ∀ i v, η i (incZ s *ᵥ v) = lam i * η i v)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hlam : ∀ i, ‖lam i‖ ≤ ρ)
    (hproper : ∀ a b : ℝ, {v : α → ℤ | |L v| ≤ a ∧ ∑ i, ‖η i v‖ ≤ b}.Finite) :
    ContractionData s L (fun v => ∑ i, ‖η i v‖) ρ where
  rho_nonneg := hρ0
  rho_lt_one := hρ1
  add_le v w := by
    simp only [map_add]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => norm_add_le _ _
  neg v := by simp only [map_neg, norm_neg]
  contract v := by
    simp only [hη, norm_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hlam i) (norm_nonneg _)).trans_eq (by ring)
  proper := hproper

theorem ContractionData.contract_pow (hc : ContractionData s L ν ρ) (k : ℕ) (v : α → ℤ) :
    ν (incZ s ^ k *ᵥ v) ≤ ρ ^ k * ν v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, pow_succ, mul_assoc]
    exact (ih _).trans (mul_le_mul_of_nonneg_left (hc.contract v) (pow_nonneg hc.rho_nonneg k))

omit [Fintype α] in
/-- A uniform bound for `ν` on the Parikh vectors of the prefixes of the images. -/
theorem exists_prefix_bound [Finite α] (ν : (α → ℤ) → ℝ) (t : α → List α) :
    ∃ D : ℝ, ∀ a P, P <+: t a → ν (pvec P) ≤ D := by
  have hfin : (⋃ a : α, {P : List α | P ∈ (t a).inits}).Finite :=
    Set.finite_iUnion fun a => List.finite_toSet (t a).inits
  obtain ⟨D, hD⟩ := (hfin.image fun P => ν (pvec P)).bddAbove
  exact ⟨D, fun a P hP =>
    hD ⟨P, Set.mem_iUnion.2 ⟨a, (List.mem_inits P (t a)).2 hP⟩, rfl⟩⟩

omit [DecidableEq α] [Fintype α] in
theorem phi_succ (t : α → List α) (X : ℕ → α) (n : ℕ) :
    phi t X (n + 1) = phi t X n + (t (X n)).length := by
  have h1 : win X n 1 = [X n] := by simp [win]
  unfold phi
  rw [win_add, Nat.zero_add, h1, subst_append, List.length_append]
  simp [subst]

omit [DecidableEq α] [Fintype α] in
/-- The image of the `n`-th letter of a fixed word, as a window of it. -/
theorem win_phi {t : α → List α} {X : ℕ → α} (hX : IsFixed t X) (n : ℕ) :
    win X (phi t X n) (t (X n)).length = t (X n) := by
  have h := subst_win hX n 1
  have h1 : win X n 1 = [X n] := by simp [win]
  have h2 : subst t [X n] = t (X n) := by simp [subst]
  rw [h1, h2] at h
  exact h.symm

omit [Fintype α] in
theorem le_phi {t : α → List α} (ht : ∀ a, t a ≠ []) (X : ℕ → α) (n : ℕ) : n ≤ phi t X n := by
  have h := Psc.FixedPointLimit.length_le_subst t ht (win X 0 n)
  simpa [phi] using h

omit [Fintype α] in
/-- **Desubstitution** of the prefixes of a fixed word: `X[0, N) = τ(X[0, n)) P` with
`n ≤ N` and `P` a prefix of `τ(X[n])`. -/
theorem desubst {t : α → List α} (ht : ∀ a, t a ≠ []) {X : ℕ → α} (hX : IsFixed t X) (N : ℕ) :
    ∃ n ≤ N, ∃ P, P <+: t (X n) ∧ win X 0 N = subst t (win X 0 n) ++ P := by
  classical
  have h0 : phi t X 0 ≤ N := by simp [phi, subst]
  have hnN : Nat.findGreatest (fun n => phi t X n ≤ N) N ≤ N := Nat.findGreatest_le N
  have hle : phi t X (Nat.findGreatest (fun n => phi t X n ≤ N) N) ≤ N :=
    Nat.findGreatest_spec (P := fun n => phi t X n ≤ N) (Nat.zero_le N) h0
  have hlt : N < phi t X (Nat.findGreatest (fun n => phi t X n ≤ N) N + 1) := by
    rcases Nat.lt_or_ge (Nat.findGreatest (fun n => phi t X n ≤ N) N) N with h | h
    · exact not_le.1 (Nat.findGreatest_is_greatest (P := fun n => phi t X n ≤ N)
        (Nat.lt_succ_self _) h)
    · have e : Nat.findGreatest (fun n => phi t X n ≤ N) N = N := le_antisymm hnN h
      rw [e]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self N) (le_phi ht X (N + 1))
  generalize Nat.findGreatest (fun n => phi t X n ≤ N) N = n at hnN hle hlt
  rw [phi_succ] at hlt
  refine ⟨n, hnN, win X (phi t X n) (N - phi t X n), ?_, ?_⟩
  · have h1 := win_phi hX n
    have h2 := take_win X (phi t X n) (k := N - phi t X n) (N := (t (X n)).length) (by omega)
    rw [h1] at h2
    rw [← h2]
    exact List.take_prefix _ _
  · rw [subst_win_zero hX, ← win_zero_add]
    congr 1
    omega

omit [Fintype α] in
theorem power_nonerasing (hs : ∀ a, s a ≠ []) (m : ℕ) (a : α) : power s m a ≠ [] :=
  Psc.FixedPointLimit.iterate_subst_ne_nil s hs m (by simp)

theorem ContractionData.nonneg (hc : ContractionData s L ν ρ) (v : α → ℤ) : 0 ≤ ν v := by
  have h1 := hc.add_le 0 0
  have h2 := hc.add_le v (-v)
  rw [add_zero] at h1
  rw [add_neg_cancel, hc.neg] at h2
  linarith

/-- **Step (Fin), the claim**: `ν(y) ≤ D_τ / (1 − ρ^m)` for every vertex `y` of a
`σ^m`-fixed word. -/
theorem vertex_bound (hc : ContractionData s L ν ρ) (hs : ∀ a, s a ≠ []) {m : ℕ} (hm : 1 ≤ m)
    {X : ℕ → α} (hX : IsFixed (power s m) X) {D : ℝ}
    (hD : ∀ a P, P <+: power s m a → ν (pvec P) ≤ D) (N : ℕ) :
    ν (prefixParikh X N) ≤ D / (1 - ρ ^ m) := by
  have hr0 : 0 ≤ ρ ^ m := pow_nonneg hc.rho_nonneg m
  have hr1 : ρ ^ m < 1 := pow_lt_one₀ hc.rho_nonneg hc.rho_lt_one (by omega)
  have h1r : 0 < 1 - ρ ^ m := by linarith
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    obtain ⟨n, hn, P, hP, hw⟩ := desubst (power_nonerasing hs m) hX N
    have e : prefixParikh X N = incZ s ^ m *ᵥ prefixParikh X n + pvec P := by
      rw [prefixParikh_eq_pvec, hw, pvec_append, pvec_subst, incZ_power, ← prefixParikh_eq_pvec]
    have h2 : ν (prefixParikh X N) ≤ ρ ^ m * ν (prefixParikh X n) + D := by
      rw [e]
      exact (hc.add_le _ _).trans (add_le_add (hc.contract_pow m _) (hD _ P hP))
    rw [le_div_iff₀ h1r]
    rcases Nat.lt_or_ge n N with h | h
    · have h3 := ih n h
      rw [le_div_iff₀ h1r] at h3
      have a1 := mul_le_mul_of_nonneg_right h2 h1r.le
      have a2 := mul_le_mul_of_nonneg_left h3 hr0
      nlinarith [a1, a2]
    · have e' : n = N := le_antisymm hn h
      subst e'
      nlinarith [h2]

/-- Every relative state of a vertex of `X` in `X'` lies in a fixed bounded box. -/
theorem relState_bound (hc : ContractionData s L ν ρ) (hs : ∀ a, s a ≠ []) {m : ℕ}
    (hm : 1 ≤ m) {X X' : ℕ → α} (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    {D : ℝ} (hD : ∀ a P, P <+: power s m a → ν (pvec P) ≤ D) {ℓmax : ℝ}
    (hmax : ∀ a, L (pvec [a]) ≤ ℓmax) {y : α → ℤ} {x : α × (α → ℤ)} (hy : y ∈ vertexSet X)
    (h : RelState L X' y x) :
    |L x.2| ≤ ℓmax ∧ ν x.2 ≤ D / (1 - ρ ^ m) + D / (1 - ρ ^ m) := by
  obtain ⟨k, rfl⟩ := hy
  obtain ⟨n, -, hv, hs0, hs1⟩ := h
  constructor
  · rw [abs_le]
    constructor <;> linarith [hmax x.1]
  · rw [hv, sub_eq_add_neg]
    refine (hc.add_le _ _).trans (add_le_add (vertex_bound hc hs hm hX hD k) ?_)
    rw [hc.neg]
    exact vertex_bound hc hs hm hX' hD n

/-- **(Fin)** (Theorem FC1, step (Fin); Lemma 3 (2)): under contraction data the set of
relative states of two `σ^m`-fixed words is finite. -/
theorem relStates_finite_of_contraction (hL : LengthData s L β)
    (hc : ContractionData s L ν ρ) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X') :
    (relStates L X X').Finite := by
  obtain ⟨D, hD⟩ := exists_prefix_bound ν (power s m)
  have : Nonempty α := ⟨X 0⟩
  obtain ⟨a₁, h₁⟩ := Finite.exists_max fun a : α => L (pvec [a])
  refine ((Set.finite_univ (α := α)).prod
    (hc.proper (L (pvec [a₁])) (D / (1 - ρ ^ m) + D / (1 - ρ ^ m)))).subset ?_
  rintro x (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
  · exact ⟨Set.mem_univ _, relState_bound hc hL.nonerasing hm hX hX' hD h₁ hy h⟩
  · exact ⟨Set.mem_univ _, relState_bound hc hL.nonerasing hm hX' hX hD h₁ hy h⟩

omit [Fintype α] in
theorem relStates_isState {X X' : ℕ → α} {x : α × (α → ℤ)} (hx : x ∈ relStates L X X') :
    IsState L x := by
  rcases hx with ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h

/-! ### Lemma 3: property (F) and "every state reaches a vertex state" -/

/-- **Lemma 3 (1)**: `ν(f(x)) ≤ ρ ν(x) + D`. -/
theorem step_bound (hc : ContractionData s L ν ρ) {D : ℝ}
    (hD : ∀ a P, P <+: s a → ν (pvec P) ≤ D) {x y : α × (α → ℤ)} (h : Step s L x y) :
    ν y.2 ≤ ρ * ν x.2 + D := by
  obtain ⟨P, S, hP, hy, -⟩ := h
  rw [hy, sub_eq_add_neg]
  refine (hc.add_le _ _).trans (add_le_add (hc.contract _) ?_)
  rw [hc.neg]
  exact hD x.1 P ⟨_, hP.symm⟩

/-- **Lemma 3 (1)**: `ν(fⁿ(x)) ≤ max (ν(x), D / (1 − ρ))`. -/
theorem stepN_bound (hc : ContractionData s L ν ρ) {D : ℝ}
    (hD : ∀ a P, P <+: s a → ν (pvec P) ≤ D) {x : α × (α → ℤ)} :
    ∀ (n : ℕ) {y : α × (α → ℤ)}, StepN s L n x y → ν y.2 ≤ max (ν x.2) (D / (1 - ρ))
  | 0, _, h => h ▸ le_max_left _ _
  | n + 1, y, ⟨z, hz, hy⟩ => by
    have h1 := stepN_bound hc hD n hz
    have h2 := step_bound hc hD hy
    have h1ρ : 0 < 1 - ρ := by linarith [hc.rho_lt_one]
    have h3 : D ≤ max (ν x.2) (D / (1 - ρ)) * (1 - ρ) :=
      (div_le_iff₀ h1ρ).1 (le_max_right _ _)
    have h4 := mul_le_mul_of_nonneg_left h1 hc.rho_nonneg
    nlinarith [h2, h3, h4]

/-- **Property (F)** of the note, §2: no `f`-periodic state has `v ≠ 0`. -/
def PropertyF (s : α → List α) (L : (α → ℤ) →+ ℝ) : Prop :=
  ∀ x, IsState L x → ∀ k, 1 ≤ k → StepN s L k x x → x.2 = 0

/-- **Lemma 3 (4)**, forward: under contraction data, (F) implies that every state reaches
a vertex state under iteration of `f`. -/
theorem reaches_vertex_of_propertyF (hL : LengthData s L β) (hc : ContractionData s L ν ρ)
    (hF : PropertyF s L) {x : α × (α → ℤ)} (hx : IsState L x) :
    ∃ n a, StepN s L n x (a, 0) := by
  obtain ⟨D, hD⟩ := exists_prefix_bound ν s
  choose orb horb using stepN_total hL hx
  have : Nonempty α := ⟨x.1⟩
  obtain ⟨a₁, h₁⟩ := Finite.exists_max fun a : α => L (pvec [a])
  have hfin := (Set.finite_univ (α := α)).prod
    (hc.proper (L (pvec [a₁])) (max (ν x.2) (D / (1 - ρ))))
  have hmem : ∀ n, orb n ∈ (Set.univ : Set α) ×ˢ
      {v : α → ℤ | |L v| ≤ L (pvec [a₁]) ∧ ν v ≤ max (ν x.2) (D / (1 - ρ))} := by
    intro n
    have hst := stepN_isState hx n (horb n)
    refine ⟨Set.mem_univ _, ?_, stepN_bound hc hD n (horb n)⟩
    rw [abs_le]
    constructor <;> linarith [hst.1, hst.2, h₁ (orb n).1]
  obtain ⟨i, j, hij, he⟩ := hfin.exists_lt_map_eq_of_forall_mem hmem
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  rw [Nat.add_assoc] at he
  obtain ⟨z, hz, hzj⟩ := stepN_split (d + 1) (horb (i + (d + 1)))
  have ez := stepN_unique hL.pos i hz (horb i)
  rw [ez, ← he] at hzj
  have h0 := hF (orb i) (stepN_isState hx i (horb i)) (d + 1) (by omega) hzj
  refine ⟨i, (orb i).1, ?_⟩
  have e : ((orb i).1, (0 : α → ℤ)) = orb i := Prod.ext rfl h0.symm
  rw [e]
  exact horb i

omit [Fintype α] in
/-- **Lemma 3 (4)**, converse: if every state reaches a vertex state, (F) holds. -/
theorem propertyF_of_reaches_vertex [Fintype α] (hpos : ∀ a, 0 < L (pvec [a]))
    (h : ∀ x, IsState L x → ∃ n a, StepN s L n x (a, 0)) : PropertyF s L := by
  intro x hx k hk hper
  obtain ⟨n, a, hn⟩ := h x hx
  have hmul : ∀ j, StepN s L (k * j) x x := by
    intro j
    induction j with
    | zero => exact rfl
    | succ j ih => rw [Nat.mul_succ]; exact stepN_add ih k hper
  exact stepN_absorb hpos hn (Nat.le_mul_of_pos_left n hk) (hmul n)

/-- **Theorem FC1, items (1) and (2), with (Fin) discharged and (F) in the note's form.**
Length data, contraction data (the Pisot bound and Lemma 1 (2)) and property (F): for any two
`σ^m`-fixed words, `m ≥ 1`, there is `N` with `M^{mN}(V_X ∪ V_{X'}) ⊆ V_X ∩ V_{X'}`, and the
common vertices have gaps at most `β^{mN} ℓ_max`. -/
theorem fc1_inclusion_gap_of_contraction (hL : LengthData s L β)
    (hc : ContractionData s L ν ρ) (hF : PropertyF s L) {m : ℕ} (hm : 1 ≤ m) {X X' : ℕ → α}
    (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X') :
    ∃ N, (∀ y ∈ vertexSet X ∪ vertexSet X',
        incZ s ^ (m * N) *ᵥ y ∈ vertexSet X ∩ vertexSet X') ∧
      ∀ ℓmax : ℝ, (∀ a, L (pvec [a]) ≤ ℓmax) → ∀ t : ℝ, 0 ≤ t →
        ∃ z ∈ vertexSet X ∩ vertexSet X', t < L z ∧ L z ≤ t + β ^ (m * N) * ℓmax :=
  fc1_inclusion_gap hL hm hX hX' (relStates_finite_of_contraction hL hc hm hX hX')
    fun _ hx => reaches_vertex_of_propertyF hL hc hF (relStates_isState hx)

end Contraction

end Psc.GeometricF
