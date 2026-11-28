import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Option
import Mathlib.Order.Preorder.Finite
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Factor complexity of one-sided infinite words

For `u : ℕ → α`, `block u i n` is the length-`n` factor at position `i`,
`Factors u n` the set of length-`n` factors and `complexity u n` its cardinality.
This is the complexity function `p_u(n)` of Adamczewski–Bugeaud (ETDS 2007).

Proved here:

* `eventuallyPeriodic_of_complexity_succ_le` (Morse–Hedlund, the direction used):
  if `p(n+1) ≤ p(n)` for one `n`, the word is eventually periodic;
* `succ_le_complexity`: a word that is not eventually periodic has `p(n) ≥ n + 1`,
  so its complexity is unbounded;
* `complexity_comp` / `EventuallyPeriodic.of_comp`: an injective letter-to-letter
  coding preserves complexity and reflects eventual periodicity;
* `window_flatten`: a factor of `w₀ w₁ ⋯ w_r` of length at most the length of every
  `w_t` lies in some `w_t w_{t+1}`, starting inside `w_t`.

Finiteness of the factor sets is an explicit hypothesis where the alphabet is not
finite, so that bounded `ℕ`-valued digit streams are covered.
Source decision: `docs/beta-numeration-research-route-2026-11-27.md`.
-/

set_option autoImplicit false

namespace Psc.WordComplexity

variable {α β : Type*}

/-- The length-`n` factor of `u` at position `i`. -/
def block (u : ℕ → α) (i n : ℕ) : List α := (List.range n).map fun j => u (i + j)

/-- The length-`n` factors of `u`. -/
def Factors (u : ℕ → α) (n : ℕ) : Set (List α) := Set.range fun i => block u i n

/-- The factor complexity `p_u(n)`. -/
noncomputable def complexity (u : ℕ → α) (n : ℕ) : ℕ := (Factors u n).ncard

/-- `u` is eventually periodic. -/
def EventuallyPeriodic (u : ℕ → α) : Prop :=
  ∃ q p : ℕ, 0 < p ∧ ∀ n, q ≤ n → u (n + p) = u n

@[simp] theorem length_block (u : ℕ → α) (i n : ℕ) : (block u i n).length = n := by
  simp [block]

@[simp] theorem getElem_block (u : ℕ → α) (i n j : ℕ) (h : j < (block u i n).length) :
    (block u i n)[j] = u (i + j) := by
  simp [block]

theorem block_mem (u : ℕ → α) (i n : ℕ) : block u i n ∈ Factors u n := ⟨i, rfl⟩

theorem block_succ (u : ℕ → α) (i n : ℕ) :
    block u i (n + 1) = block u i n ++ [u (i + n)] := by
  simp [block, List.range_succ]

theorem take_block (u : ℕ → α) (i n : ℕ) : (block u i (n + 1)).take n = block u i n := by
  rw [block_succ, List.take_append_of_le_length (by simp)]
  simp

theorem drop_one_block (u : ℕ → α) (i n : ℕ) :
    (block u i (n + 1)).drop 1 = block u (i + 1) n := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_drop, getElem_block]
  congr 1
  omega

theorem block_eq_ofFn (u : ℕ → α) (i n : ℕ) :
    block u i n = List.ofFn fun j : Fin n => u (i + j) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp

theorem factors_finite [Finite α] (u : ℕ → α) (n : ℕ) : (Factors u n).Finite := by
  refine (Set.finite_range fun f : Fin n → α => List.ofFn f).subset ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨fun j => u (i + j), (block_eq_ofFn u i n).symm⟩

/-! ## Coding by a letter map -/

theorem block_comp (f : α → β) (u : ℕ → α) (i n : ℕ) :
    block (f ∘ u) i n = (block u i n).map f := by
  simp [block, List.map_map, Function.comp_def]

theorem factors_comp (f : α → β) (u : ℕ → α) (n : ℕ) :
    Factors (f ∘ u) n = List.map f '' Factors u n := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨block u i n, block_mem u i n, (block_comp f u i n).symm⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, block_comp f u i n⟩

theorem complexity_comp {f : α → β} (hf : Function.Injective f) (u : ℕ → α) (n : ℕ) :
    complexity (f ∘ u) n = complexity u n := by
  unfold complexity
  rw [factors_comp]
  exact Set.ncard_image_of_injective _ (List.map_injective_iff.mpr hf)

theorem factors_finite_comp (f : α → β) {u : ℕ → α} {n : ℕ} (h : (Factors u n).Finite) :
    (Factors (f ∘ u) n).Finite := by
  rw [factors_comp]
  exact h.image _

theorem EventuallyPeriodic.of_comp {f : α → β} (hf : Function.Injective f) {u : ℕ → α}
    (h : EventuallyPeriodic (f ∘ u)) : EventuallyPeriodic u := by
  obtain ⟨q, p, hp, hu⟩ := h
  exact ⟨q, p, hp, fun n hn => hf (hu n hn)⟩

/-- A stream of naturals bounded by `m` has finitely many factors of each length. -/
theorem factors_finite_of_bounded {d : ℕ → ℕ} {m : ℕ} (hd : ∀ n, d n ≤ m) (n : ℕ) :
    (Factors d n).Finite := by
  have : d = (fun x : Fin (m + 1) => (x : ℕ)) ∘ fun k => ⟨d k, Nat.lt_succ_of_le (hd k)⟩ := by
    funext k; rfl
  rw [this]
  exact factors_finite_comp _ (factors_finite _ n)

/-! ## Morse–Hedlund -/

theorem image_take_factors (u : ℕ → α) (n : ℕ) :
    (fun w : List α => w.take n) '' Factors u (n + 1) = Factors u n := by
  ext w
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (take_block u i n).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨block u i (n + 1), block_mem u i (n + 1), take_block u i n⟩

theorem complexity_le_succ (u : ℕ → α) (n : ℕ) (hfin : (Factors u (n + 1)).Finite) :
    complexity u n ≤ complexity u (n + 1) := by
  unfold complexity
  rw [← image_take_factors u n]
  exact Set.ncard_image_le hfin

/-- **Morse–Hedlund** (the direction used): equal consecutive complexities force
eventual periodicity. -/
theorem eventuallyPeriodic_of_complexity_succ_le (u : ℕ → α) (n : ℕ)
    (hfin : (Factors u n).Finite) (hfin' : (Factors u (n + 1)).Finite)
    (hle : complexity u (n + 1) ≤ complexity u n) : EventuallyPeriodic u := by
  have heq : ((fun w : List α => w.take n) '' Factors u (n + 1)).ncard =
      (Factors u (n + 1)).ncard := by
    rw [image_take_factors]
    exact le_antisymm (complexity_le_succ u n hfin') hle
  have hinj := Set.injOn_of_ncard_image_eq heq hfin'
  -- Equal length-`n` windows have equal length-`(n+1)` windows.
  have hext : ∀ i j, block u i n = block u j n → block u i (n + 1) = block u j (n + 1) := by
    intro i j h
    exact hinj (block_mem u i (n + 1)) (block_mem u j (n + 1))
      (by simp only [take_block]; exact h)
  obtain ⟨a, b, hab, hwin⟩ :=
    hfin.exists_lt_map_eq_of_forall_mem (f := fun i => block u i n) (fun i => block_mem u i n)
  have hall : ∀ t, block u (a + t) (n + 1) = block u (b + t) (n + 1) := by
    intro t
    induction t with
    | zero => exact hext _ _ hwin
    | succ t ih =>
      apply hext
      have h1 := congrArg (fun w : List α => w.drop 1) ih
      simp only [drop_one_block] at h1
      simpa [Nat.add_assoc] using h1
  refine ⟨a, b - a, by omega, fun N hN => ?_⟩
  have e1 : (block u (a + (N - a)) (n + 1))[0]? = some (u N) := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp only [getElem_block]
    congr 2
    omega
  have e2 : (block u (b + (N - a)) (n + 1))[0]? = some (u (N + (b - a))) := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp only [getElem_block]
    congr 2
    omega
  have h' := congrArg (fun w : List α => w[0]?) (hall (N - a))
  rw [e1, e2] at h'
  exact (Option.some.inj h').symm

/-- A word that is not eventually periodic has complexity at least `n + 1`. -/
theorem succ_le_complexity (u : ℕ → α) (hfin : ∀ n, (Factors u n).Finite)
    (hper : ¬ EventuallyPeriodic u) (n : ℕ) : n + 1 ≤ complexity u n := by
  induction n with
  | zero =>
    have : Factors u 0 = {[]} := by
      ext w
      constructor
      · rintro ⟨i, rfl⟩; simp [block]
      · rintro rfl; exact ⟨0, by simp [block]⟩
    simp [complexity, this]
  | succ n ih =>
    by_contra h
    exact hper (eventuallyPeriodic_of_complexity_succ_le u n (hfin n) (hfin (n + 1)) (by omega))

/-! ## Windows of a concatenation -/

/-- A short window of `w₀ w₁ ⋯` lies in `w_t w_{t+1}` (or `w_t` alone at the end),
starting inside `w_t`. -/
theorem window_flatten (L : List (List α)) (n : ℕ) (hL : ∀ w ∈ L, n ≤ w.length) :
    ∀ p, p < L.flatten.length →
      ∃ w ∈ L, ∃ w' : List α, (w' ∈ L ∨ w' = []) ∧ ∃ o < w.length,
        (L.flatten.drop p).take n = ((w ++ w').drop o).take n := by
  induction L with
  | nil => intro p hp; simp at hp
  | cons w L ih =>
    intro p hp
    by_cases hpw : p < w.length
    · refine ⟨w, List.mem_cons_self .., L.headD [], ?_, p, hpw, ?_⟩
      · cases L with
        | nil => exact Or.inr rfl
        | cons w1 L' => exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [List.flatten_cons, List.drop_append_of_le_length hpw.le,
          List.drop_append_of_le_length hpw.le, List.take_append, List.take_append]
        congr 1
        cases L with
        | nil => simp
        | cons w1 L' =>
          simp only [List.flatten_cons, List.headD_cons]
          have hw1 : n ≤ w1.length := hL w1 (List.mem_cons_of_mem _ List.mem_cons_self)
          rw [List.take_append_of_le_length (by omega)]
    · have hp' : p - w.length < L.flatten.length := by
        simp only [List.flatten_cons, List.length_append] at hp
        omega
      obtain ⟨v, hv, v', hv', o, ho, h⟩ :=
        ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) (p - w.length) hp'
      refine ⟨v, List.mem_cons_of_mem _ hv, v', ?_, o, ho, ?_⟩
      · rcases hv' with hv' | hv'
        · exact Or.inl (List.mem_cons_of_mem _ hv')
        · exact Or.inr hv'
      · rw [List.flatten_cons, List.drop_append,
          List.drop_eq_nil_of_le (by omega), List.nil_append]
        exact h

end Psc.WordComplexity
