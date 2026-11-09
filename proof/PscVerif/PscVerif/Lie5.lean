/-
# The degree-five shuffle annihilator on three letters

The certificate identities are computed over integers. The reconstruction
theorem interprets them over the rationals and divides by their denominators.
-/
import PscVerif.Lie5Data
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Psc.Lie5

open scoped BigOperators

def wordIndex (w : Word5) : Nat :=
  81 * w.1.val + 27 * w.2.1.val + 9 * w.2.2.1.val +
    3 * w.2.2.2.1.val + w.2.2.2.2.val

def wordOfList (w : List (Fin 3)) : Word5 :=
  ⟨w[0]?.getD 0, w[1]?.getD 0, w[2]?.getD 0, w[3]?.getD 0, w[4]?.getD 0⟩

private def Bracket.expand : Bracket → List (List (Fin 3) × ℤ)
  | .letter a => [([a], 1)]
  | .comm u v =>
      u.expand.flatMap fun (x, c) =>
        v.expand.flatMap fun (y, d) => [(x ++ y, c * d), (y ++ x, -(c * d))]

private def Bracket.leaves : Bracket → List (Fin 3)
  | .letter a => [a]
  | .comm u v => u.leaves ++ v.leaves

private def isLyndon (w : List (Fin 3)) : Bool :=
  !w.isEmpty && (List.range (w.length - 1)).all (fun n => w.lex (w.drop (n + 1)))

private def Bracket.isStandard : Bracket → Bool
  | .letter _ => true
  | .comm u v =>
      let w := u.leaves ++ v.leaves
      u.isStandard && v.isStandard && isLyndon w &&
        (List.range (u.leaves.length - 1)).all (fun n => !(isLyndon (w.drop (n + 1))))

private def wordsOfLength : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => (List.finRange 3).flatMap fun a => (wordsOfLength n).map (a :: ·)

/-- The list contains exactly the ternary Lyndon words of length five, and
every commutator uses its longest proper Lyndon suffix. -/
theorem lyndonTrees_checked :
    lyndonTrees.size = 48 ∧
      lyndonTrees.toList.map Bracket.leaves = (wordsOfLength 5).filter isLyndon ∧
      lyndonTrees.toList.all Bracket.isStandard = true := by
  decide +kernel

def bracket5 (i : Fin 48) : Sparse :=
  ((lyndonTrees[i.val]?.getD (.letter 0)).expand).map fun (w, c) => (wordOfList w, c)

def shuffle5 (r : ShuffleRow) : Sparse :=
  let ⟨a, b, c, d, e⟩ := r.2
  let words : List Word5 :=
    if r.1 then
      [⟨a,b,c,d,e⟩, ⟨a,c,b,d,e⟩, ⟨a,c,d,b,e⟩, ⟨a,c,d,e,b⟩,
       ⟨c,a,b,d,e⟩, ⟨c,a,d,b,e⟩, ⟨c,a,d,e,b⟩,
       ⟨c,d,a,b,e⟩, ⟨c,d,a,e,b⟩, ⟨c,d,e,a,b⟩]
    else [⟨a,b,c,d,e⟩, ⟨b,a,c,d,e⟩, ⟨b,c,a,d,e⟩, ⟨b,c,d,a,e⟩, ⟨b,c,d,e,a⟩]
  words.map fun w => (w, 1)

def coeff (row : Sparse) (w : Word5) : ℤ :=
  ((row.filter fun t => t.1 == w).map Prod.snd).sum

private def extract (i : Fin 48) : Sparse := extractRows[i.val]?.getD []

/-- Linear evaluation of the integral row against a tensor. -/
def eval {R : Type*} [CommRing R] (row : Sparse) (f : Word5 → R) : R :=
  (row.map fun (w, c) => (c : R) * f w).sum

theorem eval_cons {R : Type*} [CommRing R] (w : Word5) (c : ℤ) (x : Sparse)
    (f : Word5 → R) : eval ((w,c) :: x) f = (c : R) * f w + eval x f := rfl

theorem eval_singleton {R : Type*} [CommRing R] (w : Word5) (c : ℤ)
    (f : Word5 → R) : eval [(w,c)] f = (c : R) * f w := by simp [eval]

private def scale (k : ℤ) (row : Sparse) : Sparse :=
  row.map fun (w, c) => (w, k * c)

theorem eval_append {R : Type*} [CommRing R] (x y : Sparse) (f : Word5 → R) :
    eval (x ++ y) f = eval x f + eval y f := by simp [eval]

theorem eval_scale {R : Type*} [CommRing R] (k : ℤ) (x : Sparse) (f : Word5 → R) :
    eval (scale k x) f = (k : R) * eval x f := by
  induction x with
  | nil => simp [scale, eval]
  | cons p x ih =>
    rcases p with ⟨w,c⟩
    simp only [scale, List.map_cons, eval, List.sum_cons, Int.cast_mul] at ih ⊢
    rw [ih, mul_add, mul_assoc]

private def insertTerm (t : Word5 × ℤ) : Sparse → Sparse
  | [] => if t.2 = 0 then [] else [t]
  | u :: us =>
      if t.2 = 0 then u :: us
      else if t.1 = u.1 then
        if t.2 + u.2 = 0 then us else (t.1, t.2 + u.2) :: us
      else if wordIndex t.1 < wordIndex u.1 then t :: u :: us
      else u :: insertTerm t us

private def normal (x : Sparse) : Sparse := x.foldr insertTerm []

theorem eval_insert {R : Type*} [CommRing R] (t : Word5 × ℤ) (x : Sparse)
    (f : Word5 → R) : eval (insertTerm t x) f = eval [t] f + eval x f := by
  rcases t with ⟨w,c⟩
  induction x with
  | nil =>
      by_cases h : c = 0 <;> simp [insertTerm, eval, h]
  | cons u us ih =>
      rcases u with ⟨v,d⟩
      simp only [insertTerm]
      split_ifs with hc hw hs hl
      · simp [eval, hc]
      · subst v
        have hh : (c : R) + (d : R) = 0 := by
          rw [← Int.cast_add, hs, Int.cast_zero]
        simp only [eval, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero]
        rw [← add_assoc, ← add_mul, hh, zero_mul, zero_add]
      · subst v
        simp only [eval, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero,
          Int.cast_add]
        ring
      · simp [eval]
      · simp only [eval_singleton] at ih
        simp only [eval_cons]
        rw [ih, show eval [] f = 0 by rfl, add_zero]
        ring

theorem eval_normal {R : Type*} [CommRing R] (x : Sparse) (f : Word5 → R) :
    eval (normal x) f = eval x f := by
  induction x with
  | nil => rfl
  | cons t x ih =>
    change eval (insertTerm t (normal x)) f = eval (t :: x) f
    rw [eval_insert, ih]
    simp [eval]

theorem eval_eq_of_normal {R : Type*} [CommRing R] {x y : Sparse}
    (h : normal x = normal y) (f : Word5 → R) : eval x f = eval y f := by
  rw [← eval_normal x f, ← eval_normal y f, h]

theorem eval_flatMap {ι R : Type*} [CommRing R] (is : List ι) (rows : ι → Sparse)
    (f : Word5 → R) :
    eval (is.flatMap rows) f = (is.map fun i => eval (rows i) f).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.flatMap_cons, eval_append, ih, List.map_cons, List.sum_cons]

private def reconstruction (w : Word5) : Sparse :=
  (List.finRange 48).flatMap fun i => scale (coeff (bracket5 i) w) (extract i)

private def residual (w : Word5) : Sparse := (w, 1) :: scale (-1) (reconstruction w)

private def witness (w : Word5) : ℕ × List (ShuffleRow × ℤ) :=
  shuffleWitnesses[wordIndex w]?.getD (0, [])

private def rhs (w : Word5) : Sparse :=
  (witness w).2.flatMap fun (r, c) => scale c (shuffle5 r)

private def Checks (w : Word5) : Prop :=
  (witness w).1 ≠ 0 ∧ normal (scale (witness w).1 (residual w)) = normal (rhs w)

private instance (w : Word5) : Decidable (Checks w) := by unfold Checks; infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checks (w : Word5) : Checks w := by
  rcases w with ⟨a,b,c,d,e⟩
  revert c d e
  fin_cases a <;> fin_cases b <;> decide +kernel

abbrev Vec5 := Word5 → ℚ

def lyndon5 (i : Fin 48) : Vec5 := fun w => coeff (bracket5 i) w

def ShuffleAnnih5 (f : Vec5) : Prop := ∀ r, eval (shuffle5 r) f = 0

theorem eq_sum_lyndon5 {f : Vec5} (h : ShuffleAnnih5 f) :
    f = ∑ i, eval (extract i) f • lyndon5 i := by
  funext w
  have hEq := eval_eq_of_normal (checks w).2 f
  have hz (r : ShuffleRow × ℤ) : eval (scale r.2 (shuffle5 r.1)) f = 0 := by
    rw [eval_scale, h, mul_zero]
  have hrhs : eval (rhs w) f = 0 := by
    unfold rhs
    rw [eval_flatMap]
    have hm : ((witness w).2.map fun r => eval (scale r.2 (shuffle5 r.1)) f) =
        (witness w).2.map (fun _ => (0 : ℚ)) :=
      List.map_congr_left fun r _ => hz r
    rw [hm]
    simp
  rw [eval_scale, hrhs, Int.cast_natCast] at hEq
  have hn : (((witness w).1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (checks w).1
  have hres : eval (residual w) f = 0 := (mul_eq_zero.mp hEq).resolve_left hn
  have hr : eval (residual w) f = f w - eval (reconstruction w) f := by
    rw [residual, eval_cons, eval_scale]
    push_cast
    ring
  rw [hr, sub_eq_zero] at hres
  rw [hres]
  simp only [reconstruction, eval_flatMap, eval_scale, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, lyndon5]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem eval_coeff_cast (row column : Sparse) :
    eval row (fun w => (coeff column w : ℚ)) =
      (eval row (fun w => coeff column w) : ℤ) := by
  induction row with
  | nil => simp [eval]
  | cons t row ih =>
    rcases t with ⟨w, c⟩
    simp only [eval, List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul] at ih ⊢
    simpa using ih

private def annihRows (column : Sparse) (a : Fin 3) : Bool :=
  [false, true].all fun tag =>
    (List.finRange 3).all fun b => (List.finRange 3).all fun c =>
      (List.finRange 3).all fun d => (List.finRange 3).all fun e =>
        eval (shuffle5 (tag, ⟨a,b,c,d,e⟩)) (fun w => coeff column w) == (0 : ℤ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem annihRows_checked (i : Fin 48) (a : Fin 3) :
    annihRows (bracket5 i) a = true := by
  fin_cases i <;> fin_cases a <;> decide +kernel

theorem lyndon5_annih (i : Fin 48) : ShuffleAnnih5 (lyndon5 i) := by
  rintro ⟨tag,a,b,c,d,e⟩
  have h := annihRows_checked i a
  simp only [annihRows, List.all_eq_true, beq_iff_eq] at h
  exact (eval_coeff_cast _ _).trans (by
    exact_mod_cast h tag (by cases tag <;> simp) b (by simp) c (by simp) d (by simp) e (by simp))

private def ExtractCheck (i : Fin 48) : Prop :=
  ∀ j : Fin 48, eval (extract i) (fun w => coeff (bracket5 j) w) =
    if i = j then (1 : ℤ) else 0

private instance (i : Fin 48) : Decidable (ExtractCheck i) := by
  unfold ExtractCheck
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem extractCheck (i : Fin 48) : ExtractCheck i := by
  fin_cases i <;> decide +kernel

theorem eval_add (row : Sparse) (f g : Vec5) :
    eval row (f + g) = eval row f + eval row g := by
  induction row with
  | nil => simp [eval]
  | cons t row ih =>
    rcases t with ⟨w,c⟩
    simp only [eval, List.map_cons, List.sum_cons, Pi.add_apply] at ih ⊢
    rw [ih]
    ring

theorem eval_smul (row : Sparse) (c : ℚ) (f : Vec5) :
    eval row (c • f) = c * eval row f := by
  induction row with
  | nil => simp [eval]
  | cons t row ih =>
    rcases t with ⟨w,d⟩
    simp only [eval, List.map_cons, List.sum_cons, Pi.smul_apply, smul_eq_mul] at ih ⊢
    rw [ih]
    ring

theorem eval_zero (row : Sparse) : eval row (0 : Vec5) = 0 := by simp [eval]

private def evalLinear (row : Sparse) : Vec5 →ₗ[ℚ] ℚ where
  toFun := eval row
  map_add' := eval_add row
  map_smul' := eval_smul row

theorem linearIndependent_lyndon5 : LinearIndependent ℚ lyndon5 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (evalLinear (extract i)) hg
  have hc (j : Fin 48) : evalLinear (extract i) (lyndon5 j) = if j = i then 1 else 0 := by
    change eval (extract i) (fun w => (coeff (bracket5 j) w : ℚ)) = _
    rw [eval_coeff_cast, extractCheck i j]
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, Ne.symm hji]
  simpa [map_sum, map_smul, hc, smul_eq_mul, mul_ite] using h

def shuffleAnnih5Space : Submodule ℚ Vec5 where
  carrier := {f | ShuffleAnnih5 f}
  zero_mem' := fun r => eval_zero (shuffle5 r)
  add_mem' := fun hf hg r => by rw [eval_add, hf r, hg r, add_zero]
  smul_mem' := fun c _ hf r => by rw [eval_smul, hf r, mul_zero]

theorem shuffleAnnih5_iff_mem_span (f : Vec5) :
    ShuffleAnnih5 f ↔ f ∈ Submodule.span ℚ (Set.range lyndon5) := by
  constructor
  · intro hf
    rw [eq_sum_lyndon5 hf]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hf
    exact show f ∈ shuffleAnnih5Space from
      (Submodule.span_le.mpr (Set.range_subset_iff.mpr lyndon5_annih) :
        Submodule.span ℚ (Set.range lyndon5) ≤ shuffleAnnih5Space) hf

theorem shuffleAnnih5Space_eq_span : shuffleAnnih5Space = Submodule.span ℚ (Set.range lyndon5) :=
  Submodule.ext shuffleAnnih5_iff_mem_span

theorem finrank_shuffleAnnih5Space : Module.finrank ℚ shuffleAnnih5Space = 48 := by
  rw [shuffleAnnih5Space_eq_span, finrank_span_eq_card linearIndependent_lyndon5]
  simp

theorem finrank_shuffleAnnih5Space_witt :
    Module.finrank ℚ shuffleAnnih5Space = (3^5 - 3) / 5 := by
  norm_num [finrank_shuffleAnnih5Space]

section CharacteristicFive

private def pureWord : Word5 := ⟨0,0,0,0,0⟩

private def fifthPower (w : Word5) : ZMod 5 := if w = pureWord then 1 else 0

set_option maxRecDepth 20000 in
theorem fifthPower_annih (r : ShuffleRow) : eval (shuffle5 r) fifthPower = 0 := by
  rcases r with ⟨tag,a,b,c,d,e⟩
  revert a b c d e
  cases tag <;> decide +kernel

theorem bracket5_pure (i : Fin 48) : coeff (bracket5 i) pureWord = 0 := by
  revert i
  decide +kernel

/-- A pure fifth power satisfies the same shuffle equations in characteristic
five, but cannot be a linear combination of the commutator columns. -/
theorem characteristic_five_control :
    (∀ r, eval (shuffle5 r) fifthPower = 0) ∧
      ¬ ∃ g : Fin 48 → ZMod 5,
        fifthPower = ∑ i, g i • (fun w => (coeff (bracket5 i) w : ZMod 5)) := by
  refine ⟨fifthPower_annih, ?_⟩
  rintro ⟨g, h⟩
  have hc := congrFun h pureWord
  simp [fifthPower, bracket5_pure] at hc
  exact (by decide : (1 : ZMod 5) ≠ 0) hc

end CharacteristicFive

end Psc.Lie5
