import PscVerif.ForwardCarrier
import Mathlib.Tactic.FinCases

/-!
# Streaming refinement of indexed finite forward carriers

A three-counter scan proves each state's actual irreducible balanced-block
predicate. Complete ordered child tracks then identify the supplied row
with the source reduction by `red_unique`. This proves the existing
finite-carrier specification without evaluating its slow prefix-permutation
reduction on the concrete long words.

Compact word decoding, row-range checks and their proof aggregation use
ordinary kernel computation. Concrete acceptance remains separate.

Pre-code refinement gate:
`docs/c4-forward-carrier-fast-addendum-2026-11-12.md`.
-/

namespace Psc.FastForwardCarrier

open Psc.Binomial Psc.Reduction

abbrev Word := List (Fin 3)
abbrev Pair := Word × Word

/-- Three exact counters; no machine overflow or growing prefix is used. -/
structure Counter where
  c0 : Int
  c1 : Int
  c2 : Int
  deriving DecidableEq

namespace Counter

def zero : Counter := ⟨0, 0, 0⟩

def get (d : Counter) (c : Fin 3) : Int :=
  if c = 0 then d.c0 else if c = 1 then d.c1 else d.c2

def step (d : Counter) (a b : Fin 3) : Counter :=
  ⟨d.c0 + (if a = 0 then 1 else 0) - (if b = 0 then 1 else 0),
   d.c1 + (if a = 1 then 1 else 0) - (if b = 1 then 1 else 0),
   d.c2 + (if a = 2 then 1 else 0) - (if b = 2 then 1 else 0)⟩

@[simp] theorem get_zero (c : Fin 3) : zero.get c = 0 := by
  simp [get, zero]

theorem eq_zero_of_get {d : Counter} (h : ∀ c, d.get c = 0) : d = zero := by
  cases d with
  | mk x y z =>
    have hx : x = 0 := by simpa [get] using h 0
    have hy : y = 0 := by simpa [get] using h 1
    have hz : z = 0 := by simpa [get] using h 2
    subst x y z
    rfl

theorem get_step (d : Counter) (a b c : Fin 3) :
    (d.step a b).get c =
      d.get c + (if a = c then 1 else 0) - (if b = c then 1 else 0) := by
  fin_cases c <;> simp [get, step]

end Counter

/-- The initial displacement followed by the remaining top counts equals
the remaining bottom counts. At zero displacement this is `Equiv1`. -/
def ShiftedBalanced (d : Counter) (u v : Word) : Prop :=
  ∀ c, d.get c + (u.count c : Int) = (v.count c : Int)

private theorem int_count_cons (a c : Fin 3) (u : Word) :
    ((a :: u).count c : Int) = (u.count c : Int) + (if a = c then 1 else 0) := by
  by_cases h : a = c
  · subst a
    simp
  · simp [List.count_cons_of_ne h, h]

theorem shiftedBalanced_cons_iff (d : Counter) (a b : Fin 3) (u v : Word) :
    ShiftedBalanced d (a :: u) (b :: v) ↔
      ShiftedBalanced (d.step a b) u v := by
  constructor
  · intro h c
    have hc := h c
    rw [int_count_cons, int_count_cons] at hc
    rw [Counter.get_step]
    omega
  · intro h c
    have hc := h c
    rw [Counter.get_step] at hc
    rw [int_count_cons, int_count_cons]
    omega

/-- The top and bottom tracks are consumed together. The state after every
positive proper prefix must be nonzero; only the final state may be zero.
All per-letter counter work has fixed dimension three. -/
def scan : Counter → Word → Word → Bool
  | d, [], [] => decide (d = Counter.zero)
  | d, a :: u, b :: v =>
    decide (u = [] ∨ d.step a b ≠ Counter.zero) && scan (d.step a b) u v
  | _, _, _ => false

theorem scan_sound {d : Counter} {u v : Word} (h : scan d u v = true) :
    u.length = v.length ∧ ShiftedBalanced d u v ∧
      ∀ k, 0 < k → k < u.length →
        ¬ ShiftedBalanced d (u.take k) (v.take k) := by
  induction u generalizing d v with
  | nil =>
    cases v with
    | nil =>
      have hd : d = Counter.zero := of_decide_eq_true h
      subst d
      refine ⟨rfl, ?_, ?_⟩
      · intro c
        simp
      · intro k hk hkl
        simp at hkl
    | cons b v => simp [scan] at h
  | cons a u ih =>
    cases v with
    | nil => simp [scan] at h
    | cons b v =>
      change (decide (u = [] ∨ d.step a b ≠ Counter.zero) &&
        scan (d.step a b) u v) = true at h
      have hp := Bool.and_eq_true_iff.mp h
      have hguard : u = [] ∨ d.step a b ≠ Counter.zero := of_decide_eq_true hp.1
      obtain ⟨hlen, hbal, hirr⟩ := ih hp.2
      refine ⟨by simp [hlen], (shiftedBalanced_cons_iff d a b u v).2 hbal, ?_⟩
      intro k hk hkl hprefix
      have hu : u ≠ [] := by
        intro hu
        simp only [List.length_cons, hu, List.length_nil] at hkl
        omega
      have hnzero : d.step a b ≠ Counter.zero := hguard.resolve_left hu
      cases k with
      | zero => omega
      | succ k =>
        have hshift : ShiftedBalanced (d.step a b) (u.take k) (v.take k) :=
          (shiftedBalanced_cons_iff d a b (u.take k) (v.take k)).1
            (by simpa only [List.take_succ_cons] using hprefix)
        by_cases hk0 : k = 0
        · subst k
          apply hnzero
          apply Counter.eq_zero_of_get
          intro c
          simpa using hshift c
        · exact hirr k (by omega) (by simp only [List.length_cons] at hkl; omega) hshift

/-- Require a nonempty top word, then execute one exact streaming scan. -/
def isBlockCheck (T : Pair) : Bool :=
  decide (T.1 ≠ []) && scan Counter.zero T.1 T.2

/-- Streaming success entails exactly the repository's literal block
predicate: nonempty, balanced, and no balanced positive proper prefix. -/
theorem isBlockCheck_sound {T : Pair} (h : isBlockCheck T = true) : IsBlock T := by
  have hp := Bool.and_eq_true_iff.mp h
  have hnonempty : T.1 ≠ [] := of_decide_eq_true hp.1
  obtain ⟨_, hbal, hirr⟩ := scan_sound hp.2
  refine ⟨hnonempty, ?_, ?_⟩
  · intro c
    have hc := hbal c
    simp only [Counter.get_zero, zero_add] at hc
    omega
  · intro k hk hkl hprefix
    apply hirr k hk hkl
    intro c
    simp only [Counter.get_zero, zero_add]
    exact congrArg (fun n : Nat => (n : Int)) (hprefix c)

/-- The elementary noncoincidence block has no balanced proper prefix. -/
theorem block_control : isBlockCheck ([0, 1], [1, 0]) = true := by decide

theorem empty_control : isBlockCheck ([], []) = false := by decide

theorem unequal_lengths_control : isBlockCheck ([0], [0, 0]) = false := by decide

theorem unbalanced_endpoint_control : isBlockCheck ([0], [1]) = false := by decide

theorem proper_balanced_prefix_control : isBlockCheck ([0, 1], [0, 1]) = false := by decide

theorem singleton_coincidence_control : isBlockCheck ([2], [2]) = true := by decide


/-! ## Compact literals and indexed factorization certificates -/

/-- Only the three literal alphabet digits decode. -/
def decodeDigit (c : Char) : Option (Fin 3) :=
  if c = '0' then some 0 else if c = '1' then some 1
  else if c = '2' then some 2 else none

/-- A malformed digit fails the entire word, never just its suffix. -/
def decodeWord (text : String) : Option Word :=
  text.toList.mapM decodeDigit

/-- The empty fallback is rejected by the nonempty-block check for every
listed state, including states not reached from a seed. -/
def word (text : String) : Word := (decodeWord text).getD []

theorem literal_word_decoded : decodeWord "012" = some [0, 1, 2] := by decide

theorem malformed_word_rejected : decodeWord "01x2" = none := by decide

/-- The source-word and row lookup functions may use shared arrays or
balanced tables. Their implementation is untrusted: all resulting states,
rows and ordered seeds are checked. -/
structure Packet (n : Nat) where
  state : Fin n → Pair
  rows : Fin n → List (Fin n)
  seed : Fin 3 → Fin 3 → Fin n

variable {n : Nat}

def Packet.children (p : Packet n) (i : Fin n) : List Pair :=
  (p.rows i).map p.state

/-- Every actual unequal ordered letter pair is a represented seed. -/
def Packet.SeedsValid (p : Packet n) : Prop :=
  ∀ a b : Fin 3, a ≠ b → p.state (p.seed a b) = ([a, b], [b, a])

instance (p : Packet n) : Decidable p.SeedsValid := by
  unfold Packet.SeedsValid
  infer_instance

/-- Every listed state is checked once for irreducibility. The supplied
ordered row must reproduce both complete substituted tracks; coincidence
rows are empty because the target relation is `ChildNC`. -/
def Packet.RowValid (p : Packet n) (s : Fin 3 → Word) (i : Fin n) : Prop :=
  isBlockCheck (p.state i) = true ∧
    if (p.state i).1 = (p.state i).2 then p.rows i = []
    else ((p.children i).map Prod.fst).flatten = Psc.Binomial.subst s (p.state i).1 ∧
      ((p.children i).map Prod.snd).flatten = Psc.Binomial.subst s (p.state i).2

instance (p : Packet n) (s : Fin 3 → Word) (i : Fin n) :
    Decidable (p.RowValid s i) := by
  unfold Packet.RowValid
  infer_instance

def Packet.Valid (p : Packet n) (s : Fin 3 → Word) : Prop :=
  p.SeedsValid ∧ ∀ i, p.RowValid s i

/-- Complete checking can be split into kernel-reduced row ranges. -/
def Packet.checkAt (p : Packet n) (s : Fin 3 → Word) (i : Nat) : Bool :=
  if h : i < n then decide (p.RowValid s ⟨i, h⟩) else false

theorem Packet.checkAt_iff (p : Packet n) (s : Fin 3 → Word) (i : Nat) :
    p.checkAt s i = true ↔ ∃ h : i < n, p.RowValid s ⟨i, h⟩ := by
  unfold Packet.checkAt
  split_ifs with h <;> simp [h]

def Packet.checkRange (p : Packet n) (s : Fin 3 → Word) (start count : Nat) : Bool :=
  Nat.allLTTR count (fun i _ => p.checkAt s (start + i))

theorem Packet.checkRange_append (p : Packet n) (s : Fin 3 → Word)
    (start a b : Nat)
    (ha : p.checkRange s start a = true)
    (hb : p.checkRange s (start + a) b = true) :
    p.checkRange s start (a + b) = true := by
  simp only [Packet.checkRange, Nat.allLTTR_eq_true] at *
  intro i hi
  by_cases h : i < a
  · exact ha i h
  · have hsub : i - a < b := by omega
    have heq : start + a + (i - a) = start + i := by omega
    simpa only [heq] using hb (i - a) hsub

/-- Range aggregation discharges every real row. Out-of-range checks
return false and cannot be used to certify omitted rows. -/
theorem Packet.valid_of_range (p : Packet n) (s : Fin 3 → Word)
    (header : p.SeedsValid) (rows : p.checkRange s 0 n = true) : p.Valid s := by
  refine ⟨header, fun i => ?_⟩
  have hi := (Nat.allLTTR_eq_true.mp rows) i.val i.isLt
  simp only [Nat.zero_add] at hi
  obtain ⟨_, hrow⟩ := (p.checkAt_iff s i.val).mp hi
  exact hrow

/-- Every state used by any decoded child row is an actual irreducible
balanced block, not merely a pair with matching final counts. -/
theorem Packet.isBlock (p : Packet n) (s : Fin 3 → Word) (h : p.Valid s)
    (i : Fin n) : Psc.Reduction.IsBlock (p.state i) :=
  isBlockCheck_sound (h.2 i).1

/-- Complete literal concatenation plus irreducibility identifies the
supplied ordered row with actual `red`, including every occurrence. -/
theorem Packet.children_eq_red (p : Packet n) (s : Fin 3 → Word)
    (h : p.Valid s) (i : Fin n) (hne : (p.state i).1 ≠ (p.state i).2) :
    p.children i =
      Psc.Reduction.red (Psc.Binomial.subst s (p.state i).1)
        (Psc.Binomial.subst s (p.state i).2) := by
  have htracks := (h.2 i).2
  simp only [if_neg hne] at htracks
  apply Psc.Reduction.red_unique (p.children i) _ htracks.1 htracks.2
  intro T hT
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hT
  exact p.isBlock s h j

/-- Refinement to the original literal-state closure specification. This
does not evaluate the slow reduction checker on the concrete carrier. -/
theorem Packet.forward_valid (p : Packet n) (s : Fin 3 → Word) (h : p.Valid s) :
    Psc.ForwardCarrier.Valid s (List.ofFn p.state) := by
  constructor
  · intro T hT
    obtain ⟨a, b, hab, rfl⟩ := Psc.Descendants.mem_seeds.mp hT
    exact List.mem_ofFn.mpr ⟨p.seed a b, h.1 a b hab⟩
  · intro T hT hne U hU
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    rw [← p.children_eq_red s h i hne] at hU
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hU
    exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- Recover the existing checker equality by proof, not by re-executing
its prefix-permutation reduction on the long literal words. -/
theorem Packet.forward_check (p : Packet n) (s : Fin 3 → Word) (h : p.Valid s) :
    Psc.ForwardCarrier.check s (List.ofFn p.state) = true :=
  (Psc.ForwardCarrier.check_eq_true_iff s (List.ofFn p.state)).mpr (p.forward_valid s h)

theorem Packet.finite_bpaStatesNC (p : Packet n) (s : Fin 3 → Word) (h : p.Valid s) :
    (Psc.Descendants.bpaStatesNC s).Finite :=
  (p.forward_valid s h).finite_bpaStatesNC

theorem Packet.finite_reachable (p : Packet n) (s : Fin 3 → Word)
    (h : p.Valid s) (i : Fin n) :
    {U | Relation.ReflTransGen (Psc.Descendants.ChildNC s) (p.state i) U}.Finite :=
  (p.forward_valid s h).finite_reachable (List.mem_ofFn.mpr ⟨i, rfl⟩)

end Psc.FastForwardCarrier
