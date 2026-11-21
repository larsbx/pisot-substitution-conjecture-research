/- The six-phase product recognizes literal balanced-cut failures. -/
import PscVerif.PeriodicPartner
import PscVerif.PeriodicPartnerMarkerReachability
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

namespace Psc.PeriodicPartnerMarkerDecision

open Psc.PeriodicPartnerMarkerParity Psc.PeriodicPartnerMarkerReachability
open Function Relation
open scoped List

variable {A Q S : Type*}

/-- A proper prefix together with the occurrence immediately after it. -/
def Cut (w u : List A) (a : A) : Prop := ∃ r, w = u ++ a :: r

theorem Cut.of_prefix {w w' u : List A} {a : A} (h : Cut w u a) (hp : w <+: w') :
    Cut w' u a := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨t, rfl⟩ := hp
  exact ⟨r ++ t, by simp [List.append_assoc]⟩

theorem Cut.inflate {σ : A → List A} {w u p : List A} {a b : A}
    (h : Cut w u a) (hp : Cut (σ a) p b) :
    Cut (w.flatMap σ) (u.flatMap σ ++ p) b := by
  obtain ⟨r, rfl⟩ := h
  obtain ⟨t, ht⟩ := hp
  exact ⟨t ++ r.flatMap σ, by simp [ht, List.append_assoc]⟩

/-- Trace the following occurrence to its ancestor and recover its in-image digit. -/
theorem cut_flatMap {σ : A → List A} {w u : List A} {b : A}
    (h : Cut (w.flatMap σ) u b) :
    ∃ v a p, Cut w v a ∧ Cut (σ a) p b ∧ u = v.flatMap σ ++ p := by
  obtain ⟨r, hr⟩ := h
  induction w generalizing u with
  | nil => simp at hr
  | cons a w ih =>
    rw [List.flatMap_cons] at hr
    rcases List.append_eq_append_iff.mp hr with ⟨v, hu, hv⟩ | ⟨v, hv, hr⟩
    · obtain ⟨p, c, q, hc, hq, rfl⟩ := ih hv
      obtain ⟨t, rfl⟩ := hc
      exact ⟨a :: p, c, q, ⟨t, rfl⟩, hq, by simpa [List.append_assoc] using hu⟩
    · cases v with
      | nil =>
        have hi : σ a = u := by simpa using hv
        obtain ⟨p, c, q, hc, hq, he⟩ := ih (u := []) (by simpa using hr.symm)
        obtain ⟨t, rfl⟩ := hc
        exact ⟨a :: p, c, q, ⟨t, rfl⟩, hq, by simp [List.append_assoc, hi, ← he]⟩
      | cons c v =>
        obtain ⟨rfl, -⟩ := List.cons.inj hr
        exact ⟨[], a, u, ⟨w, rfl⟩, ⟨v, hv⟩, rfl⟩

/-- The contract surface of the exact Parikh automaton, with two occurrence digits. -/
structure ParikhDFA (Q : Type*) where
  start : Q
  step : Q → ℕ → ℕ → Q
  accepts : Q → Bool

/-- A synchronized pair of admissible occurrence addresses, with decoded prefixes. -/
inductive AddressPath (σ : A → List A) (D : ParikhDFA Q) (x y : A) :
    ℕ → Q → List A → A → List A → A → Prop
  | root : AddressPath σ D x y 0 D.start [] x [] y
  | snoc {n k u v a b p q c d} :
      AddressPath σ D x y n k u a v b → Cut (σ a) p c → Cut (σ b) q d →
      AddressPath σ D x y (n + 1) (D.step k p.length q.length)
        (u.flatMap σ ++ p) c (v.flatMap σ ++ q) d

def levelWord (σ : A → List A) (n : ℕ) (x : A) : List A :=
  ((List.flatMap σ)^[n]) [x]

theorem levelWord_succ (σ : A → List A) (n : ℕ) (x : A) :
    levelWord σ (n + 1) x = (levelWord σ n x).flatMap σ :=
  Function.iterate_succ_apply' _ _ _

theorem levelWord_head {σ : A → List A} {first : A → A}
    (hfirst : ∀ a, (σ a).head? = some (first a)) (n : ℕ) (x : A) :
    (levelWord σ n x).head? = some (first^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [levelWord_succ, head_flatMap σ first hfirst, ih, Function.iterate_succ_apply']
    rfl

theorem seed_prolongable {σ : A → List A} {first : A → A}
    (hfirst : ∀ a, (σ a).head? = some (first a)) {x : A} (hx : first^[6] x = x) :
    [x] <+: levelWord σ 6 x := by
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.mp (hx ▸ levelWord_head hfirst 6 x)
  exact ⟨r, hr.symm⟩

/-- A cut of the prolonged ray is a proper cut of some sixth-power approximant. -/
def RayCut (σ : A → List A) (x : A) (u : List A) (a : A) : Prop :=
  ∃ n, Cut (levelWord σ (6 * n) x) u a

theorem levelWord_prefix_of_le {σ : A → List A} {x : A}
    (hx : [x] <+: levelWord σ 6 x) {m n : ℕ} (hmn : m ≤ n) :
    levelWord σ (6 * m) x <+: levelWord σ (6 * n) x := by
  have preserve (k : ℕ) {u v : List A} (h : u <+: v) :
      ((List.flatMap σ)^[k]) u <+: ((List.flatMap σ)^[k]) v := by
    induction k with
    | zero => exact h
    | succ k ih =>
      simpa only [Function.iterate_succ_apply'] using ih.flatMap σ
  induction hmn with
  | refl => exact ⟨[], by simp⟩
  | @step n _ ih =>
    apply ih.trans
    rw [levelWord, levelWord, Nat.mul_succ, Function.iterate_add_apply]
    exact preserve (6 * n) hx

/-- Two independently located ray cuts persist to their common maximum depth. -/
theorem rayCuts_iff {σ : A → List A} {x y a b : A} {u v : List A}
    (hx : [x] <+: levelWord σ 6 x) (hy : [y] <+: levelWord σ 6 y) :
    (RayCut σ x u a ∧ RayCut σ y v b) ↔
      ∃ n, n % 6 = 0 ∧ Cut (levelWord σ n x) u a ∧ Cut (levelWord σ n y) v b := by
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    exact ⟨6 * max m n, by omega, hm.of_prefix (levelWord_prefix_of_le hx (le_max_left m n)),
      hn.of_prefix (levelWord_prefix_of_le hy (le_max_right m n))⟩
  · rintro ⟨n, hn, hu, hv⟩
    have h : 6 * (n / 6) = n := by omega
    exact ⟨⟨n / 6, by rwa [h]⟩, ⟨n / 6, by rwa [h]⟩⟩

theorem AddressPath.cuts {σ : A → List A} {D : ParikhDFA Q} {x y a b : A}
    {n : ℕ} {k : Q} {u v : List A} (h : AddressPath σ D x y n k u a v b) :
    Cut (levelWord σ n x) u a ∧ Cut (levelWord σ n y) v b := by
  induction h with
  | root => exact ⟨⟨[], rfl⟩, ⟨[], rfl⟩⟩
  | snoc h hp hq ih =>
    rw [levelWord_succ, levelWord_succ]
    exact ⟨ih.1.inflate hp, ih.2.inflate hq⟩

private theorem cut_singleton {x a : A} {u : List A} (h : Cut [x] u a) : u = [] ∧ a = x := by
  obtain ⟨r, hr⟩ := h
  cases u with
  | nil => simpa using (List.cons.inj hr).1.symm
  | cons b u =>
    have hl := congrArg List.length hr
    simp at hl

/-- Two cuts at the same depth can always be read by one synchronized path. -/
theorem addressPath_of_cuts {σ : A → List A} (D : ParikhDFA Q) {x y a b : A}
    {n : ℕ} {u v : List A} (hu : Cut (levelWord σ n x) u a)
    (hv : Cut (levelWord σ n y) v b) : ∃ k, AddressPath σ D x y n k u a v b := by
  induction n generalizing u v a b with
  | zero =>
    obtain ⟨rfl, rfl⟩ := cut_singleton hu
    obtain ⟨rfl, rfl⟩ := cut_singleton hv
    exact ⟨D.start, .root⟩
  | succ n ih =>
    rw [levelWord_succ] at hu hv
    obtain ⟨u', c, p, hprevTop, hp, rfl⟩ := cut_flatMap hu
    obtain ⟨v', d, q, hprevBottom, hq, rfl⟩ := cut_flatMap hv
    obtain ⟨k, h⟩ := ih hprevTop hprevBottom
    exact ⟨D.step k p.length q.length, h.snoc hp hq⟩

/-- The exact equality contract is only needed on words of admissible digits. -/
def ExactParikh (σ : A → List A) (D : ParikhDFA Q) (x y : A) : Prop :=
  ∀ ⦃n k u a v b⦄, AddressPath σ D x y n k u a v b → (D.accepts k = true ↔ u.Perm v)

def phase (n : ℕ) : Fin 6 := ⟨(6 - n % 6) % 6, by omega⟩

def previousPhase (j : Fin 6) : Fin 6 := ⟨(j.val + 5) % 6, by omega⟩

theorem phase_succ (n : ℕ) : phase (n + 1) = previousPhase (phase n) := by
  apply Fin.ext
  simp only [phase, previousPhase]
  omega

theorem phase_eq_zero (n : ℕ) : phase n = 0 ↔ n % 6 = 0 := by
  rw [Fin.ext_iff]
  change (6 - n % 6) % 6 = 0 ↔ n % 6 = 0
  omega

structure MarkerRules (σ : A → List A) (mark : ℤ → A → A → Bool) (first last : A → A) : Prop where
  first_image : ∀ a, (σ a).head? = some (first a)
  last_image : ∀ a, (σ a).getLast? = some (last a)
  phase_step : ∀ j a b, mark j (last a) (first b) = mark (j + 1) a b
  periodic : ∀ j, mark (j + 6) = mark j
  nilpotent : ∀ row, pull σ (pull σ (pull σ row)) = 0

private def endpointPhase (f : A → A) (j : ℤ) : A → A := f^[6 + (j % 6).toNat]

/-- The mismatch bit for a projected endpoint, with the marker group numbered zero. -/
def endpointGroup [DecidableEq A] (f : A → A) (marker a : A) : Bool :=
  decide (f^[6] a ≠ marker)

/-- The phase table used by the product, extended periodically to integer indices. -/
def projectedMark [DecidableEq A] (first last : A → A) (left right : A)
    (j : ℤ) (a b : A) : Bool :=
  decide (endpointPhase last j a = left) && decide (endpointPhase first j b = right)

theorem projectedMark_zero [DecidableEq A] (first last : A → A) (left right a b : A) :
    projectedMark first last left right 0 a b =
      (!endpointGroup last left a && !endpointGroup first right b) := by
  simp [projectedMark, endpointPhase, endpointGroup]

private theorem endpointPhase_step (f : A → A) (hf : f^[12] = f^[6]) (j : ℤ) (a : A) :
    endpointPhase f j (f a) = endpointPhase f (j + 1) a := by
  unfold endpointPhase
  rw [← Function.iterate_succ_apply]
  by_cases h : j % 6 = 5
  · have hl : (6 + (j % 6).toNat).succ = 12 := by omega
    have hr : 6 + ((j + 1) % 6).toNat = 6 := by omega
    rw [hl, hr]
    exact congrFun hf a
  · have he : (6 + (j % 6).toNat).succ = 6 + ((j + 1) % 6).toNat := by omega
    rw [he]

private theorem endpoint_six_idempotent (f : Fin 3 → Fin 3) : f^[12] = f^[6] := by
  funext a
  simpa only [← Function.iterate_add_apply] using Psc.PeriodicPartner.endpoint_period_six f (f^[4] a)

theorem markerRules_three {σ : Fin 3 → List (Fin 3)} {first last : Fin 3 → Fin 3}
    (hfirst : ∀ a, (σ a).head? = some (first a)) (hlast : ∀ a, (σ a).getLast? = some (last a))
    (hnil : ∀ row, pull σ (pull σ (pull σ row)) = 0) (left right : Fin 3) :
    MarkerRules σ (projectedMark first last left right) first last := by
  refine ⟨hfirst, hlast, ?_, ?_, hnil⟩
  · intro j a b
    simp only [projectedMark, endpointPhase_step _ (endpoint_six_idempotent _)]
  · intro j
    have h : (j + 6) % 6 = j % 6 := by omega
    have hp (f : Fin 3 → Fin 3) : endpointPhase f (j + 6) = endpointPhase f j := by
      unfold endpointPhase
      rw [h]
    funext a b
    simp [projectedMark, hp]

private theorem advance_phase_register {σ : A → List A} {mark : ℤ → A → A → Bool}
    {first last : A → A} (rules : MarkerRules σ mark first last) (j : Fin 6)
    (u v p q : List A) :
    advance σ mark (previousPhase j).val last (register σ mark j.val u v) p q =
      register σ mark (previousPhase j).val (u.flatMap σ ++ p) (v.flatMap σ ++ q) := by
  have wrap : register σ mark ((previousPhase j).val + 1 : ℤ) u v =
      register σ mark j.val u v := by
    by_cases hz : j.val = 0
    · have hv : (previousPhase j).val = 5 := by simp [previousPhase, hz]
      simpa [hv, hz] using register_periodic σ mark rules.periodic 0 u v
    · have hv : ((previousPhase j).val + 1 : ℤ) = j.val := by
        simp only [previousPhase]
        have hj := j.isLt
        omega
      rw [hv]
  rw [← wrap]
  exact advance_register σ mark (previousPhase j).val first last rules.first_image
    rules.last_image (rules.phase_step _) rules.nilpotent u v p q

structure ProductState (A Q : Type*) where
  parikh : Q
  phase : Fin 6
  top : A
  bottom : A
  marker : Register A

def productComponents : ProductState A Q ≃ Q × Fin 6 × A × A × Option A × Option A × ZMod 2 where
  toFun s := ⟨s.parikh, s.phase, s.top, s.bottom, s.marker.topLast, s.marker.bottomLast, s.marker.parity⟩
  invFun t := let ⟨k, j, a, b, c, d, p⟩ := t; ⟨k, j, a, b, ⟨c, d, p⟩⟩
  left_inv := by
    rintro ⟨k, j, a, b, c, d, p⟩
    rfl
  right_inv := by
    rintro ⟨k, j, a, b, c, d, p⟩
    rfl

noncomputable instance [Fintype A] [Fintype Q] : Fintype (ProductState A Q) :=
  Fintype.ofEquiv _ (Equiv.symm productComponents)

/-- A ternary product has 1728 states per Parikh state before any external sink. -/
theorem card_productState_three [Fintype Q] :
    Fintype.card (ProductState (Fin 3) Q) = 1728 * Fintype.card Q := by
  rw [Fintype.card_congr productComponents]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_option, ZMod.card]
  omega

theorem card_productState_with_sink_three [Fintype Q] :
    Fintype.card (Option (ProductState (Fin 3) Q)) = 1728 * Fintype.card Q + 1 := by
  rw [Fintype.card_option, card_productState_three]

def productStart (D : ParikhDFA Q) (x y : A) : ProductState A Q :=
  ⟨D.start, 0, x, y, ⟨none, none, 0⟩⟩

def view (σ : A → List A) (mark : ℤ → A → A → Bool) (n : ℕ)
    (k : Q) (u : List A) (a : A) (v : List A) (b : A) : ProductState A Q :=
  ⟨k, phase n, a, b, register σ mark (phase n).val u v⟩

theorem view_root (σ : A → List A) (mark : ℤ → A → A → Bool) (D : ParikhDFA Q) (x y : A) :
    view σ mark 0 D.start [] x [] y = productStart D x y := by
  simp [view, productStart, phase, register_empty]

def advanceProduct (σ : A → List A) (D : ParikhDFA Q) (mark : ℤ → A → A → Bool)
    (last : A → A) (s : ProductState A Q) (p q : List A) (a b : A) : ProductState A Q :=
  let j := previousPhase s.phase
  ⟨D.step s.parikh p.length q.length, j, a, b, advance σ mark j.val last s.marker p q⟩

def ProductStep (σ : A → List A) (D : ParikhDFA Q) (mark : ℤ → A → A → Bool)
    (last : A → A) (s t : ProductState A Q) : Prop :=
  ∃ p q a b, Cut (σ s.top) p a ∧ Cut (σ s.bottom) q b ∧
    t = advanceProduct σ D mark last s p q a b

theorem advance_view {σ : A → List A} {mark : ℤ → A → A → Bool} {first last : A → A}
    (rules : MarkerRules σ mark first last) (D : ParikhDFA Q) (n : ℕ) (k : Q)
    (u v p q : List A) (a b c d : A) :
    advanceProduct σ D mark last (view σ mark n k u a v b) p q c d =
      view σ mark (n + 1) (D.step k p.length q.length) (u.flatMap σ ++ p) c
        (v.flatMap σ ++ q) d := by
  simp only [advanceProduct, view, phase_succ, advance_phase_register rules]

/-- Every reachable product state represents a literal address, and conversely. -/
theorem reachable_iff_address {σ : A → List A} {mark : ℤ → A → A → Bool} {first last : A → A}
    (rules : MarkerRules σ mark first last) (D : ParikhDFA Q) (x y : A) (s : ProductState A Q) :
    ReflTransGen (ProductStep σ D mark last) (productStart D x y) s ↔
      ∃ n k u a v b, AddressPath σ D x y n k u a v b ∧ s = view σ mark n k u a v b := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨0, D.start, [], x, [], y, .root, (view_root σ mark D x y).symm⟩
    | tail _ edge ih =>
      obtain ⟨n, k, u, a, v, b, h, rfl⟩ := ih
      obtain ⟨p, q, c, d, hp, hq, rfl⟩ := edge
      exact ⟨n + 1, _, _, c, _, d, h.snoc hp hq, advance_view rules D n k u v p q a b c d⟩
  · rintro ⟨n, k, u, a, v, b, path, rfl⟩
    induction path with
    | root => rw [view_root]
    | snoc h hp hq ih =>
      exact ih.tail ⟨_, _, _, _, hp, hq, (advance_view rules D _ _ _ _ _ _ _ _ _ _).symm⟩

/-- The endpoint bits are true for the group different from the marker's group. -/
def Failure (left right : A → Bool) (origin : Bool) (a b : A)
    (lastTop lastBottom : Option A) (parity : ZMod 2) : Prop :=
  ∃ c d, lastTop = some c ∧ lastBottom = some d ∧
    (left c = left d ∨ right a = right b ∨ parity ≠ 1 + bit origin + bit (left c))

def Target (D : ParikhDFA Q) (left right : A → Bool) (origin : Bool) (s : ProductState A Q) : Prop :=
  s.phase = 0 ∧ D.accepts s.parikh = true ∧
    Failure left right origin s.top s.bottom s.marker.topLast s.marker.bottomLast s.marker.parity

def LiteralFailure (mark : A → A → Bool) (left right : A → Bool) (origin : Bool)
    (u : List A) (a : A) (v : List A) (b : A) : Prop :=
  u.Perm v ∧ Failure left right origin a b u.getLast? v.getLast?
    ((adjacentCount mark u : ZMod 2) - adjacentCount mark v)

def RayFailure (σ : A → List A) (x y : A) (mark : A → A → Bool)
    (left right : A → Bool) (origin : Bool) : Prop :=
  ∃ u a v b, RayCut σ x u a ∧ RayCut σ y v b ∧ LiteralFailure mark left right origin u a v b

theorem target_view_iff {σ : A → List A} {D : ParikhDFA Q} {mark : ℤ → A → A → Bool}
    {x y a b : A} {n : ℕ} {k : Q} {u v : List A} (e : ExactParikh σ D x y)
    (path : AddressPath σ D x y n k u a v b) (left right : A → Bool) (origin : Bool) :
    Target D left right origin (view σ mark n k u a v b) ↔
      n % 6 = 0 ∧ LiteralFailure (mark 0) left right origin u a v b := by
  simp only [Target, view, LiteralFailure, e path]
  by_cases hj : phase n = 0
  · have ht := (phase_eq_zero n).mp hj
    simp only [hj, ht, true_and, Fin.val_zero, Nat.cast_zero]
    apply and_congr_right
    intro hperm
    rw [register_of_perm σ mark 0 hperm]
  · have ht : n % 6 ≠ 0 := fun h => hj ((phase_eq_zero n).mpr h)
    simp [hj, ht]

/-- Acceptance is equivalent to a literal failure at a common phase-zero level. -/
theorem reachable_target_iff_literal {σ : A → List A} {mark : ℤ → A → A → Bool}
    {first last : A → A} {D : ParikhDFA Q} {x y : A}
    (rules : MarkerRules σ mark first last) (e : ExactParikh σ D x y)
    (left right : A → Bool) (origin : Bool) :
    (∃ s, ReflTransGen (ProductStep σ D mark last) (productStart D x y) s ∧
      Target D left right origin s) ↔
    ∃ n u a v b, n % 6 = 0 ∧ Cut (levelWord σ n x) u a ∧ Cut (levelWord σ n y) v b ∧
      LiteralFailure (mark 0) left right origin u a v b := by
  constructor
  · rintro ⟨s, hs, ht⟩
    obtain ⟨n, k, u, a, v, b, path, rfl⟩ := (reachable_iff_address rules D x y s).mp hs
    obtain ⟨hj, hf⟩ := (target_view_iff e path left right origin).mp ht
    exact ⟨n, u, a, v, b, hj, path.cuts.1, path.cuts.2, hf⟩
  · rintro ⟨n, u, a, v, b, hj, hu, hv, hf⟩
    obtain ⟨k, path⟩ := addressPath_of_cuts D hu hv
    exact ⟨_, (reachable_iff_address rules D x y _).mpr ⟨n, k, u, a, v, b, path, rfl⟩,
      (target_view_iff e path left right origin).mpr ⟨hj, hf⟩⟩

theorem reachable_target_iff_ray_failure {σ : A → List A} {mark : ℤ → A → A → Bool}
    {first last : A → A} {D : ParikhDFA Q} {x y : A}
    (rules : MarkerRules σ mark first last) (e : ExactParikh σ D x y)
    (hx : [x] <+: levelWord σ 6 x) (hy : [y] <+: levelWord σ 6 y)
    (left right : A → Bool) (origin : Bool) :
    (∃ s, ReflTransGen (ProductStep σ D mark last) (productStart D x y) s ∧
      Target D left right origin s) ↔ RayFailure σ x y (mark 0) left right origin := by
  rw [reachable_target_iff_literal rules e left right origin]
  constructor
  · rintro ⟨n, u, a, v, b, hj, hu, hv, hf⟩
    obtain ⟨hu, hv⟩ := (rayCuts_iff hx hy).mpr ⟨n, hj, hu, hv⟩
    exact ⟨u, a, v, b, hu, hv, hf⟩
  · rintro ⟨u, a, v, b, hu, hv, hf⟩
    obtain ⟨n, hj, hu, hv⟩ := (rayCuts_iff hx hy).mp ⟨hu, hv⟩
    exact ⟨n, u, a, v, b, hj, hu, hv, hf⟩

/-- A certificate includes the root, avoids targets, and contains all legal successors. -/
def ClosedCertificate (step : S → S → Prop) (root : S) (target : S → Prop) (states : Finset S) : Prop :=
  root ∈ states ∧ (∀ s ∈ states, ¬ target s) ∧ (∀ s ∈ states, ∀ t, step s t → t ∈ states)

theorem no_target_of_closed_certificate {step : S → S → Prop} {root : S} {target : S → Prop}
    {states : Finset S} (h : ClosedCertificate step root target states) :
    ¬ ∃ s, ReflTransGen step root s ∧ target s := by
  rintro ⟨s, hs, ht⟩
  have hm : s ∈ states := by
    clear ht
    induction hs with
    | refl => exact h.1
    | tail _ edge ih => exact h.2.2 _ ih _ edge
  exact h.2.1 s hm ht

theorem closed_certificate_of_no_target [Finite S] {step : S → S → Prop} {root : S}
    {target : S → Prop} (h : ¬ ∃ s, ReflTransGen step root s ∧ target s) :
    ∃ states, ClosedCertificate step root target states := by
  classical
  let reach : Set S := {s | ReflTransGen step root s}
  let states := reach.toFinite.toFinset
  have mem (s : S) : s ∈ states ↔ ReflTransGen step root s := Set.Finite.mem_toFinset _
  exact ⟨states, (mem root).mpr .refl, fun s hs ht => h ⟨s, (mem s).mp hs, ht⟩,
    fun s hs t edge => (mem t).mpr (((mem s).mp hs).tail edge)⟩

/-- A finite certificate exists exactly when the prescribed pair of rays has no failure. -/
theorem closed_certificate_iff_no_ray_failure [Fintype A] [Fintype Q]
    {σ : A → List A} {mark : ℤ → A → A → Bool} {first last : A → A}
    {D : ParikhDFA Q} {x y : A} (rules : MarkerRules σ mark first last) (e : ExactParikh σ D x y)
    (hx : [x] <+: levelWord σ 6 x) (hy : [y] <+: levelWord σ 6 y)
    (left right : A → Bool) (origin : Bool) :
    (∃ states, ClosedCertificate (ProductStep σ D mark last) (productStart D x y)
      (Target D left right origin) states) ↔ ¬ RayFailure σ x y (mark 0) left right origin := by
  rw [← reachable_target_iff_ray_failure rules e hx hy left right origin]
  exact ⟨fun ⟨states, h⟩ => no_target_of_closed_certificate h, closed_certificate_of_no_target⟩

/-- Bind the certificate theorem to the ternary endpoint projections and periodic seeds. -/
theorem ternary_certificate_iff_no_ray_failure [Fintype Q] {σ : Fin 3 → List (Fin 3)}
    {first last : Fin 3 → Fin 3} {D : ParikhDFA Q} {x y : Fin 3}
    (hfirst : ∀ a, (σ a).head? = some (first a)) (hlast : ∀ a, (σ a).getLast? = some (last a))
    (hnil : ∀ row, pull σ (pull σ (pull σ row)) = 0) (e : ExactParikh σ D x y)
    (hx : first^[6] x = x) (hy : first^[6] y = y) (l r : Fin 3) :
    let mark := projectedMark first last l r
    let left := endpointGroup last l
    let right := endpointGroup first r
    (∃ states, ClosedCertificate (ProductStep σ D mark last) (productStart D x y)
      (Target D left right (right x)) states) ↔ ¬ RayFailure σ x y (mark 0) left right (right x) :=
  closed_certificate_iff_no_ray_failure (markerRules_three hfirst hlast hnil l r) e
    (seed_prolongable hfirst hx) (seed_prolongable hfirst hy) _ _ _

/-- A target-free set containing the root can still omit a reachable target. -/
theorem singleton_root_fails_closure :
    ¬ ClosedCertificate (fun x y : Bool => x = false ∧ y = true) false (· = true) {false} := by
  intro h
  simpa using h.2.2 false (by simp) true ⟨rfl, rfl⟩

/-- Isolate each endpoint test and the parity test on nonempty prefixes. -/
theorem failure_controls :
    Failure id id false false true (some true) (some true) 0 ∧
    Failure id id false false false (some true) (some false) 0 ∧
    Failure id id false false true (some true) (some false) 1 ∧
    ¬ Failure id id false false true (some true) (some false) 0 := by
  unfold Failure
  decide

end Psc.PeriodicPartnerMarkerDecision
