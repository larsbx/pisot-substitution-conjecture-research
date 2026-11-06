import TwoTail502.Core

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace TwoTail502
open Letter
inductive Tail | t102 | t120 deriving DecidableEq, Repr
open Tail
def A : Word := [z,o]
def B (a b : ℕ) : Word := power [o] a ++ [t] ++ power [o] b
def C : Tail → Word | t102 => [o,z,t] | t120 => [o,t,z]
def source (tail : Tail) (a b : ℕ) : Substitution
  | z => A
  | o => B a b
  | t => C tail
def F (a b : ℕ) : Word := A ++ B a b
def G (tail : Tail) (a b : ℕ) : Word :=
  power (B a b) a ++ C tail ++ power (B a b) b
def H (tail : Tail) (a b : ℕ) : Word :=
  match tail with
  | t102 => B a b ++ A ++ C tail
  | t120 => B a b ++ C tail ++ A
def U (tail : Tail) (a b : ℕ) : Word := F a b ++ G tail a b
def V (tail : Tail) (a b : ℕ) : Word :=
  power (G tail a b) a ++ H tail a b ++ power (G tail a b) b
def W (tail : Tail) (a b : ℕ) : Word :=
  match tail with
  | t102 => G tail a b ++ F a b ++ H tail a b
  | t120 => G tail a b ++ H tail a b ++ F a b
def X (tail : Tail) (a b : ℕ) : Word := U tail a b ++ V tail a b
def Y (tail : Tail) (a b : ℕ) : Word :=
  power (V tail a b) a ++ W tail a b ++ power (V tail a b) b
def Z (tail : Tail) (a b : ℕ) : Word :=
  match tail with
  | t102 => V tail a b ++ U tail a b ++ W tail a b
  | t120 => V tail a b ++ W tail a b ++ U tail a b

theorem source_nonerasing (tail : Tail) (a b : ℕ) : Nonerasing (source tail a b) := by
  intro c
  cases c <;> cases tail <;> simp [source, A, B, C]
theorem power_succ_right (w : Word) (n : ℕ) :
    power w (n+1) = power w n ++ w := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    change w ++ power w (n+1) = (w ++ power w n) ++ w
    rw [ih,List.append_assoc]
theorem power_comm (w : Word) (n : ℕ) :
    w ++ power w n = power w n ++ w := by
  rw [← power_succ, power_succ_right]
@[simp] theorem count_power (w : Word) (n : ℕ) (c : Letter) :
    (power w n).count c = n * w.count c := by
  induction n with
  | zero => simp
  | succ n ih => simp only [power_succ, List.count_append, ih, Nat.add_mul, Nat.one_mul]; omega

theorem level_two (tail : Tail) (a b : ℕ) :
    iterate (source tail a b) 2 [z] = F a b ∧
    iterate (source tail a b) 2 [o] = G tail a b ∧
    iterate (source tail a b) 2 [t] = H tail a b := by
  cases tail <;>
    simp [iterate, source, A, B, C, F, G, H, inflate_power, List.append_assoc]

@[simp] theorem iterate_B (σ : Substitution) (n a b : ℕ) :
    iterate σ n (B a b) =
      power (iterate σ n [o]) a ++ iterate σ n [t] ++ power (iterate σ n [o]) b := by
  unfold B
  rw [iterate_append,iterate_append,iterate_power,iterate_power]

theorem level_three (tail : Tail) (a b : ℕ) :
    iterate (source tail a b) 3 [z] = U tail a b ∧
    iterate (source tail a b) 3 [o] = V tail a b ∧
    iterate (source tail a b) 3 [t] = W tail a b := by
  have h := level_two tail a b
  have hi (c : Letter) :
      iterate (source tail a b) 3 [c] =
        iterate (source tail a b) 2 (source tail a b c) :=
    (iterate_commute _ 2 [c]).symm.trans (by simp)
  constructor
  · rw [hi]; simp [source, A, U, h.1, h.2.1]
  constructor
  · rw [hi]; simp [source, V, h.2.1, h.2.2]
  · rw [hi]; cases tail <;> simp [source, C, W, h.1, h.2.1, h.2.2, List.append_assoc]

theorem level_four (tail : Tail) (a b : ℕ) :
    iterate (source tail a b) 4 [z] = X tail a b ∧
    iterate (source tail a b) 4 [o] = Y tail a b ∧
    iterate (source tail a b) 4 [t] = Z tail a b := by
  have h := level_three tail a b
  have hi (c : Letter) :
      iterate (source tail a b) 4 [c] =
        iterate (source tail a b) 3 (source tail a b c) :=
    (iterate_commute _ 3 [c]).symm.trans (by simp)
  constructor
  · rw [hi]; simp [source, A, X, h.1, h.2.1]
  constructor
  · rw [hi]; simp [source, Y, h.2.1, h.2.2]
  · rw [hi]; cases tail <;> simp [source, C, Z, h.1, h.2.1, h.2.2, List.append_assoc]

theorem level_five (tail : Tail) (a b : ℕ) (c : Letter) :
    iterate (source tail a b) 5 [c] =
      match c with
      | z => X tail a b ++ Y tail a b
      | o => power (Y tail a b) a ++ Z tail a b ++ power (Y tail a b) b
      | t => match tail with
        | t102 => Y tail a b ++ X tail a b ++ Z tail a b
        | t120 => Y tail a b ++ Z tail a b ++ X tail a b := by
  have h := level_four tail a b
  have hi : iterate (source tail a b) 5 [c] =
      iterate (source tail a b) 4 (source tail a b c) :=
    (iterate_commute _ 4 [c]).symm.trans (by simp)
  rw [hi]
  cases c <;> cases tail <;>
    simp [source, A, C, h.1, h.2.1, h.2.2, List.append_assoc]

/- These are symbolic identities for arbitrary natural parameters, not samples. -/
theorem positive102_mass (a b : ℕ) :
    Balanced (F a b ++ power (G t102 a b) a)
      (power (G t102 a b) a ++ B a b ++ A) := by
  funext c
  simp [parikh, F, List.count_append]
  omega
theorem positive120_mass (a b : ℕ) :
    Balanced (F a b ++ power (G t120 a b) a ++ power (B a b) a ++ C t120)
      (power (G t120 a b) a ++ H t120 a b ++ power (B a b) a) := by
  funext c
  simp [parikh, F, H, List.count_append]
  omega
theorem boundary120_mass12 (b : ℕ) :
    Balanced (H t120 0 b ++ G t120 0 b) (G t120 0 b ++ H t120 0 b) := by
  funext c; simp [parikh, Nat.add_comm]
theorem boundary120_mass01 (b : ℕ) :
    Balanced (F 0 b ++ G t120 0 b ++ H t120 0 b)
      (G t120 0 b ++ H t120 0 b ++ F 0 b) := by
  funext c; simp [parikh]; omega

def large102_left (b : ℕ) : Word := Z t102 0 b ++ G t102 0 b ++ A ++ [t]
def large102_right (b : ℕ) : Word :=
  G t102 0 b ++ F 0 b ++ H t102 0 b ++ H t102 0 b ++
    power (G t102 0 b) b ++ H t102 0 b ++ power (G t102 0 b) 2
theorem large102_mass (b : ℕ) : Balanced (large102_left b) (large102_right b) := by
  funext c
  cases c <;>
    simp [parikh, large102_left, large102_right, Z, V, U, W, F, H, G, B, A, C,
      power_succ, List.count_cons, List.count_append] <;> ring


theorem positive102_counts (a b : ℕ) :
    parikh (F a b ++ power (G t102 a b) a) =
      fun c => match c with
      | z => a+1
      | o => a*((a+b)^2+1)+(a+b)+1
      | t => a*(a+b+1)+1 := by
  funext c
  cases c <;> simp [parikh,F,G,B,A,C,List.count_cons] <;> ring_nf <;> simp

theorem positive120_counts (a b : ℕ) :
    parikh (F a b ++ power (G t120 a b) a ++ power (B a b) a ++ C t120) =
      fun c => match c with
      | z => a+2
      | o => a*((a+b)^2+(a+b)+1)+(a+b)+2
      | t => a*(a+b+2)+2 := by
  funext c
  cases c <;> simp [parikh,F,G,B,A,C,List.count_cons] <;> ring_nf <;> simp

theorem large102_counts (b : ℕ) :
    parikh (large102_left b) = fun c => match c with
      | z => b+10
      | o => b^3+3*b^2+5*b+10
      | t => b^2+4*b+10 := by
  funext c
  cases c <;>
    simp [parikh,large102_left,Z,V,U,W,F,G,H,B,A,C,power_succ,List.count_cons] <;> ring

/- Predicate for exact finite cut controls. Only this decidable predicate is
computed; the infinite-family results below require symbolic prefix proofs. -/
def CutAt (u v : Word) (p : ℕ) (c : Letter) : Prop :=
  Balanced (u.take p) (v.take p) ∧
    (u.take p ++ [c]).IsPrefix u ∧ (v.take p ++ [c]).IsPrefix v
instance (u v : Word) (p : ℕ) (c : Letter) : Decidable (CutAt u v p c) := by
  unfold CutAt
  infer_instance
theorem cut_witness {u v : Word} {p : ℕ} {c : Letter} (h : CutAt u v p c) :
    Witness u v := ⟨u.take p,v.take p,c,h⟩

theorem exceptional102_b1 : SourceWitness (source t102 0 1) 4 o t := by
  apply cut_witness (p := 27) (c := o)
  decide
theorem exceptional102_b2 : SourceWitness (source t102 0 2) 4 o t := by
  apply cut_witness (p := 50) (c := o)
  decide
theorem reject_large102_b2 :
    ¬ (large102_right 2 ++ [o]).IsPrefix (iterate (source t102 0 2) 5 [t]) := by
  decide
theorem accept_large102_b3 :
    (large102_right 3 ++ [o]).IsPrefix (iterate (source t102 0 3) 5 [t]) := by
  decide

#print axioms level_five
#print axioms positive102_mass
#print axioms positive120_mass
#print axioms large102_mass
#print axioms exceptional102_b1
#print axioms exceptional102_b2
#print axioms reject_large102_b2
end TwoTail502
