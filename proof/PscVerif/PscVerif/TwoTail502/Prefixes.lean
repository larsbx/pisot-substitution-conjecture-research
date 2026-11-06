import PscVerif.TwoTail502.Families

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace TwoTail502
open Letter Tail

theorem prepend_prefix (w : Word) {p v : Word} (h : p.IsPrefix v) :
    (w ++ p).IsPrefix (w ++ v) := by
  rcases h with ⟨r,hr⟩
  exact ⟨r, by simpa only [List.append_assoc] using congrArg (w ++ ·) hr⟩
theorem prefix_power_then {p u v : Word} (hu : p.IsPrefix u) (hv : p.IsPrefix v)
    (n : ℕ) : p.IsPrefix (power u n ++ v) := by
  cases n with
  | zero => simpa using hv
  | succ n => simpa only [power_succ, List.append_assoc] using
      prefix_extend hu (power u n ++ v)
theorem prefix_power_succ (w : Word) (n : ℕ) : w.IsPrefix (power w (n+1)) := by
  exact ⟨power w n,rfl⟩
theorem head_B (k b : ℕ) : [o].IsPrefix (B (k+1) b) := by
  simp [B, power_succ]
theorem head_C (tail : Tail) : [o].IsPrefix (C tail) := by
  cases tail <;> decide
theorem head_G_positive (tail : Tail) (k b : ℕ) : [o].IsPrefix (G tail (k+1) b) := by
  simpa only [G, power_succ, List.append_assoc] using
    prefix_extend (head_B k b)
      (power (B (k+1) b) k ++ C tail ++ power (B (k+1) b) b)
theorem head_G_zero (tail : Tail) (b : ℕ) : [o].IsPrefix (G tail 0 b) := by
  simpa only [G, power_zero, List.nil_append] using
    prefix_extend (head_C tail) (power (B 0 b) b)

theorem X_normal (tail : Tail) (a b : ℕ) :
    X tail a b = F a b ++ power (G tail a b) a ++ G tail a b ++
      H tail a b ++ power (G tail a b) b := by
  simpa only [X,U,V,List.append_assoc] using
    congrArg (fun w => F a b ++ w ++ H tail a b ++ power (G tail a b) b)
      (power_comm (G tail a b) a)

theorem positive102_prefixes (k b : ℕ) :
    let a := k+1
    let p := F a b ++ power (G t102 a b) a
    let q := power (G t102 a b) a ++ B a b ++ A
    (p ++ [o]).IsPrefix (X t102 a b) ∧
    (q ++ [o]).IsPrefix (Y t102 a b) ∧
    (q ++ [o]).IsPrefix (Z t102 a b) := by
  dsimp only
  have hp : ((F (k+1) b ++ power (G t102 (k+1) b) (k+1)) ++ [o]).IsPrefix
      (X t102 (k+1) b) := by
    rw [X_normal]
    simpa only [List.append_assoc] using prepend_prefix
      (F (k+1) b ++ power (G t102 (k+1) b) (k+1))
      (prefix_extend (head_G_positive t102 k b)
        (H t102 (k+1) b ++ power (G t102 (k+1) b) b))
  have hq : ((power (G t102 (k+1) b) (k+1) ++ B (k+1) b ++ A) ++ [o]).IsPrefix
      (V t102 (k+1) b) := by
    simpa only [V,H,List.append_assoc] using
      prepend_prefix (power (G t102 (k+1) b) (k+1) ++ B (k+1) b ++ A)
        (prefix_extend (head_C t102) (power (G t102 (k+1) b) b))
  refine ⟨hp,?_,?_⟩
  · simpa only [Y,power_succ,List.append_assoc] using
      prefix_extend hq (power (V t102 (k+1) b) k ++ W t102 (k+1) b ++
        power (V t102 (k+1) b) b)
  · simpa only [Z,List.append_assoc] using
      prefix_extend hq (U t102 (k+1) b ++ W t102 (k+1) b)

theorem positive120_prefixes (k b : ℕ) :
    let a := k+1
    let p := F a b ++ power (G t120 a b) a ++ power (B a b) a ++ C t120
    let q := power (G t120 a b) a ++ H t120 a b ++ power (B a b) a
    (p ++ [o]).IsPrefix (X t120 a b) ∧
    (q ++ [o]).IsPrefix (Y t120 a b) ∧
    (q ++ [o]).IsPrefix (Z t120 a b) := by
  dsimp only
  have hH : [o].IsPrefix (H t120 (k+1) b) := by
    simpa only [H,List.append_assoc] using
      prefix_extend (head_B k b) (C t120 ++ A)
  have hp : ((F (k+1) b ++ power (G t120 (k+1) b) (k+1) ++
      power (B (k+1) b) (k+1) ++ C t120) ++ [o]).IsPrefix (X t120 (k+1) b) := by
    rw [X_normal]
    simpa only [G,List.append_assoc] using
      prepend_prefix (F (k+1) b ++ power (G t120 (k+1) b) (k+1) ++
        power (B (k+1) b) (k+1) ++ C t120)
        (prefix_extend (prefix_power_then (head_B k b) hH b)
          (power (G t120 (k+1) b) b))
  have hqG : ((power (G t120 (k+1) b) (k+1) ++ H t120 (k+1) b ++
      power (B (k+1) b) (k+1)) ++ [o]).IsPrefix
      (power (G t120 (k+1) b) (k+1) ++ H t120 (k+1) b ++ G t120 (k+1) b) := by
    simpa only [G,List.append_assoc] using
      prepend_prefix (power (G t120 (k+1) b) (k+1) ++ H t120 (k+1) b ++
        power (B (k+1) b) (k+1))
        (prefix_extend (head_C t120) (power (B (k+1) b) b))
  have hvG : (G t120 (k+1) b).IsPrefix (V t120 (k+1) b) := by
    simpa only [V,power_succ,List.append_assoc] using
      List.prefix_append (G t120 (k+1) b)
        (power (G t120 (k+1) b) k ++ H t120 (k+1) b ++ power (G t120 (k+1) b) b)
  have hwG : (G t120 (k+1) b).IsPrefix (W t120 (k+1) b) := by
    exact ⟨H t120 (k+1) b ++ F (k+1) b, by simp [W,List.append_assoc]⟩
  refine ⟨hp,?_,?_⟩
  · cases b with
    | zero =>
      have hh := prepend_prefix
        (power (G t120 (k+1) 0) (k+1) ++ H t120 (k+1) 0)
        (prefix_power_then (hvG) (hwG) k)
      apply hqG.trans
      simpa only [Y,V,power_succ,power_zero,List.append_nil,List.append_assoc] using hh
    | succ l =>
      have hqV : ((power (G t120 (k+1) (l+1)) (k+1) ++ H t120 (k+1) (l+1) ++
          power (B (k+1) (l+1)) (k+1)) ++ [o]).IsPrefix (V t120 (k+1) (l+1)) := by
        apply hqG.trans
        simpa only [V,power_succ,List.append_assoc] using
          List.prefix_append
            (power (G t120 (k+1) (l+1)) (k+1) ++ H t120 (k+1) (l+1) ++ G t120 (k+1) (l+1))
            (power (G t120 (k+1) (l+1)) l)
      simpa only [Y,power_succ,List.append_assoc] using
        prefix_extend hqV (power (V t120 (k+1) (l+1)) k ++ W t120 (k+1) (l+1) ++
          power (V t120 (k+1) (l+1)) (l+1))
  · cases b with
    | zero =>
      apply hqG.trans
      simpa only [Z,V,power_zero,List.append_nil,List.append_assoc] using
        prepend_prefix (power (G t120 (k+1) 0) (k+1) ++ H t120 (k+1) 0)
          (prefix_extend hwG (U t120 (k+1) 0))
    | succ l =>
      apply hqG.trans
      simpa only [Z,V,power_succ,List.append_assoc] using
        List.prefix_append
          (power (G t120 (k+1) (l+1)) (k+1) ++ H t120 (k+1) (l+1) ++ G t120 (k+1) (l+1))
          (power (G t120 (k+1) (l+1)) l ++ W t120 (k+1) (l+1) ++ U t120 (k+1) (l+1))

def EndsOne (w : Word) : Prop := ∃ r, w = r ++ [o]
theorem ends_append (u : Word) {v : Word} (h : EndsOne v) : EndsOne (u ++ v) := by
  rcases h with ⟨r,hr⟩
  exact ⟨u ++ r, by simp [hr,List.append_assoc]⟩
theorem ends_power (w : Word) (h : EndsOne w) (k : ℕ) : EndsOne (power w (k+1)) := by
  rw [power_succ_right]; exact ends_append _ h
theorem boundary120_ends (k : ℕ) :
    EndsOne (F 0 (k+1)) ∧ EndsOne (G t120 0 (k+1)) ∧ EndsOne (H t120 0 (k+1)) := by
  have hb : EndsOne (B 0 (k+1)) := by
    simpa only [B,power_zero,List.nil_append] using
      ends_append [t] (ends_power [o] ⟨[],rfl⟩ k)
  refine ⟨ends_append A hb,?_,?_⟩
  · simpa only [G,power_zero,List.nil_append] using
      ends_append (C t120) (ends_power (B 0 (k+1)) hb k)
  · exact ends_append _ ⟨[z],rfl⟩

theorem witness_ending {u v f g : Word} (hb : Balanced f g)
    (hf : f.IsPrefix u) (hg : g.IsPrefix v) (ef : EndsOne f) (eg : EndsOne g) :
    Witness u v := by
  rcases ef with ⟨p,hp⟩
  rcases eg with ⟨q,hq⟩
  refine ⟨p,q,o,?_,hp ▸ hf,hq ▸ hg⟩
  funext c
  have hh := congrFun hb c
  simp only [Balanced,parikh] at hh ⊢
  rw [hp,hq] at hh
  simp only [List.count_append] at hh
  omega

theorem boundary120_pair12 (k : ℕ) : SourceWitness (source t120 0 (k+1)) 3 o t := by
  have hh := level_three t120 0 (k+1)
  rw [SourceWitness,hh.2.1,hh.2.2]
  apply witness_ending (boundary120_mass12 (k+1))
  · simp [V,power_succ,List.append_assoc]
  · exact ⟨F 0 (k+1), by simp [W,List.append_assoc]⟩
  · exact ends_append _ (boundary120_ends k).2.1
  · exact ends_append _ (boundary120_ends k).2.2

theorem boundary120_pair01 (k : ℕ) : SourceWitness (source t120 0 (k+1)) 4 z o := by
  have hh := level_four t120 0 (k+1)
  rw [SourceWitness,hh.1,hh.2.1]
  apply witness_ending (boundary120_mass01 (k+1))
  · exact ⟨power (G t120 0 (k+1)) (k+1), by simp [X,U,V,List.append_assoc]⟩
  · exact ⟨power (V t120 0 (k+1)) (k+1), by simp [Y,W,List.append_assoc]⟩
  · exact ends_append _ (boundary120_ends k).2.2
  · exact ends_append _ (boundary120_ends k).1

theorem boundary120_pair02 (k : ℕ) : SourceWitness (source t120 0 (k+1)) 5 z t := by
  have hh := boundary120_pair01 k
  rw [SourceWitness,(level_four t120 0 (k+1)).1,(level_four t120 0 (k+1)).2.1] at hh
  rw [SourceWitness,level_five,level_five]
  simpa only [List.append_assoc] using
    witness_extend hh (Y t120 0 (k+1)) (Z t120 0 (k+1) ++ X t120 0 (k+1))

theorem boundary102_pair01 (b : ℕ) : SourceWitness (source t102 0 b) 2 z o := by
  rw [SourceWitness,(level_two t102 0 b).1,(level_two t102 0 b).2.1]
  refine ⟨[z,o],[o,z],t,by decide,?_,?_⟩
  · simp [F,B,A]
  · simp [G,C]

theorem boundary102_pair02 (k : ℕ) : SourceWitness (source t102 0 (k+1)) 2 z t := by
  rw [SourceWitness,(level_two t102 0 (k+1)).1,(level_two t102 0 (k+1)).2.2]
  refine ⟨A ++ [t] ++ power [o] k,B 0 (k+1) ++ [z],o,?_,?_,?_⟩
  · funext c
    cases c <;> simp [parikh,B,A,power_succ,List.count_cons] <;> omega
  · exact ⟨[], by simp [F,B,power_succ_right,List.append_assoc]⟩
  · exact ⟨C t102, by simp [H,A,List.append_assoc]⟩

theorem large102_prefixes (k : ℕ) :
    (large102_left (k+3) ++ [o]).IsPrefix (iterate (source t102 0 (k+3)) 5 [o]) ∧
    (large102_right (k+3) ++ [o]).IsPrefix (iterate (source t102 0 (k+3)) 5 [t]) := by
  constructor
  · rw [level_five]
    simp only [large102_left,power_zero,List.nil_append,power_succ,
      Y,V,W,F,List.append_assoc,List.prefix_append_right_inj]
    simp [B,A,power_succ,List.append_assoc]
  · have hp : (large102_right (k+3) ++ [o]).IsPrefix (Y t102 0 (k+3)) := by
      simp only [large102_right,Y,V,W,power_zero,List.nil_append,power_succ,
        List.append_nil,List.append_assoc,List.prefix_append_right_inj]
      exact prefix_extend (head_G_zero t102 (k+3)) _
    rw [level_five]
    simpa only [List.append_assoc] using
      prefix_extend hp (X t102 0 (k+3) ++ Z t102 0 (k+3))

theorem large102_pair12 (k : ℕ) : SourceWitness (source t102 0 (k+3)) 5 o t :=
  ⟨large102_left (k+3),large102_right (k+3),o,large102_mass (k+3),
    (large102_prefixes k).1,(large102_prefixes k).2⟩
end TwoTail502
