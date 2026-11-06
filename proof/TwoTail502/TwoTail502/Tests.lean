import TwoTail502.Theorem

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace TwoTail502
open Letter Tail

theorem exception_literal_b1_source1 :
    (iterate (source t102 0 1) 4 [o]).take 28 =
      [o,z,t,t,o,z,o,t,o,t,o,z,o,o,z,t,t,o,z,o,o,z,t,o,z,t,t,o] := by decide

theorem exception_literal_b1_source2 :
    (iterate (source t102 0 1) 4 [t]).take 28 =
      [t,o,z,o,o,z,t,o,z,t,t,o,z,o,t,o,o,z,t,t,o,o,z,t,t,o,z,o] := by decide

theorem exception_literal_b2_source1 :
    (iterate (source t102 0 2) 4 [o]).take 51 =
      [o,z,t,t,o,o,t,o,o,z,o,t,o,o,t,o,o,z,o,o,z,t,t,o,o,z,o,o,z,t,o,z,t,t,o,o,t,o,o,o,z,t,t,o,o,t,o,o,t,o,o] := by decide

theorem exception_literal_b2_source2 :
    (iterate (source t102 0 2) 4 [t]).take 51 =
      [t,o,o,z,o,o,z,t,o,z,t,t,o,o,t,o,o,o,z,t,t,o,o,t,o,o,z,o,t,o,o,o,z,t,t,o,o,t,o,o,o,z,t,t,o,o,t,o,o,z,o] := by decide

theorem no_empty_parameter_pair : ¬ 1 ≤ (0 : ℕ)+0 := by decide

/-- A nonempty balanced cut witness has a finite search index. -/
theorem witness_has_cut {u v : Word} (h : Witness u v) :
    ∃ p, p < u.length ∧ ∃ c, CutAt u v p c := by
  rcases h with ⟨p,q,c,hb,hp,hq⟩
  have hlen := balanced_length hb
  have hpu : p.IsPrefix u := (List.prefix_append p [c]).trans hp
  have hqv : q.IsPrefix v := (List.prefix_append q [c]).trans hq
  have hpt : u.take p.length = p := (List.prefix_iff_eq_take.mp hpu).symm
  have hqt : v.take p.length = q := by
    rw [hlen]
    exact (List.prefix_iff_eq_take.mp hqv).symm
  have hl := hp.length_le
  simp only [List.length_append,List.length_singleton] at hl
  refine ⟨p.length,by omega,c,?_⟩
  simpa only [CutAt,hpt,hqt] using And.intro hb (And.intro hp hq)

def NoCuts (u v : Word) : Prop :=
  ∀ p : Fin u.length,
    ¬ CutAt u v p.val z ∧ ¬ CutAt u v p.val o ∧ ¬ CutAt u v p.val t
instance (u v : Word) : Decidable (NoCuts u v) := by unfold NoCuts; infer_instance

theorem no_witness_of_no_cuts {u v : Word} (h : NoCuts u v) : ¬ Witness u v := by
  intro hw
  rcases witness_has_cut hw with ⟨p,hp,c,hc⟩
  have hh := h ⟨p,hp⟩
  cases c
  · exact hh.1 hc
  · exact hh.2.1 hc
  · exact hh.2.2 hc

theorem sharp_no_generation_zero : ¬ SourceWitness (source t120 0 2) 0 z t := by
  apply no_witness_of_no_cuts
  decide
theorem sharp_no_generation_one : ¬ SourceWitness (source t120 0 2) 1 z t := by
  apply no_witness_of_no_cuts
  decide
theorem sharp_no_generation_two : ¬ SourceWitness (source t120 0 2) 2 z t := by
  apply no_witness_of_no_cuts
  decide
theorem sharp_no_generation_three : ¬ SourceWitness (source t120 0 2) 3 z t := by
  apply no_witness_of_no_cuts
  decide
theorem sharp_no_generation_four : ¬ SourceWitness (source t120 0 2) 4 z t := by
  apply no_witness_of_no_cuts
  decide
theorem sharp_generation_five : SourceWitness (source t120 0 2) 5 z t := by
  exact uniform_pairwise_five t120 0 2 (by decide) z t

theorem sharp_all_lower (n : ℕ) (hn : n < 5) :
    ¬ SourceWitness (source t120 0 2) n z t := by
  interval_cases n
  · exact sharp_no_generation_zero
  · exact sharp_no_generation_one
  · exact sharp_no_generation_two
  · exact sharp_no_generation_three
  · exact sharp_no_generation_four

theorem no_smaller_common_bound (n : ℕ) (hn : n < 5) :
    ¬ (∀ tail a b, 1 ≤ a+b → PairwiseAt (source tail a b) n) := by
  intro h
  exact sharp_all_lower n hn (h t120 0 2 (by decide) z t)

#print axioms sharp_no_generation_four
#print axioms sharp_generation_five
#print axioms reject_large102_b2
end TwoTail502
