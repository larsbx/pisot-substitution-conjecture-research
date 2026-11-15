/- Ternary word defects in the degree-five shuffle annihilator. -/
import PscVerif.Defect5
import PscVerif.Lie5

namespace Psc.Defect5Lie

open scoped BigOperators

open Psc.Defect4 Psc.Defect5 Psc.Lie5 Psc.SignedCocycle Psc.Incidence Psc.Binomial

def k5Vec (u v : List (Fin 3)) : Vec5 :=
  fun ⟨a,b,c,d,e⟩ => K5 u v a b c d e

theorem shuffleAnnih5_k5Vec {u v : List (Fin 3)} (h : Equiv4 u v) :
    ShuffleAnnih5 (k5Vec u v) := by
  rintro ⟨tag,a,b,c,d,e⟩
  cases tag
  · have hcast := congrArg (fun z : ℤ => (z : ℚ)) (k5_shuffle_left h a b c d e)
    push_cast at hcast
    simp [shuffle5, eval, k5Vec, add_assoc] at *
    exact hcast
  · have hcast := congrArg (fun z : ℤ => (z : ℚ)) (k5_shuffle_two h a b c d e)
    push_cast at hcast
    simp [shuffle5, eval, k5Vec, add_assoc] at *
    exact hcast

theorem k5Vec_mem_span_lyndon5 {u v : List (Fin 3)} (h : Equiv4 u v) :
    k5Vec u v ∈ Submodule.span ℚ (Set.range lyndon5) :=
  (shuffleAnnih5_iff_mem_span _).mp (shuffleAnnih5_k5Vec h)

theorem q5_col_mem_lie5 {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) (j : P.Rep) :
    (fun w : Word5 => (Q5 P w j : ℚ)) ∈ Submodule.span ℚ (Set.range lyndon5) :=
  k5Vec_mem_span_lyndon5 (hbal j.1 (P.sub j.2))

theorem k4_eq_zero_of_equiv4 {u v : List (Fin 3)} (h : Equiv4 u v) (a b c d : Fin 3) :
    K4 u v a b c d = 0 := by
  simp [K4, h.2]

/-- The rational fifth tensor action in word coordinates. -/
def phi5 (M : Matrix (Fin 3) (Fin 3) ℚ) (f : Vec5) : Vec5 :=
  fun ⟨a,b,c,d,e⟩ =>
    ∑ x, ∑ y, ∑ z, ∑ r, ∑ t, M a x * M b y * M c z * M d r * M e t * f ⟨x,y,z,r,t⟩

/-- The signed intertwiner on the actual rational Lie columns. -/
theorem phi5_k5Vec_rep {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : ∀ T ∈ S.C, Equiv4 T.1 T.2) (j : P.Rep) :
    phi5 ((inc S.s).map (Nat.cast : ℕ → ℚ)) (k5Vec j.1.1 j.1.2) =
      ∑ i : P.Rep, (P.Ssign i j : ℚ) • k5Vec i.1.1 i.1.2 := by
  funext w
  rcases w with ⟨a,b,c,d,e⟩
  have h := congrArg (fun n : ℤ => (n : ℚ)) (k5_rep P hbal j a b c d e)
  push_cast at h
  simpa only [phi5, k5Vec, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    using h

end Psc.Defect5Lie
