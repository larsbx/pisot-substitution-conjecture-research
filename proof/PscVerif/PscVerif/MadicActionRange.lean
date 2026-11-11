import PscVerif.MadicResidue

/-! The range of the action on the original matrix-adic inverse limit. -/

namespace Psc.MadicResidue

variable {V : Type*} [AddCommGroup V]

/-- Division at level q uses the representative at level q+1. -/
theorem action_range_eq_ker_eval_one (M : V →ₗ[ℤ] V)
    (hinj : Function.Injective M) : LinearMap.range (action M) = (eval M 1).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact eval_one_action M y
  · intro hx
    change eval M 1 x = 0 at hx
    have lifts (q : ℕ) : ∃ z, quotient M (q + 1) (M z) = eval M (q + 1) x := by
      obtain ⟨w, hw⟩ := quotient_surjective M (q + 1) (eval M (q + 1) x)
      have hw₁ : quotient M 1 w = 0 := by
        rw [← reduction_quotient M (Nat.le_add_left 1 q), hw, reduction_eval, hx]
      obtain ⟨z, hz⟩ := (eval_one_star_eq_zero_iff M w).mp hw₁
      exact ⟨z, hz ▸ hw⟩
    choose z hz using lifts
    have cancel {q : ℕ} {v w : V}
        (h : quotient M (q + 1) (M v) = quotient M (q + 1) (M w)) :
        quotient M q v = quotient M q w := by
      obtain ⟨u, hu⟩ := (quotient_eq_iff M (q + 1) _ _).mp h
      apply (quotient_eq_iff M q _ _).mpr
      refine ⟨u, hinj ?_⟩
      rw [map_sub]
      simpa only [pow_succ', Module.End.mul_apply] using hu
    let y : Carrier M := ⟨fun q => quotient M q (z q), by
      intro m n h
      change quotient M m (z n) = quotient M m (z m)
      apply cancel
      rw [hz m, ← reduction_eval M (Nat.succ_le_succ h) x, ← hz n]
      rfl⟩
    refine ⟨y, carrier_ext M fun q => ?_⟩
    change quotient M q (M (z q)) = eval M q x
    rw [← reduction_quotient M (Nat.le_succ q), hz, reduction_eval]

/-- The action cokernel is the actual first residue, including its group law. -/
noncomputable def actionCokernelEquiv (M : V →ₗ[ℤ] V) (hinj : Function.Injective M) :
    (Carrier M ⧸ LinearMap.range (action M)) ≃ₗ[ℤ] Residue M 1 :=
  (Submodule.quotEquivOfEq _ _ (action_range_eq_ker_eval_one M hinj)).trans
    ((eval M 1).quotKerEquivOfSurjective (eval_surjective M 1))

end Psc.MadicResidue
