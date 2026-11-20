/-
Finite covering obstruction for the complete two-by-three eventual range.
The written transfer from a strict joining uses round-4 Lemmas A, C and L.
The two coordinates index the left and right periodic seam letters.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace Psc.PeriodicPartnerCompleteRange

abbrev Seam := Bool × Fin 3

/-- Consequences of a covering on the distinguished fibre when the endpoint
map for left asymptotes is injective. `left_vertex` is the only condition
on the type of a distinct asymptotic tiling. -/
structure CoveringData {X : Type*} (seam : Seam → X)
    (Left Right Partner : X → X → Prop) : Prop where
  seam_injective : Function.Injective seam
  left_agree : ∀ {e f}, e.1 = f.1 → Left (seam e) (seam f)
  right_agree : ∀ a row other, Right (seam (row, a)) (seam (other, a))
  right_trans : ∀ {x y z}, Right x y → Right y z → Right x z
  left_vertex : ∀ {x y}, Left x y → x ≠ y → ∃ e, seam e = x
  left_lift : ∀ {x y u}, Left x y → Partner x u → ∃ v, Partner y v ∧ Left u v
  right_lift : ∀ {x y u}, Right x y → Partner x u → ∃ v, Partner y v ∧ Right u v
  left_separation : ∀ {x u v}, Partner x u → Partner x v → Left u v → u = v
  strict_rays : ∀ {x y}, Partner x y → ¬ Left x y ∧ ¬ Right x y
  symmetric : ∀ {x y}, Partner x y → Partner y x
  total_on_seams : ∀ e, ∃ y, Partner (seam e) y

variable {X : Type*} {seam : Seam → X} {Left Right Partner : X → X → Prop}

private theorem next_column_distinct : ∀ a : Fin 3, a ≠ a + 1 := by decide

private theorem other_row (a b : Bool) (h : b ≠ a) : b = !a := by
  cases a <;> cases b <;> simp_all

/-- An interior partner would have to lift along a row to itself. It would
then have two distinct left-asymptotic partners, contrary to separation. -/
theorem partner_of_seam_is_vertex (D : CoveringData seam Left Right Partner)
    {e : Seam} {u : X} (hu : Partner (seam e) u) : ∃ f, seam f = u := by
  let other : Seam := (e.1, e.2 + 1)
  have hagree : Left (seam e) (seam other) := D.left_agree rfl
  obtain ⟨v, hv, huv⟩ := D.left_lift hagree hu
  apply D.left_vertex huv
  intro h
  subst v
  have eq := D.left_separation (D.symmetric hu) (D.symmetric hv) hagree
  exact next_column_distinct e.2 (congrArg Prod.snd (D.seam_injective eq))

/-- All partners of a seam now lie in the other row. Separation on that row
makes the partner unique. -/
theorem partners_of_seam_equal (D : CoveringData seam Left Right Partner)
    {e : Seam} {u v : X} (hu : Partner (seam e) u) (hv : Partner (seam e) v) : u = v := by
  obtain ⟨f, rfl⟩ := partner_of_seam_is_vertex D hu
  obtain ⟨g, rfl⟩ := partner_of_seam_is_vertex D hv
  have hf : f.1 ≠ e.1 := fun h => (D.strict_rays hu).1 (D.left_agree h.symm)
  have hg : g.1 ≠ e.1 := fun h => (D.strict_rays hv).1 (D.left_agree h.symm)
  have eq := (other_row _ _ hf).trans (other_row _ _ hg).symm
  exact D.left_separation hu hv (D.left_agree eq)

/-- A fixed-point-free permutation of three columns has order three. In this
form the square of its inverse is the original permutation. -/
theorem square_inverse_of_derangement :
    ∀ f g : Fin 3 → Fin 3, (∀ a, f (g a) = a) → (∀ a, f a ≠ a) →
      ∀ a, g (g a) = f a := by
  decide

/-- The left and right lifting and separation properties of a covering are
incompatible with this complete seam range. -/
theorem covering_impossible (D : CoveringData seam Left Right Partner) : False := by
  classical
  have hex : ∀ e, ∃ f, Partner (seam e) (seam f) := by
    intro e
    obtain ⟨u, hu⟩ := D.total_on_seams e
    obtain ⟨f, rfl⟩ := partner_of_seam_is_vertex D hu
    exact ⟨f, hu⟩
  choose p hp using hex
  have pinv (e : Seam) : p (p e) = e :=
    D.seam_injective (partners_of_seam_equal D (hp (p e)) (D.symmetric (hp e)))
  have prow (e : Seam) : (p e).1 = !e.1 := by
    apply other_row
    intro eq
    exact (D.strict_rays (hp e)).1 (D.left_agree eq.symm)
  let forward (a : Fin 3) := (p (false, a)).2
  let backward (a : Fin 3) := (p (true, a)).2
  have from_first (a : Fin 3) : p (false, a) = (true, forward a) :=
    Prod.ext (prow _) rfl
  have from_second (a : Fin 3) : p (true, a) = (false, backward a) :=
    Prod.ext (prow _) rfl
  have hInv (a : Fin 3) : forward (backward a) = a := by
    have eq := pinv (true, a)
    rw [from_second, from_first] at eq
    exact congrArg Prod.snd eq
  have hFree (a : Fin 3) : forward a ≠ a := by
    intro eq
    have strict := (D.strict_rays (hp (false, a))).2
    rw [from_first, eq] at strict
    exact strict (D.right_agree a false true)
  have hSquare := square_inverse_of_derangement forward backward hInv hFree
  let a : Fin 3 := backward 0
  obtain ⟨v, hv, hright⟩ := D.right_lift (D.right_agree a false true) (hp (false, a))
  have ev := partners_of_seam_equal D hv (hp (true, a))
  rw [ev, from_first, from_second, show forward a = 0 from hInv 0,
    show backward a = forward 0 from hSquare 0] at hright
  have contra := (D.strict_rays (hp (false, 0))).2
  rw [from_first] at contra
  exact contra (D.right_trans (D.right_agree 0 false true)
    (D.right_trans hright (D.right_agree (forward 0) false true)))

end Psc.PeriodicPartnerCompleteRange
