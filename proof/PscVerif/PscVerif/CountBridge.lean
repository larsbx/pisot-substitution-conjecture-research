/-
# Bridges between the scattered-count definitions

The repository has two independent definitions of the scattered subword
counts, kept for their own proof styles:

* `PscVerif.Basic`: `Psc.N`, `Psc.N₂`, `Psc.N₃` over `Psc.Letter = Fin 3`,
  valued in `ℤ` (the shuffle identities of `PscVerif.Shuffle`), with the
  defects `Psc.BalancedPair.K₂`, `Psc.BalancedPair.K₃`;
* the generic counts `List.count`, `Psc.Binomial.n2`, `Psc.Incidence.n3` over
  any alphabet with decidable equality, valued in `ℕ` (the intertwiner
  modules), with the defects `Psc.Intertwiner2.K2`, `Psc.Intertwiner3.K3`.
  The kernel-checked controls of `PscVerif.ConcentrationControls` use these
  generic counts directly (its defect `k3` of the pair `(u13, v13)` is built
  from `Psc.Incidence.n3`).

Proved here, in full, by list induction: the two agree.

* `N_eq_count`, `N₂_eq_n2`, `N₃_eq_n3`: `N a w = |w|_a`, `N₂ a b w = n2 w a b`,
  `N₃ a b c w = n3 w a b c` (cast to `ℤ`);
* `K₂_eq_K2`, `K₃_eq_K3`: the defects of a `Psc.BalancedPair` are the generic
  `K2`, `K3` of its two words;
* `controls_k3_eq`: `ConcentrationControls.k3 = Intertwiner3.K3 u13 v13`
  (definitional).

No definition of `PscVerif.Basic` or `PscVerif.ConcentrationControls` is
changed; these are statements about them.
-/
import PscVerif.Basic
import PscVerif.ConcentrationControls
import PscVerif.Intertwiner2
import PscVerif.Intertwiner3

namespace Psc.CountBridge

open Psc.Binomial

theorem N_eq_count (a : Letter) (w : Word) : N a w = (w.count a : ℤ) := by
  induction w with
  | nil => rfl
  | cons x t ih =>
    simp only [N, ih, List.count_cons, ind, beq_iff_eq]
    by_cases h : x = a <;> simp [h, add_comm]

theorem N₂_eq_n2 (a b : Letter) (w : Word) : N₂ a b w = (n2 w a b : ℤ) := by
  induction w with
  | nil => rfl
  | cons x t ih =>
    simp only [N₂, ih, n2, N_eq_count, ind]
    by_cases h : x = a <;> simp [h]

theorem N₃_eq_n3 (a b c : Letter) (w : Word) :
    N₃ a b c w = (Psc.Incidence.n3 w a b c : ℤ) := by
  induction w with
  | nil => rfl
  | cons x t ih =>
    simp only [N₃, ih, Psc.Incidence.n3_cons, N₂_eq_n2, ind]
    by_cases h : x = a <;> simp [h]

theorem K₂_eq_K2 (s : BalancedPair) (a b : Letter) :
    s.K₂ a b = Psc.Intertwiner2.K2 s.u s.v a b := by
  simp [BalancedPair.K₂, Psc.Intertwiner2.K2, N₂_eq_n2]

theorem K₃_eq_K3 (s : BalancedPair) (a b c : Letter) :
    s.K₃ a b c = Psc.Intertwiner3.K3 s.u s.v a b c := by
  simp [BalancedPair.K₃, Psc.Intertwiner3.K3, N₃_eq_n3]

theorem controls_k3_eq (a b c : Fin 3) :
    ConcentrationControls.k3 a b c =
      Psc.Intertwiner3.K3 ConcentrationControls.u13 ConcentrationControls.v13 a b c :=
  rfl

end Psc.CountBridge
