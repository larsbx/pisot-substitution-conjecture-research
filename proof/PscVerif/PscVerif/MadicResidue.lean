import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# The actual algebraic matrix-adic carrier

For an integer-linear endomorphism `M`, this module constructs the compatible
sequences in the quotients by `range (M ^ q)`. The residue maps, integral
canonical map, and induced action are defined on that carrier, rather than
postulated on an unspecified ambient group. The first residue detects the
integral image of `M` exactly. Injectivity of the action on the inverse limit
uses injectivity of `M` and the next coordinate; a finite quotient action need
not be injective.

The canonical map need not be injective: its kernel is the intersection of all
power ranges. With finite discrete quotients the actual carrier is a compact
Hausdorff additive group. Finiteness is proved when the original group is a
finite free integer module and `M` is injective. These constructions do not
identify compact prefix tiles, establish their literal tile equations, or
construct Haar measure.
Pre-code gate: `docs/c4-madic-residue-literature-2026-11-11.md`.
-/

namespace Psc.MadicResidue

variable {V : Type*} [AddCommGroup V]

/-- The actual image submodule at depth `q`. -/
def powerRange (M : V →ₗ[ℤ] V) (q : ℕ) : Submodule ℤ V :=
  LinearMap.range (M ^ q)

/-- The integral quotient at depth `q`, including the trivial depth zero. -/
abbrev Residue (M : V →ₗ[ℤ] V) (q : ℕ) := V ⧸ powerRange M q

/-- The canonical class map; no choice of finite class labels is made. -/
def quotient (M : V →ₗ[ℤ] V) (q : ℕ) : V →ₗ[ℤ] Residue M q :=
  (powerRange M q).mkQ

theorem quotient_surjective (M : V →ₗ[ℤ] V) (q : ℕ) :
    Function.Surjective (quotient M q) :=
  (powerRange M q).mkQ_surjective

/-- Equality of classes is exact image-lattice membership, not a coordinate cap. -/
theorem quotient_eq_iff (M : V →ₗ[ℤ] V) (q : ℕ) (z w : V) :
    quotient M q z = quotient M q w ↔ ∃ y, (M ^ q) y = z - w :=
  Submodule.Quotient.eq (powerRange M q)

theorem quotient_eq_zero_iff (M : V →ₗ[ℤ] V) (q : ℕ) (z : V) :
    quotient M q z = 0 ↔ ∃ y, (M ^ q) y = z :=
  Submodule.Quotient.mk_eq_zero (p := powerRange M q)

theorem quotient_zero_level (M : V →ₗ[ℤ] V) (z : V) :
    quotient M 0 z = 0 := by
  apply (quotient_eq_zero_iff M 0 z).mpr
  exact ⟨z, rfl⟩

theorem power_apply_commute (M : V →ₗ[ℤ] V) (q : ℕ) (z : V) :
    (M ^ q) (M z) = M ((M ^ q) z) := by
  change ((M ^ q) * M) z = (M * M ^ q) z
  rw [← pow_succ, ← pow_succ']

theorem powerRange_antitone (M : V →ₗ[ℤ] V) : Antitone (powerRange M) := by
  intro m n h z hz
  obtain ⟨y, rfl⟩ := hz
  refine ⟨(M ^ (n - m)) y, ?_⟩
  change (M ^ m * M ^ (n - m)) y = (M ^ n) y
  rw [← pow_add, Nat.add_sub_of_le h]

/-- Reduction from a deeper quotient to an earlier one. -/
def reduction (M : V →ₗ[ℤ] V) {m n : ℕ} (h : m ≤ n) :
    Residue M n →ₗ[ℤ] Residue M m :=
  (powerRange M n).mapQ (powerRange M m) LinearMap.id
    (powerRange_antitone M h)

@[simp]
theorem reduction_quotient (M : V →ₗ[ℤ] V) {m n : ℕ} (h : m ≤ n) (z : V) :
    reduction M h (quotient M n z) = quotient M m z := rfl

theorem reduction_refl (M : V →ₗ[ℤ] V) (q : ℕ) (x : Residue M q) :
    reduction M (le_refl q) x = x := by
  obtain ⟨z, rfl⟩ := quotient_surjective M q x
  rfl

theorem reduction_trans (M : V →ₗ[ℤ] V) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (x : Residue M n) :
    reduction M hlm (reduction M hmn x) = reduction M (hlm.trans hmn) x := by
  obtain ⟨z, rfl⟩ := quotient_surjective M n x
  rfl

theorem powerRange_invariant (M : V →ₗ[ℤ] V) (q : ℕ) :
    powerRange M q ≤ (powerRange M q).comap M := by
  rintro z ⟨y, rfl⟩
  exact ⟨M y, power_apply_commute M q y⟩

/-- The finite-level action, without any claim that it is injective. -/
def residueAction (M : V →ₗ[ℤ] V) (q : ℕ) : Residue M q →ₗ[ℤ] Residue M q :=
  (powerRange M q).mapQ (powerRange M q) M (powerRange_invariant M q)

@[simp]
theorem residueAction_quotient (M : V →ₗ[ℤ] V) (q : ℕ) (z : V) :
    residueAction M q (quotient M q z) = quotient M q (M z) := rfl

theorem reduction_residueAction (M : V →ₗ[ℤ] V) {m n : ℕ}
    (h : m ≤ n) (x : Residue M n) :
    reduction M h (residueAction M n x) = residueAction M m (reduction M h x) := by
  obtain ⟨z, rfl⟩ := quotient_surjective M n x
  rfl

/-- The actual inverse limit, as a submodule of the product of all quotients. -/
def compatibleSequences (M : V →ₗ[ℤ] V) : Submodule ℤ (∀ q, Residue M q) where
  carrier := {x | ∀ {m n : ℕ} (h : m ≤ n), reduction M h (x n) = x m}
  zero_mem' := by
    intro m n h
    exact map_zero (reduction M h)
  add_mem' := by
    intro x y hx hy m n h
    change reduction M h (x n + y n) = x m + y m
    rw [map_add, hx h, hy h]
  smul_mem' := by
    intro a x hx m n h
    change reduction M h (a • x n) = a • x m
    rw [map_smul, hx h]

/-- Coherent quotient tuples; this is not a supplied arbitrary carrier. -/
abbrev Carrier (M : V →ₗ[ℤ] V) := ↥(compatibleSequences M)

/-- Exact quotient coordinate on the inverse limit. -/
def eval (M : V →ₗ[ℤ] V) (q : ℕ) : Carrier M →ₗ[ℤ] Residue M q :=
  (LinearMap.proj q).comp (compatibleSequences M).subtype

@[ext]
theorem carrier_ext (M : V →ₗ[ℤ] V) {x y : Carrier M}
    (h : ∀ q, eval M q x = eval M q y) : x = y :=
  Subtype.ext (funext h)

theorem reduction_eval (M : V →ₗ[ℤ] V) {m n : ℕ}
    (h : m ≤ n) (x : Carrier M) :
    reduction M h (eval M n x) = eval M m x := x.property h

/-- The integral canonical map, which may have a nontrivial kernel. -/
def star (M : V →ₗ[ℤ] V) : V →ₗ[ℤ] Carrier M where
  toFun z := ⟨fun q => quotient M q z, fun _ => rfl⟩
  map_add' z w := by
    apply Subtype.ext
    funext q
    exact map_add (quotient M q) z w
  map_smul' a z := by
    apply Subtype.ext
    funext q
    exact map_smul (quotient M q) a z

@[simp]
theorem eval_star (M : V →ₗ[ℤ] V) (q : ℕ) (z : V) :
    eval M q (star M z) = quotient M q z := rfl

theorem eval_surjective (M : V →ₗ[ℤ] V) (q : ℕ) :
    Function.Surjective (eval M q) := by
  intro x
  obtain ⟨z, rfl⟩ := quotient_surjective M q x
  exact ⟨star M z, rfl⟩

/-- The kernel of the integral map is the intersection of the actual power ranges. -/
theorem star_eq_zero_iff (M : V →ₗ[ℤ] V) (z : V) :
    star M z = 0 ↔ ∀ q, ∃ y, (M ^ q) y = z := by
  constructor
  · intro h q
    apply (quotient_eq_zero_iff M q z).mp
    rw [← eval_star, h, map_zero]
  · intro h
    apply carrier_ext M
    intro q
    rw [eval_star, map_zero]
    exact (quotient_eq_zero_iff M q z).mpr (h q)

/-- Multiplication by `M` on every quotient, restricted to coherent sequences. -/
def action (M : V →ₗ[ℤ] V) : Carrier M →ₗ[ℤ] Carrier M where
  toFun x := ⟨fun q => residueAction M q (eval M q x), by
    intro m n h
    rw [reduction_residueAction, reduction_eval]⟩
  map_add' x y := by
    apply Subtype.ext
    funext q
    exact map_add ((residueAction M q).comp (eval M q)) x y
  map_smul' a x := by
    apply Subtype.ext
    funext q
    exact map_smul ((residueAction M q).comp (eval M q)) a x

@[simp]
theorem eval_action (M : V →ₗ[ℤ] V) (q : ℕ) (x : Carrier M) :
    eval M q (action M x) = residueAction M q (eval M q x) := rfl

theorem action_star (M : V →ₗ[ℤ] V) (z : V) :
    action M (star M z) = star M (M z) := by
  apply carrier_ext M
  intro q
  rfl

theorem residueAction_pow_quotient (M : V →ₗ[ℤ] V) (q n : ℕ) (z : V) :
    (residueAction M q ^ n) (quotient M q z) = quotient M q ((M ^ n) z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, residueAction_quotient,
        pow_succ', Module.End.mul_apply]

theorem eval_action_pow (M : V →ₗ[ℤ] V) (q n : ℕ) (x : Carrier M) :
    eval M q ((action M ^ n) x) = (residueAction M q ^ n) (eval M q x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, eval_action, ih,
        pow_succ', Module.End.mul_apply]

/-- The depth-`q` quotient annihilates the `q`-fold action on the actual limit. -/
theorem eval_action_pow_self_zero (M : V →ₗ[ℤ] V) (q : ℕ) (x : Carrier M) :
    eval M q ((action M ^ q) x) = 0 := by
  rw [eval_action_pow]
  obtain ⟨z, hz⟩ := quotient_surjective M q (eval M q x)
  rw [← hz, residueAction_pow_quotient]
  exact (quotient_eq_zero_iff M q _).mpr ⟨z, rfl⟩

theorem eval_one_action (M : V →ₗ[ℤ] V) (x : Carrier M) :
    eval M 1 (action M x) = 0 := by
  simpa only [pow_one] using eval_action_pow_self_zero M 1 x

/-- The precise integral lifting test needed by the occurrence-cover interface. -/
theorem eval_one_star_eq_zero_iff (M : V →ₗ[ℤ] V) (z : V) :
    eval M 1 (star M z) = 0 ↔ ∃ y, M y = z := by
  simpa only [eval_star, pow_one] using quotient_eq_zero_iff M 1 z

/-- An integral translation lies in the limit-action range exactly when it has
an integral preimage. Neither implication needs injectivity of `M`. -/
theorem action_preimage_star_iff (M : V →ₗ[ℤ] V) (z : V) :
    (∃ x, action M x = star M z) ↔ ∃ y, M y = z := by
  constructor
  · rintro ⟨x, hx⟩
    apply (eval_one_star_eq_zero_iff M z).mp
    rw [← hx, eval_one_action]
  · rintro ⟨y, rfl⟩
    exact ⟨star M y, action_star M y⟩

/-- Cancellation needs the next quotient: the action on a single quotient
can have a nontrivial kernel even when the original action is injective. -/
theorem reduction_eq_zero_of_residueAction_eq_zero (M : V →ₗ[ℤ] V)
    (injective : Function.Injective M) (q : ℕ) (x : Residue M (q + 1))
    (hx : residueAction M (q + 1) x = 0) :
    reduction M (Nat.le_succ q) x = 0 := by
  obtain ⟨z, rfl⟩ := quotient_surjective M (q + 1) x
  rw [residueAction_quotient, quotient_eq_zero_iff] at hx
  obtain ⟨y, hy⟩ := hx
  rw [reduction_quotient, quotient_eq_zero_iff]
  refine ⟨y, injective ?_⟩
  simpa only [pow_succ', Module.End.mul_apply] using hy

theorem action_eq_zero (M : V →ₗ[ℤ] V) (injective : Function.Injective M)
    (x : Carrier M) (hx : action M x = 0) : x = 0 := by
  apply carrier_ext M
  intro q
  rw [map_zero, ← reduction_eval M (Nat.le_succ q) x]
  apply reduction_eq_zero_of_residueAction_eq_zero M injective
  have h := congrArg (eval M (q + 1)) hx
  simpa only [eval_action, map_zero] using h

/-- Injectivity is a theorem on the actual inverse limit, not a finite-table premise. -/
theorem action_injective (M : V →ₗ[ℤ] V) (injective : Function.Injective M) :
    Function.Injective (action M) := by
  intro x y h
  apply sub_eq_zero.mp
  apply action_eq_zero M injective
  rw [map_sub, h, sub_self]

/-- Every quotient is finite for an injective endomorphism of a finite free
integer module. This is proved from equal ranks, not supplied by a packet. -/
theorem residue_finite [Module.Free ℤ V] [Module.Finite ℤ V]
    (M : V →ₗ[ℤ] V) (injective : Function.Injective M) (q : ℕ) :
    Finite (Residue M q) :=
  Submodule.finiteQuotientOfFreeOfRankEq (powerRange M q)
    (LinearMap.finrank_range_of_inj (Module.End.iterate_injective injective q))

section Topology

/-- The quotient coordinates have their discrete topology. The inverse limit
uses the induced product topology, not the discrete topology on the limit. -/
instance residueTopologicalSpace (M : V →ₗ[ℤ] V) (q : ℕ) :
    TopologicalSpace (Residue M q) := ⊥

instance residueDiscreteTopology (M : V →ₗ[ℤ] V) (q : ℕ) :
    DiscreteTopology (Residue M q) := ⟨rfl⟩

theorem compatibleSequences_isClosed (M : V →ₗ[ℤ] V) :
    IsClosed (compatibleSequences M : Set (∀ q, Residue M q)) := by
  change IsClosed {x : ∀ q, Residue M q |
    ∀ m n (h : m ≤ n), reduction M h (x n) = x m}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun h =>
    isClosed_eq
      ((continuous_of_discreteTopology : Continuous (reduction M h)).comp (continuous_apply n))
      (continuous_apply m)

/-- Compactness follows from the actual closed compatibility conditions and
finite quotients. No tile or measure premise occurs here. -/
theorem carrier_compactSpace_of_finite (M : V →ₗ[ℤ] V)
    [∀ q, Finite (Residue M q)] : CompactSpace (Carrier M) :=
  isCompact_iff_compactSpace.mp (compatibleSequences_isClosed M).isCompact

/-- In particular, a nonsingular finite-rank integer action has a compact
matrix-adic carrier with the displayed quotient-coordinate topology. -/
theorem carrier_compactSpace [Module.Free ℤ V] [Module.Finite ℤ V]
    (M : V →ₗ[ℤ] V) (injective : Function.Injective M) :
    CompactSpace (Carrier M) := by
  let : ∀ q, Finite (Residue M q) := residue_finite M injective
  exact carrier_compactSpace_of_finite M

theorem continuous_eval (M : V →ₗ[ℤ] V) (q : ℕ) : Continuous (eval M q) :=
  (continuous_apply q).comp continuous_subtype_val

theorem continuous_action (M : V →ₗ[ℤ] V) : Continuous (action M) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun q =>
    (continuous_of_discreteTopology : Continuous (residueAction M q)).comp (continuous_eval M q)

end Topology

end Psc.MadicResidue
