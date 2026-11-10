/-
# Concrete diagonal occurrences and one-step synchronized newborn cuts

The definitions in this file are on literal words, `Binomial.subst`, and
the complete `Reduction.red`.  They do not assume an abstract transition is
realized by a word occurrence.  `red_split_at_diagonal` retains the actual
factor ordinal, even if several factors have identical word labels.

The Perron-length implication uses rational cubic irreducibility and the
existing cyclic-vector theorem; rational independence is derived.

The scope is a supplied aligned equal-letter occurrence in the inflation of
an irreducible, noncoincident balanced parent.  Full packet refinement,
arbitrary-address common-factor transport, existence of a productive forced
crossing, and global G1 extraction remain separate obligations.

Literature stop/go: `docs/c4-concrete-occurrence-literature-2026-11-10.md`.
-/
import PscVerif.Descendants
import PscVerif.Cyclicity

namespace Psc.OccurrenceNewborn

open Psc.Binomial Psc.Reduction Psc.Descendants Matrix

variable {α : Type*} [DecidableEq α]

/-- A cut inherited from a zero return of the immediate parent.  The index
bound prevents saturated `List.take` from inventing additional old cuts. -/
def InheritedCut (s : α → List α) (u v : List α) (k : ℕ) : Prop :=
  ∃ j ≤ u.length, Equiv1 (u.take j) (v.take j) ∧
    (subst s (u.take j)).length = k

/-- A proper zero return in the one-step image that is not inherited from
the immediate parent. -/
def NewbornCut (s : α → List α) (u v : List α) (k : ℕ) : Prop :=
  0 < k ∧ k < (subst s u).length ∧
    Equiv1 ((subst s u).take k) ((subst s v).take k) ∧
    ¬ InheritedCut s u v k

/-- Equal adjacent letters immediately to the right of a cut. -/
def SyncPlus (u v : List α) (k : ℕ) : Prop :=
  ∃ a u' v', u.drop k = a :: u' ∧ v.drop k = a :: v'

/-- Equal adjacent letters immediately to the left of a cut. -/
def SyncMinus (u v : List α) (k : ℕ) : Prop :=
  ∃ a u' v', u.take k = u' ++ [a] ∧ v.take k = v' ++ [a]

/-- Irreducibility, rather than a newborn premise, excludes inherited
interior cuts.  Nonerasure is not needed for this implication. -/
theorem interior_not_inherited (s : α → List α) {u v : List α}
    (hirr : IrreduciblePair u v) {k : ℕ}
    (hk0 : 0 < k) (hklt : k < (subst s u).length) :
    ¬ InheritedCut s u v k := by
  rintro ⟨j, hj, hbal, hlen⟩
  by_cases hj0 : j = 0
  · subst j
    simp [subst] at hlen
    omega
  by_cases hjend : j = u.length
  · subst j
    simp only [List.take_length] at hlen
    omega
  exact hirr j (by omega) (by omega) hbal

/-- A balanced noncoincident pair has at least two letters on each track. -/
theorem two_le_length_of_noncoincident {u v : List α}
    (hbal : Equiv1 u v) (hne : u ≠ v) : 2 ≤ u.length := by
  cases u with
  | nil =>
    have hv : v = [] := List.length_eq_zero_iff.mp (by simpa using hbal.length_eq.symm)
    exact (hne hv.symm).elim
  | cons a u =>
    cases u with
    | nil =>
      have hv : v = [a] := by simpa using (equiv1_iff_perm.mp hbal).symm
      exact (hne hv.symm).elim
    | cons b u => simp

/-- At an actual aligned equal-letter occurrence, the complete reduction
splits into the prefix reduction, that singleton, and the suffix reduction.
No irreducibility or Pisot assumption is needed for this factorization. -/
theorem red_split_at_diagonal {pu pv su sv : List α} {a : α}
    (hp : Equiv1 pu pv) (hwhole : Equiv1 (pu ++ a :: su) (pv ++ a :: sv)) :
    red (pu ++ a :: su) (pv ++ a :: sv) =
      red pu pv ++ ([a], [a]) :: red su sv := by
  have ht : Equiv1 (a :: su) (a :: sv) := equiv1_cancel hp hwhole
  rw [red_append hp ht]
  congr 1
  simp [red, redAux]

/-- The actual singleton's ordinal is the number of prefix factors.  Word
membership alone would lose this information when a factor is repeated. -/
theorem diagonal_factor_ordinal {pu pv su sv : List α} {a : α}
    (hp : Equiv1 pu pv) (hwhole : Equiv1 (pu ++ a :: su) (pv ++ a :: sv)) :
    (red (pu ++ a :: su) (pv ++ a :: sv))[(red pu pv).length]? =
      some ([a], [a]) := by
  rw [red_split_at_diagonal hp hwhole]
  simp

/-- A literal aligned singleton in the immediate image of an irreducible
noncoincident parent supplies an interior synchronized newborn.  Choose its
left boundary when that boundary is interior; otherwise choose its right
boundary.  The latter case is exactly the `SyncMinus` fallback at cut one. -/
theorem aligned_letter_newborn (s : α → List α) (hs : ∀ a, s a ≠ [])
    {u v pu pv su sv : List α} {a : α}
    (hparent : IsBlock (u, v)) (hne : u ≠ v)
    (hu : subst s u = pu ++ a :: su) (hv : subst s v = pv ++ a :: sv)
    (hp : Equiv1 pu pv) :
    (0 < pu.length ∧ NewbornCut s u v pu.length ∧
      SyncPlus (subst s u) (subst s v) pu.length) ∨
    (pu = [] ∧ NewbornCut s u v 1 ∧
      SyncMinus (subst s u) (subst s v) 1) := by
  have hlen : pu.length = pv.length := hp.length_eq
  have hbig : 2 ≤ (subst s u).length :=
    (two_le_length_of_noncoincident hparent.2.1 hne).trans
      (Psc.FixedPointLimit.length_le_subst s hs u)
  by_cases hpos : 0 < pu.length
  · have hlt : pu.length < (subst s u).length := by simp [hu]
    refine Or.inl ⟨hpos, ⟨hpos, hlt, ?_,
      interior_not_inherited s hparent.2.2 hpos hlt⟩, ?_⟩
    · simpa [hu, hv, hlen] using hp
    · exact ⟨a, su, sv, by simp [hu], by simp [hv, hlen]⟩
  · have hpu : pu = [] := List.length_eq_zero_iff.mp (by omega)
    have hpv : pv = [] := List.length_eq_zero_iff.mp (by rw [← hlen, hpu]; rfl)
    have hlt : 1 < (subst s u).length := by omega
    refine Or.inr ⟨hpu, ⟨by omega, hlt, ?_,
      interior_not_inherited s hparent.2.2 (by omega) hlt⟩, ?_⟩
    · simpa [hu, hv, hpu, hpv] using (show Equiv1 [a] [a] from fun _ => rfl)
    · exact ⟨a, [], [], by simp [hu, hpu], by simp [hv, hpv]⟩

/-- A singleton actually present in the complete child reduction supplies
its concrete prefix/suffix occurrence, then an interior newborn. -/
theorem singleton_child_newborn (s : α → List α) (hs : ∀ a, s a ≠ [])
    {u v : List α} (hparent : IsBlock (u, v)) (hne : u ≠ v) {a : α}
    (hchild : Child s (u, v) ([a], [a])) :
    ∃ k, NewbornCut s u v k ∧
      (SyncPlus (subst s u) (subst s v) k ∨ SyncMinus (subst s u) (subst s v) k) := by
  obtain ⟨pre, post, heq⟩ := List.mem_iff_append.mp hchild
  have hσ := equiv1_subst s hparent.2.1
  have hpre : ∀ T ∈ pre, Equiv1 T.1 T.2 := by
    intro T hT
    exact (red_isBlock hσ T (by rw [heq]; simp [hT])).2.1
  have hu : subst s u = (pre.map Prod.fst).flatten ++
      a :: (post.map Prod.fst).flatten := by
    rw [← red_top hσ.length_eq, heq]
    simp
  have hv : subst s v = (pre.map Prod.snd).flatten ++
      a :: (post.map Prod.snd).flatten := by
    rw [← red_bot hσ.length_eq, heq]
    simp
  rcases aligned_letter_newborn s hs hparent hne hu hv (equiv1_join pre hpre) with
    ⟨_, hn, hp⟩ | ⟨_, hn, hm⟩
  · exact ⟨_, hn, Or.inl hp⟩
  · exact ⟨1, hn, Or.inr hm⟩

/-- A coincident actual child is a singleton by irreducible factorization;
the concrete newborn conclusion follows without an extra singleton premise. -/
theorem coincidence_child_newborn (s : α → List α) (hs : ∀ a, s a ≠ [])
    {T U : List α × List α} (hT : IsBlock T) (hne : T.1 ≠ T.2)
    (hchild : Child s T U) (hco : U.1 = U.2) :
    ∃ k, NewbornCut s T.1 T.2 k ∧
      (SyncPlus (subst s T.1) (subst s T.2) k ∨
        SyncMinus (subst s T.1) (subst s T.2) k) := by
  have hU := red_isBlock (equiv1_subst s hT.2.1) U hchild
  obtain ⟨a, rfl⟩ := eq_coincidence_of_isBlock hU hco
  exact singleton_child_newborn s hs hT hne hchild

/-- A literal child path to coincidence has a reachable noncoincident
immediate parent carrying an interior synchronized newborn.  This traverses
the actual complete child relation, not an unrefined packet relation. -/
theorem child_path_newborn (s : α → List α) (hs : ∀ a, s a ≠ [])
    {T U : List α × List α} (hpath : Relation.ReflTransGen (Child s) T U)
    (hco : U.1 = U.2) (hT : IsBlock T) (hne : T.1 ≠ T.2) :
    ∃ P D k, Relation.ReflTransGen (Child s) T P ∧ IsBlock P ∧ P.1 ≠ P.2 ∧
      Child s P D ∧ D.1 = D.2 ∧
      NewbornCut s P.1 P.2 k ∧
      (SyncPlus (subst s P.1) (subst s P.2) k ∨
        SyncMinus (subst s P.1) (subst s P.2) k) := by
  revert hT hne
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ hne; exact (hne hco).elim
  | @head T V hTV hVU ih =>
    intro hT hne
    by_cases hV : V.1 = V.2
    · obtain ⟨k, hk, hsync⟩ := coincidence_child_newborn s hs hT hne hTV hV
      exact ⟨T, V, k, .refl, hT, hne, hTV, hV, hk, hsync⟩
    · obtain ⟨P, D, k, hVP, hP, hPne, hPD, hD, hk, hsync⟩ :=
        ih (red_isBlock (equiv1_subst s hT.2.1) V hTV) hV
      exact ⟨P, D, k, .head hTV hVP, hP, hPne, hPD, hD, hk, hsync⟩

/-! ## Physical prefix lengths: derive rational independence -/

/-- The physical length of a ternary word for the supplied length row.
This is the row applied to its actual Parikh vector. -/
def physicalLength (ℓ : Fin 3 → ℝ) (w : List (Fin 3)) : ℝ :=
  ℓ ⬝ᵥ fun a => (w.count a : ℝ)

@[simp] theorem physicalLength_nil (ℓ : Fin 3 → ℝ) : physicalLength ℓ [] = 0 := by
  simp [physicalLength, dotProduct]

@[simp] theorem physicalLength_append (ℓ : Fin 3 → ℝ) (u v : List (Fin 3)) :
    physicalLength ℓ (u ++ v) = physicalLength ℓ u + physicalLength ℓ v := by
  simp [physicalLength, dotProduct, List.count_append, Nat.cast_add, mul_add,
    Finset.sum_add_distrib]

@[simp] theorem physicalLength_singleton (ℓ : Fin 3 → ℝ) (a : Fin 3) :
    physicalLength ℓ [a] = ℓ a := by
  simp [physicalLength, dotProduct, List.count_singleton', mul_ite]

theorem physicalLength_nonneg (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 ≤ ℓ a)
    (w : List (Fin 3)) : 0 ≤ physicalLength ℓ w := by
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hℓ a) (Nat.cast_nonneg _)

theorem physicalLength_of_equiv1 (ℓ : Fin 3 → ℝ) {u v : List (Fin 3)}
    (h : Equiv1 u v) : physicalLength ℓ u = physicalLength ℓ v := by
  unfold physicalLength
  congr 1
  funext a
  exact_mod_cast h a

theorem physicalLength_flatten (ℓ : Fin 3 → ℝ) (ws : List (List (Fin 3))) :
    physicalLength ℓ ws.flatten = (ws.map (physicalLength ℓ)).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp [ih]

/-- The actual physical boundary before factor ordinal `j` in a supplied
ordered factor list. -/
def factorBoundary (ℓ : Fin 3 → ℝ)
    (bs : List (List (Fin 3) × List (Fin 3))) (j : ℕ) : ℝ :=
  physicalLength ℓ ((bs.take j).map Prod.fst).flatten

theorem factorBoundary_mono (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 ≤ ℓ a)
    (bs : List (List (Fin 3) × List (Fin 3))) {i j : ℕ} (hij : i ≤ j) :
    factorBoundary ℓ bs i ≤ factorBoundary ℓ bs j := by
  obtain ⟨rest, hrest⟩ := List.take_prefix_take_left (l := bs) hij
  unfold factorBoundary
  rw [← hrest, List.map_append, List.flatten_append, physicalLength_append]
  exact le_add_of_nonneg_right (physicalLength_nonneg ℓ hℓ _)

theorem factorBoundary_succ (ℓ : Fin 3 → ℝ)
    {bs : List (List (Fin 3) × List (Fin 3))} {j : ℕ}
    {T : List (Fin 3) × List (Fin 3)} (h : bs[j]? = some T) :
    factorBoundary ℓ bs (j + 1) = factorBoundary ℓ bs j + physicalLength ℓ T.1 := by
  simp [factorBoundary, List.take_succ, h]

/-- A selected tile in a particular factor occurrence.  `ordinal` is part
of the data; equal word labels at different positions are not identified. -/
structure FactorOccurrence (bs : List (List (Fin 3) × List (Fin 3)))
    (track : List (Fin 3) × List (Fin 3) → List (Fin 3)) where
  ordinal : ℕ
  factor : List (Fin 3) × List (Fin 3)
  atOrdinal : bs[ordinal]? = some factor
  before : List (Fin 3)
  letter : Fin 3
  after : List (Fin 3)
  split : track factor = before ++ letter :: after

def FactorOccurrence.start (ℓ : Fin 3 → ℝ)
    {bs : List (List (Fin 3) × List (Fin 3))}
    {track : List (Fin 3) × List (Fin 3) → List (Fin 3)}
    (o : FactorOccurrence bs track) : ℝ :=
  physicalLength ℓ ((bs.take o.ordinal).map track).flatten + physicalLength ℓ o.before

def FactorOccurrence.finish (ℓ : Fin 3 → ℝ)
    {bs : List (List (Fin 3) × List (Fin 3))}
    {track : List (Fin 3) × List (Fin 3) → List (Fin 3)}
    (o : FactorOccurrence bs track) : ℝ := o.start ℓ + ℓ o.letter

/-- Actual tile bounds lie within their actual factor's common interval.
The equality between track lengths is obtained from each factor's balance. -/
theorem FactorOccurrence.bounds (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 ≤ ℓ a)
    {bs : List (List (Fin 3) × List (Fin 3))}
    {track : List (Fin 3) × List (Fin 3) → List (Fin 3)}
    (htrack : ∀ T ∈ bs, Equiv1 (track T) T.1) (o : FactorOccurrence bs track) :
    factorBoundary ℓ bs o.ordinal ≤ o.start ℓ ∧
      o.finish ℓ ≤ factorBoundary ℓ bs (o.ordinal + 1) := by
  have hprefix : physicalLength ℓ ((bs.take o.ordinal).map track).flatten =
      factorBoundary ℓ bs o.ordinal := by
    simp only [factorBoundary, physicalLength_flatten, List.map_map]
    congr 1
    exact List.map_congr_left fun T hT =>
      physicalLength_of_equiv1 ℓ (htrack T (List.mem_of_mem_take hT))
  have hfactor : physicalLength ℓ o.factor.1 =
      physicalLength ℓ o.before + ℓ o.letter + physicalLength ℓ o.after := by
    rw [← physicalLength_of_equiv1 ℓ (htrack o.factor
      (List.mem_of_getElem? o.atOrdinal)), o.split]
    rw [show o.before ++ o.letter :: o.after = (o.before ++ [o.letter]) ++ o.after by simp]
    simp
  constructor
  · unfold FactorOccurrence.start
    rw [hprefix]
    exact le_add_of_nonneg_right (physicalLength_nonneg ℓ hℓ _)
  · unfold FactorOccurrence.finish FactorOccurrence.start
    rw [hprefix, factorBoundary_succ ℓ o.atOrdinal, hfactor]
    linarith [physicalLength_nonneg ℓ hℓ o.after]

/-- Tiles with a strictly common interior, already realized as selected
occurrences in a balanced factorization, must belong to the same ordinal.
A boundary touch is deliberately insufficient. -/
theorem common_factor_ordinal (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 ≤ ℓ a)
    {bs : List (List (Fin 3) × List (Fin 3))}
    (hbs : ∀ T ∈ bs, Equiv1 T.1 T.2)
    (top : FactorOccurrence bs Prod.fst) (bot : FactorOccurrence bs Prod.snd)
    (hoverlap : ∃ x, top.start ℓ < x ∧ x < top.finish ℓ ∧
      bot.start ℓ < x ∧ x < bot.finish ℓ) : top.ordinal = bot.ordinal := by
  obtain ⟨x, hts, htf, hbs', hbf⟩ := hoverlap
  obtain ⟨htlo, hthi⟩ := top.bounds ℓ hℓ (fun _ _ _ => rfl)
  obtain ⟨hblo, hbhi⟩ := bot.bounds ℓ hℓ (fun T hT a => (hbs T hT a).symm)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := factorBoundary_mono ℓ hℓ bs (Nat.succ_le_of_lt hlt)
    linarith
  · have := factorBoundary_mono ℓ hℓ bs (Nat.succ_le_of_lt hgt)
    linarith

/-- Common-factor containment specialized to the repository's complete
zero-return reduction.  Both ordinal and factor label are preserved. -/
theorem red_common_factor (ℓ : Fin 3 → ℝ) (hℓ : ∀ a, 0 < ℓ a)
    {u v : List (Fin 3)} (hbal : Equiv1 u v)
    (top : FactorOccurrence (red u v) Prod.fst)
    (bot : FactorOccurrence (red u v) Prod.snd)
    (hoverlap : ∃ x, top.start ℓ < x ∧ x < top.finish ℓ ∧
      bot.start ℓ < x ∧ x < bot.finish ℓ) :
    top.ordinal = bot.ordinal ∧ top.factor = bot.factor := by
  have hi := common_factor_ordinal ℓ (fun a => (hℓ a).le)
    (fun T hT => (red_isBlock hbal T hT).2.1) top bot hoverlap
  refine ⟨hi, ?_⟩
  have h := top.atOrdinal
  rw [hi, bot.atOrdinal] at h
  exact (Option.some.inj h).symm

/-- A nonzero left eigenrow of a rational matrix with irreducible cubic
characteristic polynomial annihilates no nonzero rational vector. -/
theorem rational_length_injective (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hℓ : ℓ ᵥ* M.map (algebraMap ℚ ℝ) = β • ℓ) (hℓ0 : ℓ ≠ 0)
    (w : Fin 3 → ℚ) (hw : ℓ ⬝ᵥ (algebraMap ℚ ℝ ∘ w) = 0) : w = 0 := by
  by_contra hw0
  exact hℓ0 (Psc.ConcentrationAlgebra.eigenrow_eq_zero M
    (Psc.Cyclicity.cyclic_of_irreducible M hM) ℓ β hℓ w hw0 hw)

/-- Equality of physical prefix lengths is equivalent to equality of their
actual Parikh columns.  No independent rational-independence axiom occurs. -/
theorem physicalLength_eq_iff (M : Matrix (Fin 3) (Fin 3) ℚ)
    (hM : Irreducible M.charpoly) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hℓ : ℓ ᵥ* M.map (algebraMap ℚ ℝ) = β • ℓ) (hℓ0 : ℓ ≠ 0)
    (u v : List (Fin 3)) : physicalLength ℓ u = physicalLength ℓ v ↔ Equiv1 u v := by
  constructor
  · intro h
    let w : Fin 3 → ℚ := fun a => (u.count a : ℚ) - (v.count a : ℚ)
    have hw : ℓ ⬝ᵥ (algebraMap ℚ ℝ ∘ w) = 0 := by
      have heq : algebraMap ℚ ℝ ∘ w =
          (fun a => (u.count a : ℝ)) - (fun a => (v.count a : ℝ)) := by
        ext a
        simp [w]
      rw [heq, dotProduct_sub]
      exact sub_eq_zero.mpr h
    have hz := rational_length_injective M hM ℓ β hℓ hℓ0 w hw
    intro a
    have ha := congrFun hz a
    change (u.count a : ℚ) - (v.count a : ℚ) = 0 at ha
    exact_mod_cast sub_eq_zero.mp ha
  · intro h
    unfold physicalLength
    congr 1
    funext a
    exact_mod_cast h a

/-- The geometric-to-word bridge for a supplied actual occurrence in one
inflation.  The matrix is the substitution's own incidence matrix. -/
theorem physical_diagonal_newborn (s : Fin 3 → List (Fin 3))
    (hs : ∀ a, s a ≠ [])
    (hM : Irreducible ((Psc.Incidence.inc s).map (Nat.castRingHom ℚ)).charpoly)
    (ℓ : Fin 3 → ℝ) (β : ℝ) (hpos : ∀ a, 0 < ℓ a)
    (hℓ : ℓ ᵥ* (((Psc.Incidence.inc s).map (Nat.castRingHom ℚ)).map
      (algebraMap ℚ ℝ)) = β • ℓ)
    {u v pu pv su sv : List (Fin 3)} {a : Fin 3}
    (hparent : IsBlock (u, v)) (hne : u ≠ v)
    (hu : subst s u = pu ++ a :: su) (hv : subst s v = pv ++ a :: sv)
    (halign : physicalLength ℓ pu = physicalLength ℓ pv) :
    (red (subst s u) (subst s v))[(red pu pv).length]? = some ([a], [a]) ∧
    ((0 < pu.length ∧ NewbornCut s u v pu.length ∧
      SyncPlus (subst s u) (subst s v) pu.length) ∨
    (pu = [] ∧ NewbornCut s u v 1 ∧
      SyncMinus (subst s u) (subst s v) 1)) := by
  have hℓ0 : ℓ ≠ 0 := by
    intro h0
    have := hpos 0
    simp [h0] at this
  have hp := (physicalLength_eq_iff _ hM ℓ β hℓ hℓ0 pu pv).mp halign
  refine ⟨?_, aligned_letter_newborn s hs hparent hne hu hv hp⟩
  rw [hu, hv]
  exact diagonal_factor_ordinal hp (by
    rw [← hu, ← hv]
    exact equiv1_subst s hparent.2.1)

/-! ## Hypothesis and orientation controls -/

/-- A nonerasing local control with an initial equal singleton. -/
def leftBoundaryControl : Fin 2 → List (Fin 2) :=
  fun a => if a = 0 then [0] else [0, 1]

/-- The left exterior singleton is extracted at its right, interior
boundary as `SyncMinus`; choosing the exterior cut zero would be wrong. -/
theorem left_boundary_syncMinus_control :
    NewbornCut leftBoundaryControl [0, 1] [1, 0] 1 ∧
      SyncMinus (subst leftBoundaryControl [0, 1])
        (subst leftBoundaryControl [1, 0]) 1 := by
  have h := aligned_letter_newborn leftBoundaryControl (by decide)
    (u := [0, 1]) (v := [1, 0]) (pu := []) (pv := [])
    (su := [0, 1]) (sv := [1, 0]) (a := 0)
    (by unfold IsBlock; decide) (by decide) (by decide) (by decide) (by decide)
  simpa using h

/-- With erasure the image can be a singleton, so it has no interior
newborn even though the immediate parent is balanced and noncoincident. -/
def erasingControl : Fin 2 → List (Fin 2) := fun a => if a = 0 then [0] else []

theorem erasing_control_no_newborn :
    IsBlock ([0, 1], [1, 0] : List (Fin 2) × List (Fin 2)) ∧
    subst erasingControl [0, 1] = [0] ∧ subst erasingControl [1, 0] = [0] ∧
    ¬ ∃ k, NewbornCut erasingControl [0, 1] [1, 0] k := by
  refine ⟨by unfold IsBlock; decide, by decide, by decide, ?_⟩
  rintro ⟨k, h0, hlt, _⟩
  norm_num [subst, erasingControl] at hlt
  omega

/-- An interior synchronized cut can be inherited when the parent is
reducible, even if the two parent words are distinct. -/
theorem reducible_parent_inherited_control :
    InheritedCut (fun a : Fin 2 => [a]) [0, 1, 0] [0, 0, 1] 1 ∧
    ¬ NewbornCut (fun a : Fin 2 => [a]) [0, 1, 0] [0, 0, 1] 1 := by
  have h : InheritedCut (fun a : Fin 2 => [a]) [0, 1, 0] [0, 0, 1] 1 :=
    ⟨1, by decide, by decide, by decide⟩
  exact ⟨h, fun hn => hn.2.2.2 h⟩

/-- Equal physical lengths alone do not give Parikh equality when rational
independence is absent.  Unit lengths identify the one-letter words. -/
theorem dependent_lengths_control :
    physicalLength (fun _ => 1) [0] = physicalLength (fun _ => 1) [1] ∧
    ¬ Equiv1 ([0] : List (Fin 3)) [1] := by
  exact ⟨by simp, by decide⟩

end Psc.OccurrenceNewborn
