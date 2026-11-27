/-
# FC2: the orientation transfer on property (F), with no rank input

`docs/c4-fc2-orientation-2026-11-17.md` §2–§4; `docs/c4-geometric-f-class-2026-11-16.md` §4.1
(states over `0`, (St)), §4.2 (Theorem FC2, Corollary E); `docs/c4-fc2-rank-transfer-review-2026-11-16.md`
§2, §3.  `PscVerif.GeometricFRank` reduces the zero-slice rank to letter families and takes
**two** geometric inputs, the zero-slice rank realisations `IsMaximumSize (StateFamily s L) c`
and `IsMaximumSize (StateFamily (reverseSubstitution s) L) c` for one common `c`, the second
from reflection of full BBK strands.  This module proves, with no rank input at all, that on
property (F) the integer zero-slice maximum exists and is the same number in all four forms:
zero-slice state families of `σ` and of `σ^R`, left and right letter families.  The only
geometric input FC2 (2) still needs is therefore one-sided: that the BBK coincidence rank is
the zero-slice maximum of `σ` (BBK Remark 4.3 at `q = 0` with the full return lattice).

**Setting.**  That of `PscVerif.GeometricFRank`: `α` a finite alphabet, `s : α → List α`,
`M = incZ s`, an additive length functional `L : (α → ℤ) →+ ℝ`, integer edges `(a, x)`
(`IntegralEdge`), `EdgeDescendant`, `EdgeCoincident` (a labelled edge shared at a common
level), `VertexCoincident` (left strong coincidence), `RightStrongCoincidenceWitness`,
`reverseSubstitution`, `StateFamily`, `LetterFamily`, `IsMaximumSize`.

**The argument.**  (T) A common integer translation `u` preserves `EdgeCoincident`: the
descendants of `(a, x + u)` are those of `(a, x)` shifted by `Mⁿ u`.  (D) `u = e_{a₀}` for a
shortest letter `a₀` has `0 < L u ≤ L e_a` for every `a`; since the zero slice is left-closed
(`0 ≤ ℓ·v < ℓ_a`), that is all the shift has to do.  (LR) The vertex edges `(c, 0)` of a left
family reflect to the edges `(c, −e_c)` of `σ^R`, still pairwise non-coincident; translated by
`u` they are the edges of the states `(c, e_c − u)` of `σ^R`; under (F) for `σ^R` they are
absorbed into vertex states of `σ^R`, i.e. a left family of `σ^R`, i.e. a right family of `σ`.
Symmetrically right families give left families.  (MAX) `EdgeCoincident` is reflexive, so a
letter family is injective and has at most `|α|` members; with (LR) and the absorption of
`PscVerif.GeometricFRank` every family in the four forms has the size of a left letter family.

**Proved here, in full** (axioms: a subset of `propext`, `Classical.choice`, `Quot.sound`):
* (T) `edgeDescendant_translate`, `edgeCoincident_translate`, **`edgeCoincident_translate_iff`**;
  reflexivity and symmetry: `edgeCoincident_refl`, `edgeCoincident_symm`,
  `rightStrongCoincidenceWitness_refl`, `rightStrongCoincidenceWitness_symm`, with
  `edgeDescendant_zero` and `vertexCoincident_iff_strongCoincidenceWitness`;
* (D) `exists_letter_shift`; (D′) `exists_small_length` (`L` injective, `|α| ≥ 2`: the length
  group is dense);
* families: `LetterFamily.le_card`, `letterFamily_zero`, `letterFamily_one`,
  `exists_isMaximumSize`, `IsMaximumSize.unique`, `isMaximumSize_one_iff` (for a reflexive
  symmetric relation, rank one iff all pairs related);
* **`stateFamily_reverse_of_leftLetterFamily`**, `stateFamily_of_rightLetterFamily` (right
  families embed in the zero slice of `σ` itself): no (F), no contraction, no injectivity;
* reflection of arbitrary zero-slice families, no (F): **`stateFamily_reverse_of_stateFamily`**,
  `stateFamily_reverse_iff`, **`isMaximumSize_stateFamily_reverse_iff`** (the reversed rank
  realisation is equivalent to the direct one: the integer content of `cr(σ^R) = cr(σ)`);
* (LR) **`rightLetterFamily_of_leftLetterFamily`** ((F) for `σ^R`),
  **`leftLetterFamily_of_rightLetterFamily`** ((F) for `σ`);
* (MAX) **`fc2_integer_rank_of_reverse`**: under length data, contraction data and (F) for `σ`
  and for `σ^R`, there is `r` with `1 ≤ r ≤ |α|` that is the maximum in all four forms;
  **`fc2_integer_rank`**: the same with (F) for `σ` and `L` injective on `ℤ^α`;
  **`fc2_rank_transfer_one_sided`**: `fc2_rank_transfer` of `PscVerif.GeometricFRank` with the
  reversed rank realisation dropped; `fc2_rank_lower_bounds_one_sided` (FC2 (1), no (F), one
  rank input, positivity only); **`leftAll_iff_rightAll`** (Corollary E (ii) ⟺ (iii): all pairs
  left strongly coincident iff all pairs right strongly coincident);
* (Z) injectivity of `L` from the standing hypotheses: `lenHom_zero_of_pos_eigen`, a wrapper
  around round 4's `Psc.GeometricFLemmas.lenHom_eq_zero_iff` (Lemma 1 (1));
* on the standing class: **`fc2_integer_rank_of_primitive_pisot`**,
  **`fc1_right_of_primitive_pisot`** (Theorem FC1 with right strong coincidence: a strict system
  exists iff some pair of distinct letters has no right strong-coincidence witness),
  `fc2_integer_rank_pip3`; **`fc2_pip3_rank_le_two`** (three letters, with one Barge–Diamond pair
  as hypothesis: `1 ≤ r ≤ 2` in all four forms, and `σ` has a strict system iff `r = 2`);
* non-vacuity: **`trib_right_all`** (every pair of Tribonacci letters is right strongly
  coincident, obtained from the transfer) cross-checked by explicit right witnesses on words
  (`trib_right_witness_01`, `_02`, `_12`, at levels 4, 4, 3), and `trib_integer_rank_one`;
  at rank two, outside PIP3: **`tm_integer_rank_two`** (Thue–Morse `01/10`, where `ℓ = (1, 1)` is
  not injective, through `fc2_integer_rank_of_reverse`; `tm_reverse_propertyF` by
  `propertyF_of_mulVec_state_eq_zero` and `tm_mulVec_state`);
* counter-calibration: **`bd_left_two_right_one`** (Barge–Diamond's `φ = 010/110`: `ν_L = 2`,
  `ν_R = 1`; `bd_power`, `bd_not_left`, `bd_right`).  Length data exist (`bd_lengthData`);
  contraction data fail for `β > 1` (`bd_not_contractionData`), (F) fails for `φ` and for `φ^R`
  (`bd_not_propertyF`, `bd_reverse_not_propertyF`), and `ℓ` is not injective: the example shows
  that the hypotheses of the transfer cannot all be dropped, not which one is needed.

**Hypotheses and where they enter.**  In the transfer (letter families, `fc2_integer_rank*`):
injectivity of `L` on `ℤ^α` (`hzero`) only passes (F) from `σ` to `σ^R` (`propertyF_reverse_iff`),
which the direction left ⟹ right needs, and it is not necessary for that (Thue–Morse); (F) and
contraction data enter only in the absorption step (`leftLetterFamily_of_stateFamily`), and the
embeddings into the zero slice need neither; length data give the positivity of tile lengths in
the state inequalities and enter through the absorption; a nonempty alphabet gives `r ≥ 1`.  The
reflection of arbitrary families (`stateFamily_reverse_of_stateFamily` and its corollaries) uses
injectivity of `L` and at least two letters, for density (`exists_small_length`).  (Z) uses
irreducibility of `χ_M` and a positive left eigen-row only (round 4's Lemma 1 (1)); at least two
letters enter the standing-class theorems through `β > 1` (`fc1_hypotheses_of_primitive_pisot`).
The Pisot hypothesis enters only through contraction data.  On three letters, the bound
`r ≤ 2` uses one left strongly coincident pair of distinct letters as a hypothesis (Barge–Diamond
2002, Theorem 1, not formalised).

**Prior art** (the stop/go record of the note).  (T) is the translation equivariance of
coincidence (Barge–Kwapisz 2006, (7.3)); (D′) is the density step in the proofs of BBK
Remark 4.3 and Minervino–Thuswaldner Lemma 9.1; injectivity of `ℓ` is Akiyama–Lee 2014
Lemma 4.3 (by a Galois argument; here round 4's cyclic-vector proof).  `ν_L = ν_R` on (F) was not
found in the sources read; for unit `σ` its rank-one case follows by composing printed results.

**Not proved here.**  That the BBK coincidence rank equals the zero-slice maximum (BBK Def. 4.1,
Remark 4.3 at `q = 0`, the full return lattice: Lemma 6 of the class note); it is the one
geometric input left, and the consequence `cr = ν_L = ν_R` is conditional on it.  The bound
`ν_L ≤ |α| − 1` (Barge–Diamond 2002, Theorem 1).  The spectral statements (BBK Cor. 5.2).
(F) for any three-letter specimen other than Tribonacci (it is proved for the two-letter
Fibonacci and Thue–Morse `01/10`, `10/01`).  Excluding rank two on (F).  Universal C4 is open.
-/
import PscVerif.GeometricFLemmas

namespace Psc.GeometricF

open Matrix Polynomial Psc.Binomial Psc.Incidence

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ### (T) Common translation, reflexivity and symmetry -/

theorem edgeDescendant_translate {s : α → List α} {n : ℕ} {x y : IntegralEdge α} (u : α → ℤ)
    (h : EdgeDescendant s n x y) :
    EdgeDescendant s n (x.1, x.2 + u) (y.1, y.2 + incZ s ^ n *ᵥ u) := by
  obtain ⟨P, Q, hw, hy⟩ := h
  refine ⟨P, Q, hw, ?_⟩
  change y.2 + incZ s ^ n *ᵥ u = incZ s ^ n *ᵥ (x.2 + u) + pvec P
  rw [hy, Matrix.mulVec_add]
  abel

theorem edgeCoincident_translate {s : α → List α} {x y : IntegralEdge α} (u : α → ℤ)
    (h : EdgeCoincident s x y) : EdgeCoincident s (x.1, x.2 + u) (y.1, y.2 + u) := by
  obtain ⟨n, z, hx, hy⟩ := h
  exact ⟨n, (z.1, z.2 + incZ s ^ n *ᵥ u), edgeDescendant_translate u hx,
    edgeDescendant_translate u hy⟩

/-- **(T)** A common integer translation preserves eventual coincidence of edges. -/
theorem edgeCoincident_translate_iff {s : α → List α} {x y : IntegralEdge α} (u : α → ℤ) :
    EdgeCoincident s (x.1, x.2 + u) (y.1, y.2 + u) ↔ EdgeCoincident s x y := by
  refine ⟨fun h => ?_, edgeCoincident_translate u⟩
  simpa using edgeCoincident_translate (-u) h

theorem edgeDescendant_zero (s : α → List α) (x : IntegralEdge α) : EdgeDescendant s 0 x x :=
  ⟨[], [], by simp [power], by simp⟩

theorem edgeCoincident_refl (s : α → List α) (x : IntegralEdge α) : EdgeCoincident s x x :=
  ⟨0, x, edgeDescendant_zero s x, edgeDescendant_zero s x⟩

theorem edgeCoincident_symm {s : α → List α} {x y : IntegralEdge α} :
    EdgeCoincident s x y → EdgeCoincident s y x := by
  rintro ⟨n, z, hx, hy⟩
  exact ⟨n, z, hy, hx⟩

theorem rightStrongCoincidenceWitness_refl (s : α → List α) (a : α) :
    RightStrongCoincidenceWitness s a a :=
  vertexCoincident_reverse_iff.mp (edgeCoincident_refl _ _)

theorem rightStrongCoincidenceWitness_symm {s : α → List α} {a b : α} :
    RightStrongCoincidenceWitness s a b → RightStrongCoincidenceWitness s b a := by
  rw [← vertexCoincident_reverse_iff, ← vertexCoincident_reverse_iff]
  exact edgeCoincident_symm

/-! ### (D) The shift by a shortest letter -/

omit [Fintype α] in
/-- **(D)** A shortest letter `a₀`: its Parikh vector `u = e_{a₀}` has `0 < L u ≤ L e_a` for
every letter `a`.  Because the zero slice is left-closed, this shift suffices; no density of
the length group is needed. -/
theorem exists_letter_shift [Finite α] [Nonempty α] {L : (α → ℤ) →+ ℝ}
    (hpos : ∀ a, 0 < L (pvec [a])) : ∃ u : α → ℤ, 0 < L u ∧ ∀ a, L u ≤ L (pvec [a]) := by
  obtain ⟨a₀, h₀⟩ := Finite.exists_min fun a : α => L (pvec [a])
  exact ⟨pvec [a₀], hpos a₀, h₀⟩

omit [Fintype α] in
/-- **(D′) Density.**  If the length functional is injective on integer vectors and there are at
least two letters, some integer vector has length in `(0, ε)` for every `ε > 0`: a cyclic value
group would make the lengths of two distinct letters commensurable, against injectivity.  Used
only for the reflection of arbitrary zero-slice families (`stateFamily_reverse_of_stateFamily`);
the letter-family transfer needs only `exists_letter_shift`. -/
theorem exists_small_length [Nontrivial α] {L : (α → ℤ) →+ ℝ}
    (hpos : ∀ a, 0 < L (pvec [a])) (hzero : ∀ v, L v = 0 → v = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : α → ℤ, 0 < L u ∧ L u < ε := by
  rcases L.range.dense_or_cyclic with hd | ⟨g, hg⟩
  · obtain ⟨t, ⟨u, rfl⟩, ht⟩ := hd.exists_between hε
    exact ⟨u, ht.1, ht.2⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    have hmem (c : α) : ∃ k : ℤ, k • g = L (pvec [c]) := by
      have h : L (pvec [c]) ∈ L.range := ⟨_, rfl⟩
      rw [hg, AddSubgroup.mem_closure_singleton] at h
      exact h
    obtain ⟨ka, hka⟩ := hmem a
    obtain ⟨kb, hkb⟩ := hmem b
    have hv := hzero (kb • pvec [a] - ka • pvec [b]) (by
      rw [map_sub, map_zsmul, map_zsmul, ← hka, ← hkb, smul_smul, smul_smul, mul_comm,
        sub_self])
    have hva := congrFun hv a
    simp [pvec, Ne.symm hab] at hva
    have := hpos b
    rw [← hkb, hva, zero_smul] at this
    exact lt_irrefl _ this

/-! ### Finite families -/

omit [DecidableEq α] in
/-- A family of letters pairwise unrelated by a reflexive relation is injective. -/
theorem LetterFamily.le_card {C : α → α → Prop} (hC : ∀ a, C a a) {n : ℕ}
    (h : LetterFamily C n) : n ≤ Fintype.card α := by
  obtain ⟨a, ha⟩ := h
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    exact ha hne (by rw [hij]; exact hC _)
  simpa using Fintype.card_le_of_injective a hinj

omit [DecidableEq α] [Fintype α] in
theorem letterFamily_zero (C : α → α → Prop) : LetterFamily C 0 :=
  ⟨Fin.elim0, fun i => i.elim0⟩

omit [DecidableEq α] [Fintype α] in
theorem letterFamily_one [Nonempty α] (C : α → α → Prop) : LetterFamily C 1 :=
  ⟨fun _ => Classical.arbitrary α, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩

/-- A family property with the empty family and a uniform bound has a maximum size. -/
theorem exists_isMaximumSize {family : ℕ → Prop} {B : ℕ} (h0 : family 0)
    (hB : ∀ ⦃n⦄, family n → n ≤ B) : ∃ r, IsMaximumSize family r := by
  classical
  exact ⟨Nat.findGreatest family B, Nat.findGreatest_spec (Nat.zero_le B) h0,
    fun n hn => Nat.le_findGreatest (hB hn) hn⟩

theorem IsMaximumSize.unique {family : ℕ → Prop} {r r' : ℕ} (h : IsMaximumSize family r)
    (h' : IsMaximumSize family r') : r = r' :=
  le_antisymm (h'.2 h.1) (h.2 h'.1)

omit [DecidableEq α] [Fintype α] in
/-- For a reflexive symmetric relation, the maximum letter-family size is one iff all pairs of
distinct letters are related. -/
theorem isMaximumSize_one_iff [Nonempty α] {C : α → α → Prop} (hrefl : ∀ a, C a a)
    (hsymm : ∀ a b, C a b → C b a) :
    IsMaximumSize (LetterFamily C) 1 ↔ ∀ a b, a ≠ b → C a b := by
  constructor
  · intro h a b hab
    by_contra hc
    have h2 : LetterFamily C 2 := by
      refine ⟨![a, b], ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hc
      · exact fun h => hc (hsymm _ _ h)
      · exact absurd rfl hij
    exact absurd (h.2 h2) (by norm_num)
  · intro h
    refine ⟨letterFamily_one C, fun n hn => ?_⟩
    by_contra hlt
    obtain ⟨a, ha⟩ := hn
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    refine ha h01 ?_
    by_cases he : a ⟨0, by omega⟩ = a ⟨1, by omega⟩
    · rw [he]; exact hrefl _
    · exact h _ _ he

/-! ### Embeddings of letter families into the zero slice (no (F)) -/

section Embed

variable {s : α → List α} {L : (α → ℤ) →+ ℝ}

/-- **A left letter family of `σ` is a zero-slice state family of `σ^R`.**  The vertex edges
`(c, 0)` reflect to `(c, −e_c)`, which a common translation by `u = e_{a₀}`, `a₀` a shortest letter,
turns into the edges of the states `(c, e_c − u)`.  No (F), no injectivity of `L`. -/
theorem stateFamily_reverse_of_leftLetterFamily [Nonempty α]
    (hpos : ∀ a, 0 < L (pvec [a])) {n : ℕ}
    (h : LetterFamily (VertexCoincident s) n) : StateFamily (reverseSubstitution s) L n := by
  obtain ⟨u, hu0, hu⟩ := exists_letter_shift hpos
  obtain ⟨a, ha⟩ := h
  refine ⟨fun i => (a i, pvec [a i] - u), fun i => ⟨?_, ?_⟩, ?_⟩
  · change 0 ≤ L (pvec [a i] - u)
    rw [map_sub]
    linarith [hu (a i)]
  · change L (pvec [a i] - u) < L (pvec [a i])
    rw [map_sub]
    linarith
  · intro i j hij hc
    apply ha hij
    have e (c : α) : edgeOfState ((c, pvec [c] - u) : IntegralEdge α) =
        ((reflectEdge ((c, 0) : IntegralEdge α)).1,
          (reflectEdge ((c, 0) : IntegralEdge α)).2 + u) := by
      refine Prod.ext rfl ?_
      change -(pvec [c] - u) = -(0 : α → ℤ) - pvec [c] + u
      abel
    rw [e, e, edgeCoincident_translate_iff] at hc
    exact edgeCoincident_reflect_iff.mp hc

/-- **A right letter family of `σ` is a zero-slice state family of `σ` itself.**  No (F). -/
theorem stateFamily_of_rightLetterFamily [Nonempty α]
    (hpos : ∀ a, 0 < L (pvec [a])) {n : ℕ}
    (h : LetterFamily (RightStrongCoincidenceWitness s) n) : StateFamily s L n := by
  simpa using stateFamily_reverse_of_leftLetterFamily (s := reverseSubstitution s) hpos
    (rightLetterFamily_iff_reverse.mp h)

end Embed

/-! ### Reflection of arbitrary zero-slice families (no (F)): the integer content of step (c) -/

section Reflect

variable {s : α → List α} {L : (α → ℤ) →+ ℝ}

/-- **Every zero-slice family of `σ` reflects to one of `σ^R`.**  The edge `(a, −v)` of a state
`(a, v)` reflects to `(a, v − e_a)`, which crosses the slice at its end point when `v = 0`; a
common translation by `u` with `0 < L u ≤ min_i (ℓ_{a_i} − ℓ·v_i)` (density, `exists_small_length`)
makes all of them the edges of states `(a_i, e_{a_i} − v_i − u)` of `σ^R`.  No (F), no
contraction; `L` injective and at least two letters. -/
theorem stateFamily_reverse_of_stateFamily [Nontrivial α]
    (hpos : ∀ a, 0 < L (pvec [a])) (hzero : ∀ v, L v = 0 → v = 0) {n : ℕ}
    (h : StateFamily s L n) : StateFamily (reverseSubstitution s) L n := by
  obtain ⟨x, hx, hsep⟩ := h
  have hgap : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ L (pvec [(x i).1]) - L (x i).2 := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i₀, h₀⟩ := Finite.exists_min fun i => L (pvec [(x i).1]) - L (x i).2
      exact ⟨_, sub_pos.mpr (hx i₀).2, h₀⟩
  obtain ⟨δ, hδ, hδi⟩ := hgap
  obtain ⟨u, hu0, huδ⟩ := exists_small_length hpos hzero hδ
  refine ⟨fun i => ((x i).1, pvec [(x i).1] - (x i).2 - u), fun i => ⟨?_, ?_⟩, ?_⟩
  · change 0 ≤ L (pvec [(x i).1] - (x i).2 - u)
    rw [map_sub, map_sub]
    linarith [hδi i]
  · change L (pvec [(x i).1] - (x i).2 - u) < L (pvec [(x i).1])
    rw [map_sub, map_sub]
    linarith [(hx i).1]
  · intro i j hij hc
    apply hsep hij
    have e (y : IntegralEdge α) :
        edgeOfState ((y.1, pvec [y.1] - y.2 - u) : IntegralEdge α) =
          ((reflectEdge (edgeOfState y)).1, (reflectEdge (edgeOfState y)).2 + u) := by
      refine Prod.ext rfl ?_
      change -(pvec [y.1] - y.2 - u) = -(-y.2) - pvec [y.1] + u
      abel
    rw [e, e, edgeCoincident_translate_iff] at hc
    exact edgeCoincident_reflect_iff.mp hc

/-- The zero-slice families of `σ` and of `σ^R` have the same sizes (`L` injective, `|α| ≥ 2`). -/
theorem stateFamily_reverse_iff [Nontrivial α]
    (hpos : ∀ a, 0 < L (pvec [a])) (hzero : ∀ v, L v = 0 → v = 0) {n : ℕ} :
    StateFamily (reverseSubstitution s) L n ↔ StateFamily s L n :=
  ⟨fun h => by
    simpa using stateFamily_reverse_of_stateFamily (s := reverseSubstitution s) hpos hzero h,
    stateFamily_reverse_of_stateFamily hpos hzero⟩

/-- **The reversed rank realisation follows from the direct one**, for every `σ` with `L`
injective on `ℤ^α` and at least two letters, with no (F): the hypothesis `hRankRev` of
`fc2_rank_transfer` and `fc2_rank_lower_bounds` is a consequence of `hRank`.  This is the
integer content of the reflection of strands (`cr(σ^R) = cr(σ)`), at `q = 0`. -/
theorem isMaximumSize_stateFamily_reverse_iff [Nontrivial α]
    (hpos : ∀ a, 0 < L (pvec [a])) (hzero : ∀ v, L v = 0 → v = 0) {c : ℕ} :
    IsMaximumSize (StateFamily (reverseSubstitution s) L) c ↔
      IsMaximumSize (StateFamily s L) c := by
  have e : StateFamily (reverseSubstitution s) L = StateFamily s L :=
    funext fun _ => propext (stateFamily_reverse_iff hpos hzero)
  rw [e]

end Reflect

/-! ### (LR) The orientation transfer on (F) -/

section Transfer

variable {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ} {ν : (α → ℤ) → ℝ} {ρ : ℝ}

/-- **(LR)** On (F) for `σ^R`, a family of `n` letters pairwise not left strongly coincident
gives `n` letters pairwise not right strongly coincident: reflect, shift into the zero slice of
`σ^R`, absorb. -/
theorem rightLetterFamily_of_leftLetterFamily [Nonempty α]
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ)
    (hFrev : PropertyF (reverseSubstitution s) L) {n : ℕ}
    (h : LetterFamily (VertexCoincident s) n) :
    LetterFamily (RightStrongCoincidenceWitness s) n :=
  rightLetterFamily_iff_reverse.mpr <|
    leftLetterFamily_of_stateFamily hL.reverseSubstitution hC.reverseSubstitution hFrev
      (stateFamily_reverse_of_leftLetterFamily hL.pos h)

/-- **(LR), converse.** On (F) for `σ`, right families give left families of the same size:
shift into the zero slice of `σ`, absorb. -/
theorem leftLetterFamily_of_rightLetterFamily [Nonempty α]
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ) (hF : PropertyF s L) {n : ℕ}
    (h : LetterFamily (RightStrongCoincidenceWitness s) n) :
    LetterFamily (VertexCoincident s) n :=
  leftLetterFamily_of_stateFamily hL hC hF (stateFamily_of_rightLetterFamily hL.pos h)

/-- **(MAX), with (F) on both sides.**  Under length data, contraction data and (F) for `σ` and
for `σ^R`, on a nonempty alphabet, there is one number `r`, `1 ≤ r ≤ |α|`, that is the maximum
size of a pairwise non-coincident family of zero-slice states of `σ`, of zero-slice states of
`σ^R`, of letters pairwise not left strongly coincident, and of letters pairwise not right
strongly coincident.  Injectivity of `L` is not needed in this form. -/
theorem fc2_integer_rank_of_reverse [Nonempty α]
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ) (hF : PropertyF s L)
    (hFrev : PropertyF (reverseSubstitution s) L) :
    ∃ r, 1 ≤ r ∧ r ≤ Fintype.card α ∧
      IsMaximumSize (StateFamily s L) r ∧
      IsMaximumSize (StateFamily (reverseSubstitution s) L) r ∧
      IsMaximumSize (LetterFamily (VertexCoincident s)) r ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) r := by
  have hle : ∀ ⦃n⦄, LetterFamily (VertexCoincident s) n → n ≤ Fintype.card α :=
    fun n hn => LetterFamily.le_card (C := VertexCoincident s) (fun a => edgeCoincident_refl s _) hn
  obtain ⟨r, hr⟩ := exists_isMaximumSize (letterFamily_zero _) hle
  refine ⟨r, hr.2 (letterFamily_one _), hle hr.1,
    ⟨stateFamily_of_leftLetterFamily hL.pos hr.1,
      fun n hn => hr.2 (leftLetterFamily_of_stateFamily hL hC hF hn)⟩,
    ⟨stateFamily_reverse_of_leftLetterFamily hL.pos hr.1,
      fun n hn => hr.2 (leftLetterFamily_of_rightLetterFamily hL hC hF
        (rightLetterFamily_iff_reverse.mpr (leftLetterFamily_of_stateFamily
          hL.reverseSubstitution hC.reverseSubstitution hFrev hn)))⟩,
    hr,
    ⟨rightLetterFamily_of_leftLetterFamily hL hC hFrev hr.1,
      fun n hn => hr.2 (leftLetterFamily_of_rightLetterFamily hL hC hF hn)⟩⟩

/-- **(MAX), FC2 (2) in integer form, with no rank input.**  Under length data, contraction
data, injectivity of `L` on integer vectors and (F), on a nonempty alphabet, there is one
number `r`, `1 ≤ r ≤ |α|`, that is the maximum size of a pairwise non-coincident family of
zero-slice states of `σ`, of zero-slice states of `σ^R`, of letters pairwise not left strongly
coincident, and of letters pairwise not right strongly coincident.  Injectivity passes (F) to
`σ^R` (`propertyF_reverse_iff`). -/
theorem fc2_integer_rank [Nonempty α]
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ)
    (hzero : ∀ v, L v = 0 → v = 0) (hF : PropertyF s L) :
    ∃ r, 1 ≤ r ∧ r ≤ Fintype.card α ∧
      IsMaximumSize (StateFamily s L) r ∧
      IsMaximumSize (StateFamily (reverseSubstitution s) L) r ∧
      IsMaximumSize (LetterFamily (VertexCoincident s)) r ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) r :=
  fc2_integer_rank_of_reverse hL hC hF ((propertyF_reverse_iff hL hzero).mpr hF)

/-- **FC2 (2) with a one-sided geometric input.**  `PscVerif.GeometricFRank.fc2_rank_transfer`
without its reversed rank realisation: if `c` is the zero-slice maximum of `σ` (the BBK rank, by
Remark 4.3 at `q = 0` and the full return lattice), then on (F) `c` is the maximum size of left
and of right letter families, and the zero-slice maximum of `σ^R`. -/
theorem fc2_rank_transfer_one_sided [Nonempty α] {c : ℕ}
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ)
    (hzero : ∀ v, L v = 0 → v = 0) (hF : PropertyF s L)
    (hRank : IsMaximumSize (StateFamily s L) c) :
    IsMaximumSize (LetterFamily (VertexCoincident s)) c ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) c ∧
      IsMaximumSize (StateFamily (reverseSubstitution s) L) c := by
  obtain ⟨r, -, -, hS, hSrev, hl, hr⟩ := fc2_integer_rank hL hC hzero hF
  obtain rfl := hRank.unique hS
  exact ⟨hl, hr, hSrev⟩

end Transfer

/-- **FC2 (1) with a one-sided geometric input**: the zero-slice maximum of `σ` bounds the left
and the right letter families.  No (F), no contraction data, no injectivity, no reversed rank. -/
theorem fc2_rank_lower_bounds_one_sided [Nonempty α] {s : α → List α} {L : (α → ℤ) →+ ℝ}
    {c l r : ℕ} (hpos : ∀ a, 0 < L (pvec [a]))
    (hRank : IsMaximumSize (StateFamily s L) c)
    (hl : LetterFamily (VertexCoincident s) l)
    (hr : LetterFamily (RightStrongCoincidenceWitness s) r) : l ≤ c ∧ r ≤ c :=
  ⟨hRank.2 (stateFamily_of_leftLetterFamily hpos hl),
    hRank.2 (stateFamily_of_rightLetterFamily hpos hr)⟩

/-- **Corollary E (ii) ⟺ (iii), elementary.**  On (F), every pair of letters is left strongly
coincident iff every pair is right strongly coincident. -/
theorem leftAll_iff_rightAll [Nonempty α] {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    {ν : (α → ℤ) → ℝ} {ρ : ℝ}
    (hL : LengthData s L β) (hC : ContractionData s L ν ρ)
    (hzero : ∀ v, L v = 0 → v = 0) (hF : PropertyF s L) :
    (∀ a b, VertexCoincident s a b) ↔ ∀ a b, RightStrongCoincidenceWitness s a b := by
  obtain ⟨r, -, -, -, -, hl, hr⟩ := fc2_integer_rank hL hC hzero hF
  have hlrefl : ∀ a, VertexCoincident s a a := fun a => edgeCoincident_refl s _
  have hrrefl : ∀ a, RightStrongCoincidenceWitness s a a := rightStrongCoincidenceWitness_refl s
  have hlsymm : ∀ a b, VertexCoincident s a b → VertexCoincident s b a :=
    fun _ _ => edgeCoincident_symm
  have hrsymm : ∀ a b, RightStrongCoincidenceWitness s a b →
      RightStrongCoincidenceWitness s b a := fun _ _ => rightStrongCoincidenceWitness_symm
  constructor
  · intro h
    have h1 : r = 1 := hl.unique ((isMaximumSize_one_iff hlrefl hlsymm).mpr fun a b _ => h a b)
    subst h1
    intro a b
    by_cases hab : a = b
    · subst hab; exact rightStrongCoincidenceWitness_refl s a
    · exact (isMaximumSize_one_iff hrrefl hrsymm).mp hr a b hab
  · intro h
    have h1 : r = 1 := hr.unique ((isMaximumSize_one_iff hrrefl hrsymm).mpr fun a b _ => h a b)
    subst h1
    intro a b
    by_cases hab : a = b
    · subst hab; exact edgeCoincident_refl s _
    · exact (isMaximumSize_one_iff hlrefl hlsymm).mp hl a b hab

/-! ### (Z) Injectivity of the length functional on the standing class -/

/-- **(Z)** `v ↦ ℓ·v` is injective on integer vectors when `χ_M` is irreducible over `ℚ` and `ℓ`
is a positive left eigen-row: Lemma 1 (1) of the class note, machine-checked in round 4
(`Psc.GeometricFLemmas.lenHom_eq_zero_iff`; no Pisot or contraction input).  This wrapper only
supplies `ℓ ≠ 0` from positivity. -/
theorem lenHom_zero_of_pos_eigen [Nonempty α] {s : α → List α} {β : ℝ} {ℓ : α → ℝ}
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ) :
    ∀ v, lenHom ℓ v = 0 → v = 0 :=
  fun _ hv => (Psc.GeometricFLemmas.lenHom_eq_zero_iff s hirr
    (fun h => (hℓ (Classical.arbitrary α)).ne' (by simp [h])) hℓM).1 hv

/-! ### The standing class -/

section Standing

variable {s : α → List α} {β : ℝ} {ℓ : α → ℝ}

/-- **FC2 (2) in integer form on the standing class**, with no rank input: `σ` primitive on at
least two letters, `χ_M` irreducible over `ℚ`, `ℓ > 0` with `ℓ M = β ℓ`, every other complex
root of `χ_M` in the open unit disc, and (F).  The four maxima exist and agree. -/
theorem fc2_integer_rank_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ∃ r, 1 ≤ r ∧ r ≤ Fintype.card α ∧
      IsMaximumSize (StateFamily s (lenHom ℓ)) r ∧
      IsMaximumSize (StateFamily (reverseSubstitution s) (lenHom ℓ)) r ∧
      IsMaximumSize (LetterFamily (VertexCoincident s)) r ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) r := by
  obtain ⟨hL, hβ, ν, ρ, hC⟩ :=
    Psc.GeometricFPisot.fc1_hypotheses_of_primitive_pisot hprim hirr hℓ hℓM hpisot
  exact fc2_integer_rank hL hC
    (lenHom_zero_of_pos_eigen hirr hℓ hℓM) hF

theorem vertexCoincident_iff_strongCoincidenceWitness {a b : α} :
    VertexCoincident s a b ↔ Psc.StrictSystem.StrongCoincidenceWitness s a b := by
  rw [edgeCoincident_zero_iff]
  rfl

/-- **Theorem FC1 with right strong coincidence** (Corollary E (i) ⟺ (iii), with no rank or
spectral input): on the standing class with (F), `σ` has a strict system iff some pair of
distinct letters has no right strong-coincidence witness. -/
theorem fc1_right_of_primitive_pisot [Nontrivial α]
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    (∃ C : Finset (List α × List α), Psc.StrictSystem.StrictSystem s C) ↔
      ¬ ∀ c c', c ≠ c' → RightStrongCoincidenceWitness s c c' := by
  obtain ⟨hL, hβ, ν, ρ, hC⟩ :=
    Psc.GeometricFPisot.fc1_hypotheses_of_primitive_pisot hprim hirr hℓ hℓM hpisot
  have hzero := lenHom_zero_of_pos_eigen hirr hℓ hℓM
  rw [(Psc.GeometricFPisot.fc1_equivalence_of_primitive_pisot hprim hirr hℓ hℓM hpisot hF).2]
  have key := leftAll_iff_rightAll hL hC hzero hF
  have hl : (∀ c c', c ≠ c' → Psc.StrictSystem.StrongCoincidenceWitness s c c') ↔
      ∀ a b, VertexCoincident s a b := by
    constructor
    · intro h a b
      by_cases hab : a = b
      · subst hab; exact edgeCoincident_refl s _
      · exact vertexCoincident_iff_strongCoincidenceWitness.mpr (h a b hab)
    · intro h c c' _
      exact vertexCoincident_iff_strongCoincidenceWitness.mp (h c c')
  have hr : (∀ c c', c ≠ c' → RightStrongCoincidenceWitness s c c') ↔
      ∀ a b, RightStrongCoincidenceWitness s a b := by
    constructor
    · intro h a b
      by_cases hab : a = b
      · subst hab; exact rightStrongCoincidenceWitness_refl s a
      · exact h a b hab
    · intro h c c' _
      exact h c c'
  rw [hl, hr, key]

end Standing

/-- **FC2 (2) in integer form on PIP3** (three letters). -/
theorem fc2_integer_rank_pip3 {s : Fin 3 → List (Fin 3)} {β : ℝ} {ℓ : Fin 3 → ℝ}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) :
    ∃ r, 1 ≤ r ∧ r ≤ 3 ∧
      IsMaximumSize (StateFamily s (lenHom ℓ)) r ∧
      IsMaximumSize (StateFamily (reverseSubstitution s) (lenHom ℓ)) r ∧
      IsMaximumSize (LetterFamily (VertexCoincident s)) r ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) r := by
  simpa using fc2_integer_rank_of_primitive_pisot hprim hirr hℓ hℓM hpisot hF

/-- **FC2 (2) on PIP3 in integer form, with Barge–Diamond as a hypothesis.**  On the standing class
on three letters with (F), suppose two distinct letters are left strongly coincident (Barge–Diamond
2002, Theorem 1, which holds for every substitution of Pisot type; imported, not formalised here).
Then the integer rank `r` of `fc2_integer_rank_pip3` satisfies `1 ≤ r ≤ 2`, and `σ` has a strict
system iff `r = 2`.  With `cr(σ) = S(σ)` (BBK Remark 4.3 at `q = 0`) this is Corollary E of the
class note: `cr = 1` iff no strict system, and otherwise `cr = 2`. -/
theorem fc2_pip3_rank_le_two {s : Fin 3 → List (Fin 3)} {β : ℝ} {ℓ : Fin 3 → ℝ}
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hℓ : ∀ a, 0 < ℓ a) (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 → z ≠ β →
      ‖z‖ < 1)
    (hF : PropertyF s (lenHom ℓ)) (hBD : ∃ a b, a ≠ b ∧ VertexCoincident s a b) :
    ∃ r, 1 ≤ r ∧ r ≤ 2 ∧
      IsMaximumSize (StateFamily s (lenHom ℓ)) r ∧
      IsMaximumSize (StateFamily (reverseSubstitution s) (lenHom ℓ)) r ∧
      IsMaximumSize (LetterFamily (VertexCoincident s)) r ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness s)) r ∧
      ((∃ C : Finset (List (Fin 3) × List (Fin 3)), Psc.StrictSystem.StrictSystem s C) ↔
        r = 2) := by
  obtain ⟨r, hr1, hr3, hS, hSrev, hl, hr⟩ := fc2_integer_rank_pip3 hprim hirr hℓ hℓM hpisot hF
  have hr2 : r ≤ 2 := by
    by_contra h
    have h3 : r = 3 := by omega
    subst h3
    obtain ⟨a, ha⟩ := hl.1
    have hinj : Function.Injective a := fun i j hij => by
      by_contra hne; exact ha hne (by rw [hij]; exact edgeCoincident_refl s _)
    obtain ⟨x, y, hxy, hc⟩ := hBD
    obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.mp hinj) x
    obtain ⟨j, rfl⟩ := (Finite.injective_iff_surjective.mp hinj) y
    exact ha (fun e => hxy (congrArg a e)) hc
  refine ⟨r, hr1, hr2, hS, hSrev, hl, hr, ?_⟩
  have e := isMaximumSize_one_iff (C := VertexCoincident s) (fun a => edgeCoincident_refl s _)
    (fun _ _ => edgeCoincident_symm)
  have hone : (∀ c c', c ≠ c' → Psc.StrictSystem.StrongCoincidenceWitness s c c') ↔ r = 1 := by
    constructor
    · intro h
      exact hl.unique (e.mpr fun a b hab =>
        vertexCoincident_iff_strongCoincidenceWitness.mpr (h a b hab))
    · rintro rfl c c' hcc
      exact vertexCoincident_iff_strongCoincidenceWitness.mp (e.mp hl c c' hcc)
  rw [(Psc.GeometricFPisot.fc1_pip3 hprim hirr hℓ hℓM hpisot hF).2, hone]
  omega

/-! ### Non-vacuity: Tribonacci -/

section Tribonacci

open Psc.Descendants (tribSubst)

/-- **Every pair of Tribonacci letters is right strongly coincident**, obtained from the
transfer: (F) is `Psc.GeometricFTriple.trib_propertyF`, all pairs are left strongly coincident
(`Psc.GeometricFTriple.trib_fc1_evaluated`), and `leftAll_iff_rightAll` turns that into right
strong coincidence. -/
theorem trib_right_all : ∀ a b : Fin 3, RightStrongCoincidenceWitness tribSubst a b := by
  obtain ⟨β, ℓ, hprim, hirr, hℓ, hℓM, hroots, hF⟩ :=
    Psc.GeometricFTriple.trib_fc1_hypotheses_complete
  obtain ⟨hL, hβ, ν, ρ, hC⟩ :=
    Psc.GeometricFPisot.fc1_hypotheses_of_primitive_pisot hprim hirr hℓ hℓM hroots
  have hzero := lenHom_zero_of_pos_eigen hirr hℓ hℓM
  refine (leftAll_iff_rightAll hL hC hzero hF).mp fun a b => ?_
  by_cases hab : a = b
  · subst hab; exact edgeCoincident_refl _ _
  · exact vertexCoincident_iff_strongCoincidenceWitness.mpr
      (Psc.GeometricFTriple.trib_fc1_evaluated.2.2.1 a b hab)

/-- The integer rank of Tribonacci is one, in all four forms. -/
theorem trib_integer_rank_one :
    ∃ (β : ℝ) (ℓ : Fin 3 → ℝ), (∀ a, 0 < ℓ a) ∧
      ℓ ᵥ* (inc tribSubst).map (Nat.cast : ℕ → ℝ) = β • ℓ ∧
      IsMaximumSize (StateFamily tribSubst (lenHom ℓ)) 1 ∧
      IsMaximumSize (StateFamily (reverseSubstitution tribSubst) (lenHom ℓ)) 1 ∧
      IsMaximumSize (LetterFamily (VertexCoincident tribSubst)) 1 ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness tribSubst)) 1 := by
  obtain ⟨β, ℓ, hprim, hirr, hℓ, hℓM, hroots, hF⟩ :=
    Psc.GeometricFTriple.trib_fc1_hypotheses_complete
  obtain ⟨r, -, -, hS, hSrev, hl, hr⟩ :=
    fc2_integer_rank_of_primitive_pisot hprim hirr hℓ hℓM hroots hF
  have h1 : r = 1 := hr.unique ((isMaximumSize_one_iff (rightStrongCoincidenceWitness_refl _)
    (fun _ _ => rightStrongCoincidenceWitness_symm)).mpr fun a b _ => trib_right_all a b)
  subst h1
  exact ⟨β, ℓ, hℓ, hℓM, hS, hSrev, hl, hr⟩

/-- Cross-check on words, independent of the transfer: `σ⁴(0) = 01·0·2010010201` and
`σ⁴(1) = 0·1020100102`; the suffixes after the common `0` have equal Parikh vectors. -/
theorem trib_right_witness_01 : RightStrongCoincidenceWitness tribSubst 0 1 :=
  ⟨4, [0, 1], [2, 0, 1, 0, 0, 1, 0, 2, 0, 1], [], [1, 0, 2, 0, 1, 0, 0, 1, 0, 2], 0,
    by decide, by decide, by decide⟩

/-- `σ⁴(0) = 010201·0·010201` and `σ⁴(2) = 0·102010`. -/
theorem trib_right_witness_02 : RightStrongCoincidenceWitness tribSubst 0 2 :=
  ⟨4, [0, 1, 0, 2, 0, 1], [0, 1, 0, 2, 0, 1], [], [1, 0, 2, 0, 1, 0], 0,
    by decide, by decide, by decide⟩

/-- `σ³(1) = 01·0·201` and `σ³(2) = 0·102`. -/
theorem trib_right_witness_12 : RightStrongCoincidenceWitness tribSubst 1 2 :=
  ⟨3, [0, 1], [2, 0, 1], [], [1, 0, 2], 0, by decide, by decide, by decide⟩

end Tribonacci

/-! ### Non-vacuity at rank two: Thue–Morse -/

section ThueMorse


omit [DecidableEq α] in
/-- If `M` kills the vector of every state, every step lands on a vertex state, so (F) holds. -/
theorem propertyF_of_mulVec_state_eq_zero [DecidableEq α] {s : α → List α}
    {L : (α → ℤ) →+ ℝ} (hpos : ∀ a, 0 < L (pvec [a]))
    (h : ∀ x, IsState L x → incZ s *ᵥ x.2 = 0) : PropertyF s L := by
  intro x hx k hk hper
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm] at hper
  obtain ⟨z, hz, P, S, -, hy, hs0, -⟩ := hper
  rw [h z (stepN_isState hx k hz), zero_sub] at hy
  rw [hy, map_neg] at hs0
  have hP : P = [] := by
    by_contra hne
    linarith [L_pvec_pos hpos hne]
  rw [hy, hP, pvec_nil, neg_zero]

theorem tm_mulVec_state {x : Fin 2 × (Fin 2 → ℤ)} (hx : IsState tmL x) :
    incZ thueMorseSubst *ᵥ x.2 = 0 := by
  obtain ⟨h0, h1⟩ := hx
  rw [tmL_apply] at h0 h1
  have e1 : tmL (pvec [x.1]) = 1 := by simp [tmL, lenHom_single]
  rw [e1] at h1
  have h0' : (0 : ℤ) ≤ x.2 0 + x.2 1 := by exact_mod_cast h0
  have h1' : x.2 0 + x.2 1 < (1 : ℤ) := by exact_mod_cast h1
  funext a
  rw [tm_mulVec]
  change x.2 0 + x.2 1 = 0
  omega

/-- (F) for the reversed Thue–Morse substitution `10/01`. -/
theorem tm_reverse_propertyF : PropertyF (reverseSubstitution thueMorseSubst) tmL :=
  propertyF_of_mulVec_state_eq_zero tm_lengthData.pos fun x hx => by
    rw [incZ_reverseSubstitution]
    exact tm_mulVec_state hx

/-- **Thue–Morse `01/10`: all four maxima are `2`.**  Length data, contraction data and (F)
for both orientations hold (`tm_lengthData`, `tm_contractionData`, `tm_propertyF`,
`tm_reverse_propertyF`), while `ℓ = (1, 1)` is not injective on `ℤ²`; so
`fc2_integer_rank_of_reverse` applies where `fc2_integer_rank` does not, and its common value is
`2`, since `0` and `1` are not left strongly coincident (`Psc.StrictSystem.tm_no_witness`). Not
PIP3: `χ_M = x (x − 2)`. -/
theorem tm_integer_rank_two :
    IsMaximumSize (StateFamily thueMorseSubst tmL) 2 ∧
      IsMaximumSize (StateFamily (reverseSubstitution thueMorseSubst) tmL) 2 ∧
      IsMaximumSize (LetterFamily (VertexCoincident thueMorseSubst)) 2 ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness thueMorseSubst)) 2 := by
  obtain ⟨r, -, hr2, hS, hSrev, hl, hr⟩ := fc2_integer_rank_of_reverse tm_lengthData
    tm_contractionData tm_propertyF tm_reverse_propertyF
  have h2 : LetterFamily (VertexCoincident thueMorseSubst) 2 := by
    refine ⟨![0, 1], ?_⟩
    intro i j hij hc
    rw [vertexCoincident_iff_strongCoincidenceWitness] at hc
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact Psc.StrictSystem.tm_no_witness hc
    · exact Psc.StrictSystem.tm_no_witness
        (Psc.StrictSystem.strongCoincidenceWitness_comm.mp hc)
    · exact hij rfl
  have : r = 2 := le_antisymm (by simpa using hr2) (hl.2 h2)
  subst this
  exact ⟨hS, hSrev, hl, hr⟩

end ThueMorse

/-! ### Counter-calibration: Barge–Diamond's `121/221` -/

section BargeDiamond

/-- Barge–Diamond 2002, final paragraph: `φ = (121, 221)`, here on the letters `0, 1`:
`0 ↦ 010`, `1 ↦ 110`.  Primitive, `M = [[2, 1], [1, 2]]`, eigenvalues `3` and `1`: not of
Pisot type, `χ_M` reducible. -/
def bdSubst : Fin 2 → List (Fin 2) := ![[0, 1, 0], [1, 1, 0]]

/-- `φⁿ(0)` and `φⁿ(1)` differ only in their first letter. -/
theorem bd_power (n : ℕ) :
    ∃ T : List (Fin 2), power bdSubst n 0 = 0 :: T ∧ power bdSubst n 1 = 1 :: T := by
  induction n with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ n ih =>
    obtain ⟨T, h0, h1⟩ := ih
    refine ⟨[1, 0] ++ subst bdSubst T, ?_, ?_⟩
    · rw [power, Function.iterate_succ_apply',
        show (subst bdSubst)^[n] [0] = power bdSubst n 0 from rfl, h0, subst_cons]
      rfl
    · rw [power, Function.iterate_succ_apply',
        show (subst bdSubst)^[n] [1] = power bdSubst n 1 from rfl, h1, subst_cons]
      rfl

/-- `0` and `1` are not left strongly coincident (Barge–Diamond's statement). -/
theorem bd_not_left : ¬ VertexCoincident bdSubst 0 1 := by
  rw [edgeCoincident_zero_iff]
  rintro ⟨n, P, Q, P', Q', c, h0, h1, he⟩
  obtain ⟨T, hT0, hT1⟩ := bd_power n
  rw [hT0] at h0
  rw [hT1] at h1
  have hlen : P.length = P'.length := (List.perm_iff_count.mpr he).length_eq
  cases P with
  | nil =>
    cases P' with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h0 h1
      exact absurd (h0.1.trans h1.1.symm) (by decide)
    | cons _ _ => simp at hlen
  | cons p P₀ =>
    cases P' with
    | nil => simp at hlen
    | cons p' P₀' =>
      simp only [List.cons_append, List.cons.injEq] at h0 h1
      obtain ⟨rfl, h0⟩ := h0
      obtain ⟨rfl, h1⟩ := h1
      have hP : P₀ = P₀' :=
        (List.append_inj (h0.symm.trans h1) (by simpa using hlen)).1
      subst hP
      have := he 0
      simp at this

/-- `0` and `1` are right strongly coincident at level `1`: both images end in `0`. -/
theorem bd_right : RightStrongCoincidenceWitness bdSubst 0 1 :=
  ⟨1, [0, 1], [], [1, 1], [], 0, by decide, by decide, fun _ => rfl⟩

/-- **The two maxima differ off the hypotheses: `ν_L = 2`, `ν_R = 1`.**  `φ` fails contraction
data, (F) on both sides and injectivity of `ℓ`. -/
theorem bd_left_two_right_one :
    IsMaximumSize (LetterFamily (VertexCoincident bdSubst)) 2 ∧
      IsMaximumSize (LetterFamily (RightStrongCoincidenceWitness bdSubst)) 1 := by
  refine ⟨⟨⟨![0, 1], ?_⟩, fun n hn => by
      simpa using LetterFamily.le_card (C := VertexCoincident bdSubst)
        (fun a => edgeCoincident_refl _ _) hn⟩,
    (isMaximumSize_one_iff (rightStrongCoincidenceWitness_refl _)
      (fun _ _ => rightStrongCoincidenceWitness_symm)).mpr ?_⟩
  · intro i j hij hc
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact bd_not_left hc
    · exact bd_not_left (edgeCoincident_symm hc)
    · exact hij rfl
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact bd_right
    · exact rightStrongCoincidenceWitness_symm bd_right
    · exact absurd rfl hab

/-- Length data exist on `φ` (`ℓ = (1, 1)`, `β = 3`). -/
theorem bd_lengthData : LengthData bdSubst (lenHom fun _ => 1) 3 := by
  refine lengthData_of_left_eigen (by norm_num) (fun _ => by norm_num) ?_
  funext c
  fin_cases c <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, bdSubst, inc_apply] <;> norm_num

/-- **One place where Theorem O stops on `φ`**: `M (1, −1) = (1, −1)`, so no contraction data
exist for any length data with `β > 1` (`not_contractionData_of_unit_eigenvector`).  (F) fails
too (`bd_not_propertyF`, `bd_reverse_not_propertyF`), and `ℓ = (1, 1)` is not injective. -/
theorem bd_not_contractionData {L : (Fin 2 → ℤ) →+ ℝ} {β : ℝ} {ν : (Fin 2 → ℤ) → ℝ} {ρ : ℝ}
    (hL : LengthData bdSubst L β) (hβ : 1 < β) : ¬ ContractionData bdSubst L ν ρ :=
  not_contractionData_of_unit_eigenvector hL hβ (w := ![1, -1]) (by decide)
    (Or.inl (by decide))

/-- On `φ` with `ℓ = (1, 1)` the state `(0; 1, −1)` is `f`-fixed: (F) fails. -/
theorem bd_not_propertyF : ¬ PropertyF bdSubst (lenHom fun _ => 1) := by
  intro hF
  have hx : IsState (lenHom fun _ : Fin 2 => (1 : ℝ)) ((0 : Fin 2), ![1, -1]) := by
    refine ⟨?_, ?_⟩ <;> simp [lenHom_apply, Fin.sum_univ_two, pvec]
  have hstep : StepN bdSubst (lenHom fun _ => 1) 1 ((0 : Fin 2), ![1, -1])
      ((0 : Fin 2), ![1, -1]) :=
    ⟨_, rfl, [], [1, 0], by decide, by rw [pvec_nil, sub_zero]; decide, hx⟩
  exact absurd (congrFun (hF _ hx 1 le_rfl hstep) 0) (by decide)

/-- The same state is `f`-fixed for the reversal `010/011`: (F) fails for `φ^R` too. -/
theorem bd_reverse_not_propertyF :
    ¬ PropertyF (reverseSubstitution bdSubst) (lenHom fun _ => 1) := by
  intro hF
  have hx : IsState (lenHom fun _ : Fin 2 => (1 : ℝ)) ((0 : Fin 2), ![1, -1]) := by
    refine ⟨?_, ?_⟩ <;> simp [lenHom_apply, Fin.sum_univ_two, pvec]
  have hstep : StepN (reverseSubstitution bdSubst) (lenHom fun _ => 1) 1 ((0 : Fin 2), ![1, -1])
      ((0 : Fin 2), ![1, -1]) :=
    ⟨_, rfl, [], [1, 0], by decide, by rw [pvec_nil, sub_zero]; decide, hx⟩
  exact absurd (congrFun (hF _ hx 1 le_rfl hstep) 0) (by decide)

end BargeDiamond

end Psc.GeometricF
