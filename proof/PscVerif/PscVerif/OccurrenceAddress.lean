/-
# Occurrence addresses and the residual transport law

The literal layer under the packet square (roadmap immediate-sequence item 2;
`docs/packet-square-stop-go-2026-11-10.md`).  For a pair `(u, v)` of words and
the inflated pair `(σ u, σ v)`:

* `cutAddr s w p = (i, r)`: position `p` of `σ w` is digit `r` of the image of
  the letter `w[i]` (`cutAddr_spec`: every position below `|σ w|` has this
  address, and the prefix of length `p` is `σ (w.take i) ++ (s w[i]).take r`);
* `blockStart bs j`: the start offset of the `j`-th block of a block list;
  `getElem_red`: the `j`-th block of `red u v` is the aligned factor of `(u, v)`
  at `blockStart (red u v) j`, so a child is located by its ordinal;
* `residual_transport`: for selected letters `u[i]`, `v[j]`, digits `d`, `e`
  of their images, and any balanced cut `lo` of `(σ u, σ v)` at or before both
  inflated positions, the Parikh difference of the two prefixes measured from
  `lo` is `M · (u.take i − v.take j) + ((s u[i]).take d − (s v[j]).take e)`.
  This is the packet update `r' = M r + λ` of
  `docs/c4-ordered-word-completion-interface-2026-11-02.md` §1 as a theorem
  about literal prefixes: it holds whether or not the two positions fall in the
  same child, so survival of an occurrence pair is a separate condition;
* `cut_residual_zero`: at a balanced cut, `M · (source prefix defect) + digit
  defect = 0` (the `R1Source` transport law, restated on `Psc` definitions).

The address lemmas and `cut_defect_transport`, `cut_residual_zero` were first
checked in a scratch file of the packet-square reader pass; the standalone
`proof/psc_routes/R1Source.lean` proves the same transport identity over an
arbitrary labelling with the column identity as a hypothesis, which here is
the definition of `inc` (`Psc.Incidence.count_subst`).

Not proved here: that any packet graph is complete or sound with respect to
these occurrences, which pairs of positions fall in one child, or anything
about a substitution in particular.
-/
import PscVerif.Descendants

namespace Psc.OccurrenceAddress

open Psc.Binomial Psc.Reduction Psc.Incidence

variable {α : Type*} [DecidableEq α]

/-! ### Addresses of positions of `σ w` -/

/-- `cutAddr s w p = (i, r)`: position `p` of `σ w` is digit `r` of the image of
`w[i]`. -/
def cutAddr (s : α → List α) : List α → ℕ → ℕ × ℕ
  | [], p => (0, p)
  | a :: w, p =>
    if p < (s a).length then (0, p)
    else ((cutAddr s w (p - (s a).length)).1 + 1, (cutAddr s w (p - (s a).length)).2)

omit [DecidableEq α] in
/-- Every position of `σ w` has an address, and the prefix up to it is the image
of the letters before it followed by a proper prefix of one image. -/
theorem cutAddr_spec (s : α → List α) : ∀ (w : List α) (p : ℕ), p < (subst s w).length →
    ∃ hi : (cutAddr s w p).1 < w.length,
      (cutAddr s w p).2 < (s w[(cutAddr s w p).1]).length ∧
        (subst s w).take p =
          subst s (w.take (cutAddr s w p).1) ++ (s w[(cutAddr s w p).1]).take (cutAddr s w p).2
  | [], p, hp => by simp [subst] at hp
  | a :: w, p, hp => by
    rw [subst_cons, List.length_append] at hp
    by_cases h : p < (s a).length
    · have e : cutAddr s (a :: w) p = (0, p) := by simp [cutAddr, h]
      rw [e]
      refine ⟨by simp, by simpa using h, ?_⟩
      rw [subst_cons, List.take_append_of_le_length h.le]
      simp [subst]
    · have hq : p - (s a).length < (subst s w).length := by omega
      obtain ⟨hi, hr, ht⟩ := cutAddr_spec s w (p - (s a).length) hq
      have e : cutAddr s (a :: w) p =
          ((cutAddr s w (p - (s a).length)).1 + 1, (cutAddr s w (p - (s a).length)).2) := by
        simp [cutAddr, h]
      rw [e]
      refine ⟨by simpa using hi, by simpa using hr, ?_⟩
      rw [subst_cons, List.take_append, List.take_of_length_le (by omega), ht]
      simp [subst_cons, List.append_assoc]

omit [DecidableEq α] in
/-- The converse direction: the prefix of `σ w` ending at digit `d` of the image
of `w[i]`. -/
theorem take_subst_digit (s : α → List α) (w : List α) (i d : ℕ) (hi : i < w.length)
    (hd : d ≤ (s w[i]).length) :
    (subst s w).take ((subst s (w.take i)).length + d) =
      subst s (w.take i) ++ (s w[i]).take d := by
  have hw : subst s w = subst s (w.take i) ++ (s w[i] ++ subst s (w.drop (i + 1))) := by
    conv_lhs => rw [← List.take_append_drop i w]
    rw [List.drop_eq_getElem_cons hi, subst_append, subst_cons]
  rw [hw, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
    List.take_append_of_le_length hd]

/-! ### Locating the `j`-th block -/

/-- The start offset of the `j`-th block. -/
def blockStart (bs : List (List α × List α)) (j : ℕ) : ℕ :=
  ((bs.take j).map fun T => T.1.length).sum

omit [DecidableEq α] in
theorem take_drop_flatten_map (bs : List (List α × List α)) (f : List α × List α → List α)
    (hf : ∀ T ∈ bs, (f T).length = T.1.length) (j : ℕ) (hj : j < bs.length) :
    (((bs.map f).flatten).drop (blockStart bs j)).take bs[j].1.length = f bs[j] := by
  have hlen : (bs.map f).map List.length = bs.map fun T => T.1.length := by
    rw [List.map_map]
    exact List.map_congr_left fun T hT => hf T hT
  have h1 := List.drop_take_succ_flatten_eq_getElem (bs.map f) j (by simpa using hj)
  rw [hlen, ← List.map_take, ← List.map_take] at h1
  have h2 : ((bs.take (j + 1)).map fun T => T.1.length).sum =
      blockStart bs j + bs[j].1.length := by
    rw [← List.take_concat_get' bs j hj, List.map_append, List.sum_append]
    simp [blockStart]
  rw [h2, List.drop_take] at h1
  have h3 : blockStart bs j + bs[j].1.length -
      ((bs.take j).map fun T => T.1.length).sum = bs[j].1.length := by
    simp [blockStart]
  rw [h3] at h1
  simpa [blockStart] using h1

/-- **The `j`-th block of `red u v` is the aligned factor of `(u, v)` at
`blockStart`**: a child is determined by its parent and its ordinal. -/
theorem getElem_red {u v : List α} (h : Equiv1 u v) (j : ℕ) (hj : j < (red u v).length) :
    (red u v)[j] =
      ((u.drop (blockStart (red u v) j)).take (red u v)[j].1.length,
        (v.drop (blockStart (red u v) j)).take (red u v)[j].1.length) := by
  have hb : ∀ T ∈ red u v, T.2.length = T.1.length :=
    fun T hT => ((red_isBlock h T hT).2.1.length_eq).symm
  have ht := take_drop_flatten_map (red u v) Prod.fst (fun _ _ => rfl) j hj
  have hbt := take_drop_flatten_map (red u v) Prod.snd hb j hj
  rw [red_top h.length_eq] at ht
  rw [red_bot h.length_eq] at hbt
  exact Prod.ext ht.symm hbt.symm

/-! ### The transport law -/

section Transport

variable [Fintype α]

/-- The Parikh count of a cut prefix. -/
theorem count_cut (s : α → List α) (pre : List α) (a : α) (r : ℕ) (x : α) :
    (subst s pre ++ (s a).take r).count x =
      (∑ c, inc s x c * pre.count c) + ((s a).take r).count x := by
  rw [List.count_append, count_subst]

/-- `R1Source.actualCut_prefix_mass_transport` on `Psc` definitions, coordinatewise
over `ℤ`. -/
theorem cut_defect_transport (s : α → List α) (p p' : List α) (a a' : α)
    (r r' : ℕ) (x : α) :
    ((subst s p ++ (s a).take r).count x : ℤ) - ((subst s p' ++ (s a').take r').count x : ℤ) =
      (∑ c, (inc s x c : ℤ) * ((p.count c : ℤ) - (p'.count c : ℤ))) +
        ((((s a).take r).count x : ℤ) - (((s a').take r').count x : ℤ)) := by
  rw [count_cut, count_cut]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- At a balanced cut `p` of `(σ u, σ v)`, `M · (source prefix defect) + digit
defect = 0`. -/
theorem cut_residual_zero (s : α → List α) (u v : List α) (p : ℕ)
    (hp : p < (subst s u).length) (hp' : p < (subst s v).length)
    (hz : Equiv1 ((subst s u).take p) ((subst s v).take p)) (x : α) :
    ∃ (hi : (cutAddr s u p).1 < u.length) (hj : (cutAddr s v p).1 < v.length),
      (∑ c, (inc s x c : ℤ) *
          (((u.take (cutAddr s u p).1).count c : ℤ) - ((v.take (cutAddr s v p).1).count c : ℤ))) +
        ((((s u[(cutAddr s u p).1]).take (cutAddr s u p).2).count x : ℤ) -
          (((s v[(cutAddr s v p).1]).take (cutAddr s v p).2).count x : ℤ)) = 0 := by
  obtain ⟨hi, -, hu⟩ := cutAddr_spec s u p hp
  obtain ⟨hj, -, hv⟩ := cutAddr_spec s v p hp'
  refine ⟨hi, hj, ?_⟩
  rw [← cut_defect_transport, ← hu, ← hv, hz x]
  simp

/-- **The residual transport law, derived.**  Select the letters `u[i]` and
`v[j]` and the digits `d`, `e` of their images, and let `lo` be a balanced cut of
`(σ u, σ v)` at or before both inflated positions.  Measured from `lo`, the
Parikh difference of the two prefixes is `M · (u.take i − v.take j)` plus the
digit difference `(s u[i]).take d − (s v[j]).take e`: the packet update
`r' = M r + λ`.  No hypothesis says that the two positions lie in the same
child. -/
theorem residual_transport (s : α → List α) (u v : List α) (i j d e lo : ℕ)
    (hi : i < u.length) (hj : j < v.length) (hd : d ≤ (s u[i]).length)
    (he : e ≤ (s v[j]).length)
    (hlo : lo ≤ (subst s (u.take i)).length + d) (hlo' : lo ≤ (subst s (v.take j)).length + e)
    (hbal : Equiv1 ((subst s u).take lo) ((subst s v).take lo)) (x : α) :
    ((((subst s u).drop lo).take ((subst s (u.take i)).length + d - lo)).count x : ℤ) -
        ((((subst s v).drop lo).take ((subst s (v.take j)).length + e - lo)).count x : ℤ) =
      (∑ c, (inc s x c : ℤ) * (((u.take i).count c : ℤ) - ((v.take j).count c : ℤ))) +
        ((((s u[i]).take d).count x : ℤ) - (((s v[j]).take e).count x : ℤ)) := by
  have split : ∀ (w : List α) (n : ℕ), lo ≤ n →
      ((w.take n).count x : ℤ) = ((w.take lo).count x : ℤ) + (((w.drop lo).take (n - lo)).count x : ℤ) := by
    intro w n hn
    conv_lhs => rw [show n = lo + (n - lo) by omega, List.take_add]
    rw [List.count_append]
    push_cast
    ring
  have hu := split (subst s u) _ hlo
  have hv := split (subst s v) _ hlo'
  rw [take_subst_digit s u i d hi hd] at hu
  rw [take_subst_digit s v j e hj he] at hv
  rw [← cut_defect_transport, hu, hv, hbal x]
  ring

/-- With `lo = 0` the transport law is the defect of the inflated prefixes
themselves. -/
theorem residual_transport_zero (s : α → List α) (u v : List α) (i j d e : ℕ)
    (hi : i < u.length) (hj : j < v.length) (hd : d ≤ (s u[i]).length)
    (he : e ≤ (s v[j]).length) (x : α) :
    ((((subst s u).take ((subst s (u.take i)).length + d)).count x : ℤ) -
        (((subst s v).take ((subst s (v.take j)).length + e)).count x : ℤ)) =
      (∑ c, (inc s x c : ℤ) * (((u.take i).count c : ℤ) - ((v.take j).count c : ℤ))) +
        ((((s u[i]).take d).count x : ℤ) - (((s v[j]).take e).count x : ℤ)) := by
  have := residual_transport s u v i j d e 0 hi hj hd he (Nat.zero_le _) (Nat.zero_le _)
    (fun _ => by simp) x
  simpa using this

end Transport

/-! ### Calibration on Tribonacci -/

open Psc.Descendants (tribSubst)

/-- Tribonacci `0 ↦ 01, 1 ↦ 02, 2 ↦ 0` on the seed `(01, 10)`: the inflated pair
`(0102, 0201)` has the children `(0, 0)` and `(102, 201)`, in that order; the
second starts at offset `1`, which is digit `1` of the image of the first letter
on both tracks. -/
theorem trib_seed_row :
    red (subst tribSubst [0, 1]) (subst tribSubst [1, 0]) = [([0], [0]), ([1, 0, 2], [2, 0, 1])] ∧
      blockStart (red (subst tribSubst [0, 1]) (subst tribSubst [1, 0])) 1 = 1 ∧
      cutAddr tribSubst [0, 1] 1 = (0, 1) ∧ cutAddr tribSubst [1, 0] 1 = (0, 1) := by
  decide

/-- The transport law on that row.  Select the second letters, `u[1] = 1` and
`v[1] = 0`, with digit `0` each: positions `2` of `0102` and of `0201`, both in
the child `(102, 201)` that starts at the balanced cut `1`.  Measured from `1`,
the residual is `M (e₀ − e₁) + 0`. -/
theorem trib_child_transport (x : Fin 3) :
    ((((subst tribSubst [0, 1]).drop 1).take ((subst tribSubst ([0, 1].take 1)).length + 0 - 1)).count x : ℤ) -
        ((((subst tribSubst [1, 0]).drop 1).take ((subst tribSubst ([1, 0].take 1)).length + 0 - 1)).count x : ℤ) =
      (∑ c, (inc tribSubst x c : ℤ) * ((([0, 1].take 1).count c : ℤ) - (([1, 0].take 1).count c : ℤ))) +
        ((((tribSubst ([0, 1] : List (Fin 3))[1]).take 0).count x : ℤ) -
          (((tribSubst ([1, 0] : List (Fin 3))[1]).take 0).count x : ℤ)) :=
  residual_transport tribSubst [0, 1] [1, 0] 1 1 0 0 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) x

/-- The value: the child prefixes are `1` and `2`, so the residual is
`(0, 1, −1) = M (e₀ − e₁)`, the difference of the first two columns of `M`. -/
theorem trib_child_residual :
    (fun x : Fin 3 => ((((subst tribSubst [0, 1]).drop 1).take 1).count x : ℤ) -
        ((((subst tribSubst [1, 0]).drop 1).take 1).count x : ℤ)) = ![0, 1, -1] ∧
      (fun x : Fin 3 => (inc tribSubst x 0 : ℤ) - inc tribSubst x 1) = ![0, 1, -1] := by
  decide

end Psc.OccurrenceAddress
