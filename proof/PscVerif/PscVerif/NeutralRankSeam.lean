/-
# Neutral rank and one-track seams: the endpoint branch and the `01/122/201` witness

`docs/c4-neutral-rank-seam-ceiling-2026-11-18.md`, Lemma B and its negative control.

**Setting (abstract).**  `C` is a finite set of overlap-cell types and `K` a field.  `rows c`
lists the physical children of `c` in order, and the occurrence matrix is
`occ rows u c = (rows c).count u` (child rows, parent columns).  An `EndpointData` records the
last- and first-child maps `gR`, `gL`; the predicates `sharedR`, `sharedL` (the right, resp.
left, end of a cell is a vertex of both tracks); the adjacency `Adj s t` of cells of the
joining (`s` on the left); and endpoint values `P`, `Q` (a defect functional's pair values,
composed with the letters of a cell), with (EC1) and (EC2) of the note.  The
promotion-weighted functional is `κ_R c = ε⁻ᵏ P (gRᵏ c)` at the least `k` with
`sharedR (gRᵏ c)` (`0` if none), `κ_L` likewise, and `kappa = κ_R − κ_L`.

**Proved here, in full** (no `sorry`):
* `promoted_comp`: `κ_R (gR c) = ε κ_R c` (persistence of shared ends, (EC2), `ε ≠ 0`).
* `promoted_adj`: `κ_R s = κ_L t` for adjacent `s`, `t` (closure of adjacency under
  `(gR, gL)`, both sides agree on sharedness, (EC1)).
* `promoted_swap`: a swap commuting with `g` and `shared`, with `P ∘ J = −P`, makes
  `κ_R ∘ J = −κ_R`.
* `linked_sum`, **`column_identity`**, **`vecMul_occ_eq`**: a row of linked children from
  `gL c` to `gR c` sums to `ε · kappa c`, so `kappa ᵥ* occ rows = ε • kappa`.  The
  promotion weights are needed: `naive_fails` is a three-cell model where the unweighted
  functional breaks the column identity.
* **`bigon_sum`**: a linked block with shared outer ends sums to `P last − Q first`, hence
  **`defect_eq_kappa_mul`**: `D = κ * Π`.
* **`rank_le_finrank_oddEigen`** and **`endpoint_rank_bound`**: `rank D` is at most the
  dimension of the swap-odd left `ε`-eigenspace of the occurrence matrix; no seam term.

**Witness `01/122/201`** (`seamSubst`, `det M = +1`), decided on words and integer vectors:
four interior addresses of period 4 (`seam_isInteriorAddress_*`, in the sense of
`Psc.GeometricFLemmas.IsInteriorAddress`); the endpoint maps; the six legal bigrams
`{1,2} × {0,1,2}`, each fixed by `(gR × gL)²`, and no other bigram with left letter in the
range of `gR`; and `seam_trace`: on six bigrams copied over a 4-cycle, fixed edges minus fixed
endpoint germs equal `4·[4 ∣ n]` for `n = 1, …, 12`, the virtual trace of `+1` at each fourth
root of unity.

**Not proved here.**  That the overlap sink of a strict rank-two component meets these
structural hypotheses (the written ledger T1–T6 of the note), the endpoint-coboundary form
(round-3 draft Proposition E), the seam-spectrum cycle theorem, that the four addresses form a
single `f`-cycle, and that they exhaust the interior states.
-/
import PscVerif.GeometricFLemmas

namespace Psc.NeutralRankSeam

open Matrix Psc.Binomial Psc.GeometricF Psc.GeometricFLemmas

/-! ### Promotion-weighted endpoint values -/

section Promotion

variable {C K : Type*} [Field K]

/-- `ε⁻ᵏ P (gᵏ c)` at the least `k` with `shared (gᵏ c)`, and `0` if there is none. -/
noncomputable def promoted (g : C → C) (shared : C → Prop) (P : C → K) (ε : K) (c : C) : K := by
  classical
  exact if h : ∃ k, shared (g^[k] c) then ε⁻¹ ^ Nat.find h * P (g^[Nat.find h] c) else 0

variable {g : C → C} {shared : C → Prop} {P : C → K} {ε : K}

theorem promoted_of_shared {c : C} (hc : shared c) : promoted g shared P ε c = P c := by
  classical
  have h : ∃ k, shared (g^[k] c) := ⟨0, hc⟩
  have h0 : Nat.find h = 0 := (Nat.find_eq_zero h).2 hc
  simp only [promoted, dite_eq_left h, h0, pow_zero, one_mul, Function.iterate_zero, id]

/-- **Promotion equivariance**: `κ_R (g c) = ε κ_R c`. -/
theorem promoted_comp (hε : ε ≠ 0) (hpers : ∀ c, shared c → shared (g c))
    (heq : ∀ c, shared c → P (g c) = ε * P c) (c : C) :
    promoted g shared P ε (g c) = ε * promoted g shared P ε c := by
  classical
  by_cases h : ∃ k, shared (g^[k] c)
  · by_cases hc : shared c
    · rw [promoted_of_shared (hpers c hc), promoted_of_shared hc, heq c hc]
    · have hk : Nat.find h ≠ 0 := fun h0 => hc ((Nat.find_eq_zero h).1 h0)
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hspec : shared (g^[j] (g c)) := by
        have := Nat.find_spec h
        rwa [hj, Function.iterate_succ_apply] at this
      have h' : ∃ k, shared (g^[k] (g c)) := ⟨j, hspec⟩
      have hfind : Nat.find h' = j := by
        refine (Nat.find_eq_iff h').2 ⟨hspec, fun i hi hsh => ?_⟩
        exact Nat.find_min h (show i + 1 < Nat.find h by omega)
          (by rwa [Function.iterate_succ_apply])
      have hiter : g^[j] (g c) = g^[Nat.find h] c := by
        rw [hj, Function.iterate_succ_apply]
      simp only [promoted, dite_eq_left h, dite_eq_left h', hfind, hiter]
      rw [hj, pow_succ]
      field_simp
  · have h' : ¬ ∃ k, shared (g^[k] (g c)) := fun ⟨k, hk⟩ =>
      h ⟨k + 1, by rwa [Function.iterate_succ_apply]⟩
    simp only [promoted, dite_eq_right h, dite_eq_right h', mul_zero]

/-- **Swap-oddness**: a swap commuting with `g` and preserving `shared`, with `P ∘ J = −P`. -/
theorem promoted_swap {J : C → C} (hJg : ∀ c, g (J c) = J (g c)) (hJs : ∀ c, shared (J c) ↔ shared c)
    (hJP : ∀ c, P (J c) = - P c) (c : C) :
    promoted g shared P ε (J c) = - promoted g shared P ε c := by
  classical
  have hit : ∀ k, g^[k] (J c) = J (g^[k] c) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hJg, Function.iterate_succ_apply']
  have hiff : ∀ k, shared (g^[k] (J c)) ↔ shared (g^[k] c) := fun k => by rw [hit, hJs]
  by_cases h : ∃ k, shared (g^[k] c)
  · have h' : ∃ k, shared (g^[k] (J c)) := let ⟨k, hk⟩ := h; ⟨k, (hiff k).2 hk⟩
    have hfind : Nat.find h' = Nat.find h :=
      le_antisymm (Nat.find_min' h' ((hiff _).2 (Nat.find_spec h)))
        (Nat.find_min' h ((hiff _).1 (Nat.find_spec h')))
    simp only [promoted]
    rw [dite_eq_left h', dite_eq_left h, hfind, hit, hJP, mul_neg]
  · have h' : ¬ ∃ k, shared (g^[k] (J c)) := fun ⟨k, hk⟩ => h ⟨k, (hiff k).1 hk⟩
    simp only [promoted]
    rw [dite_eq_right h', dite_eq_right h, neg_zero]

end Promotion

/-! ### Adjacent cells promote together -/

section Adjacency

variable {C K : Type*} [Field K] {gR gL : C → C} {sharedR sharedL : C → Prop}
  {P Q : C → K} {ε : K} {Adj : C → C → Prop}

theorem adj_iterate (hclosed : ∀ s t, Adj s t → Adj (gR s) (gL t)) {s t : C} (h : Adj s t) :
    ∀ k, Adj (gR^[k] s) (gL^[k] t) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hclosed _ _ ih

/-- **Adjacent cells carry equal promoted values across their common boundary.** -/
theorem promoted_adj (hclosed : ∀ s t, Adj s t → Adj (gR s) (gL t))
    (hside : ∀ s t, Adj s t → (sharedR s ↔ sharedL t))
    (hEC1 : ∀ s t, Adj s t → sharedR s → P s = Q t) {s t : C} (h : Adj s t) :
    promoted gR sharedR P ε s = promoted gL sharedL Q ε t := by
  classical
  have hk := adj_iterate hclosed h
  have hiff : ∀ k, sharedR (gR^[k] s) ↔ sharedL (gL^[k] t) := fun k => hside _ _ (hk k)
  by_cases hs : ∃ k, sharedR (gR^[k] s)
  · have ht : ∃ k, sharedL (gL^[k] t) := let ⟨k, hk'⟩ := hs; ⟨k, (hiff k).1 hk'⟩
    have hfind : Nat.find hs = Nat.find ht :=
      le_antisymm (Nat.find_min' hs ((hiff _).2 (Nat.find_spec ht)))
        (Nat.find_min' ht ((hiff _).1 (Nat.find_spec hs)))
    simp only [promoted, dite_eq_left hs, dite_eq_left ht, hfind]
    rw [hEC1 _ _ (hk _) (hfind ▸ Nat.find_spec hs)]
  · have ht : ¬ ∃ k, sharedL (gL^[k] t) := fun ⟨k, hk'⟩ => hs ⟨k, (hiff k).2 hk'⟩
    simp only [promoted, dite_eq_right hs, dite_eq_right ht]

end Adjacency

/-! ### Endpoint data, the column identity and the eigen-row -/

/-- Consecutive members of a list are related by `R`. -/
def Linked {C : Type*} (R : C → C → Prop) : List C → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => R a b ∧ Linked R (b :: t)

/-- The data of the endpoint branch on a set of cell types. -/
structure EndpointData (C K : Type*) [Field K] where
  gR : C → C
  gL : C → C
  sharedR : C → Prop
  sharedL : C → Prop
  Adj : C → C → Prop
  P : C → K
  Q : C → K
  ε : K
  ε_ne : ε ≠ 0
  persR : ∀ c, sharedR c → sharedR (gR c)
  persL : ∀ c, sharedL c → sharedL (gL c)
  /-- (EC2) endpoint equivariance at shared ends. -/
  eqR : ∀ c, sharedR c → P (gR c) = ε * P c
  eqL : ∀ c, sharedL c → Q (gL c) = ε * Q c
  closed : ∀ s t, Adj s t → Adj (gR s) (gL t)
  side : ∀ s t, Adj s t → (sharedR s ↔ sharedL t)
  /-- (EC1) one value at every shared cut. -/
  ec1 : ∀ s t, Adj s t → sharedR s → P s = Q t

namespace EndpointData

variable {C K : Type*} [Field K] (E : EndpointData C K)

/-- `κ_R`. -/
noncomputable def kR (c : C) : K := promoted E.gR E.sharedR E.P E.ε c
/-- `κ_L`. -/
noncomputable def kL (c : C) : K := promoted E.gL E.sharedL E.Q E.ε c
/-- The promotion-weighted endpoint functional `κ̃ = κ_R − κ_L`. -/
noncomputable def kappa (c : C) : K := E.kR c - E.kL c

theorem linked_sum : ∀ (a : C) (t : List C), Linked E.Adj (a :: t) →
    ((a :: t).map E.kappa).sum = E.kR ((a :: t).getLast (List.cons_ne_nil a t)) - E.kL a
  | a, [], _ => by simp [kappa]
  | a, b :: t, ⟨hab, hrest⟩ => by
    rw [List.map_cons, List.sum_cons, linked_sum b t hrest, List.getLast_cons_cons]
    have : E.kR a = E.kL b := promoted_adj E.closed E.side E.ec1 hab
    simp only [kappa, this]
    abel

/-- **Column identity**: a linked row from `gL c` to `gR c` sums to `ε · κ̃ c`. -/
theorem column_identity (c a : C) (t : List C) (hl : Linked E.Adj (a :: t))
    (hfirst : a = E.gL c) (hlast : (a :: t).getLast (List.cons_ne_nil a t) = E.gR c) :
    ((a :: t).map E.kappa).sum = E.ε * E.kappa c := by
  rw [E.linked_sum a t hl, hlast, hfirst]
  simp only [kR, kL, kappa, promoted_comp E.ε_ne E.persR E.eqR,
    promoted_comp E.ε_ne E.persL E.eqL, mul_sub]

/-- **Bigon sum**: a linked block with shared outer ends sums to `P last − Q first`. -/
theorem bigon_sum (a : C) (t : List C) (hl : Linked E.Adj (a :: t)) (hfirst : E.sharedL a)
    (hlast : E.sharedR ((a :: t).getLast (List.cons_ne_nil a t))) :
    ((a :: t).map E.kappa).sum = E.P ((a :: t).getLast (List.cons_ne_nil a t)) - E.Q a := by
  rw [E.linked_sum a t hl]
  simp only [kR, kL, promoted_of_shared hlast, promoted_of_shared hfirst]

end EndpointData

/-! ### Occurrence matrices -/

section Occurrence

variable {C B K : Type*} [Field K] [Fintype C] [DecidableEq C]

/-- Occurrence matrix: `occ rows u c` is the number of occurrences of `u` in `rows c`. -/
def occ (rows : B → List C) : Matrix C B K := fun u c => ((rows c).count u : K)

theorem vecMul_occ (x : C → K) (rows : B → List C) (b : B) :
    (x ᵥ* occ rows) b = ((rows b).map x).sum := by
  simp only [vecMul, dotProduct, occ]
  rw [Finset.sum_list_map_count (rows b) x]
  simp_rw [nsmul_eq_mul, mul_comm (x _)]
  exact (Finset.sum_subset (Finset.subset_univ _) fun u _ hu => by
    rw [List.count_eq_zero.2 (by simpa using hu), Nat.cast_zero, zero_mul]).symm

variable (E : EndpointData C K) (rows : C → List C)

/-- **`κ̃ ᵥ* A = ε • κ̃`** for the occurrence matrix of rows meeting the column hypotheses. -/
theorem vecMul_occ_eq
    (hrow : ∀ c, ∃ a t, rows c = a :: t ∧ Linked E.Adj (a :: t) ∧ a = E.gL c ∧
      (a :: t).getLast (List.cons_ne_nil a t) = E.gR c) :
    E.kappa ᵥ* occ rows = E.ε • E.kappa := by
  funext c
  obtain ⟨a, t, hc, hl, hf, hlast⟩ := hrow c
  rw [vecMul_occ, hc, E.column_identity c a t hl hf hlast, Pi.smul_apply, smul_eq_mul]

end Occurrence

/-! ### The rank bound -/

section Rank

variable {V B C K : Type*} [Field K] [Fintype V] [Fintype B] [Fintype C] [DecidableEq C]

/-- Swap-odd left `ε`-eigen-rows of `A`, for a swap `J : C → C`. -/
def oddEigen (A : Matrix C C K) (J : C → C) (ε : K) : Submodule K (C → K) where
  carrier := {x | x ᵥ* A = ε • x ∧ ∀ c, x (J c) = - x c}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by rw [add_vecMul, hx, hy, smul_add], fun c => ?_⟩
    simp only [Pi.add_apply, hx', hy', neg_add]
  zero_mem' := ⟨by simp, fun c => by simp⟩
  smul_mem' := by
    rintro r x ⟨hx, hx'⟩
    refine ⟨by rw [smul_vecMul, hx, smul_comm], fun c => ?_⟩
    simp only [Pi.smul_apply, hx', smul_neg]

omit [DecidableEq C] in
/-- **Rank bound**: if every row of `κ` is a swap-odd left `ε`-eigen-row of `A`, then
`rank (κ * Π) ≤ dim oddEigen A J ε`. -/
theorem rank_le_finrank_oddEigen (A : Matrix C C K) (J : C → C) (ε : K)
    (kap : Matrix V C K) (Pi : Matrix C B K) (hrows : ∀ v, kap v ∈ oddEigen A J ε) :
    (kap * Pi).rank ≤ Module.finrank K (oddEigen A J ε) := by
  refine (rank_mul_le_left kap Pi).trans ?_
  rw [rank_eq_finrank_span_row]
  exact Submodule.finrank_mono (Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hrows v))

/-- **Lemma B, assembled.**  A family of endpoint data indexed by the coordinates `V` of the
defect, sharing the maps and the adjacency, gives `D v b = P_v (last b) − Q_v (first b)` on
linked blocks with shared outer ends; `D = κ * Π` and `rank D ≤ dim oddEigen A J ε`. -/
theorem endpoint_rank_bound (E : V → EndpointData C K) (ε : K) (hε : ∀ v, (E v).ε = ε)
    (rows : C → List C) (blocks : B → List C) (J : C → C)
    (hrow : ∀ v c, ∃ a t, rows c = a :: t ∧ Linked (E v).Adj (a :: t) ∧ a = (E v).gL c ∧
      (a :: t).getLast (List.cons_ne_nil a t) = (E v).gR c)
    (hblock : ∀ v b, ∃ a t, blocks b = a :: t ∧ Linked (E v).Adj (a :: t) ∧ (E v).sharedL a ∧
      (E v).sharedR ((a :: t).getLast (List.cons_ne_nil a t)))
    (hodd : ∀ v c, (E v).kappa (J c) = - (E v).kappa c)
    (D : Matrix V B K)
    (hD : ∀ v b a t, blocks b = a :: t →
      D v b = (E v).P ((a :: t).getLast (List.cons_ne_nil a t)) - (E v).Q a) :
    D = Matrix.of (fun v c => (E v).kappa c) * occ blocks ∧
      D.rank ≤ Module.finrank K (oddEigen (occ rows) J ε) := by
  have hfac : D = Matrix.of (fun v c => (E v).kappa c) * occ blocks := by
    ext v b
    obtain ⟨a, t, hb, hl, hf, hlast⟩ := hblock v b
    have : (Matrix.of (fun v c => (E v).kappa c) * occ blocks : Matrix V B K) v b =
        ((E v).kappa ᵥ* occ blocks) b := rfl
    rw [this, vecMul_occ, hb, (E v).bigon_sum a t hl hf hlast, hD v b a t hb]
  refine ⟨hfac, hfac ▸ rank_le_finrank_oddEigen _ J ε _ _ fun v => ⟨?_, hodd v⟩⟩
  change (E v).kappa ᵥ* occ rows = ε • (E v).kappa
  rw [vecMul_occ_eq (E v) rows (hrow v), hε v]

end Rank

/-! ### The promotion weights are needed -/

section Naive

/-- Three cells: `0` has a one-track right end promoted after one step to the shared cell `1`;
`gR 0 = 1`, `gR 1 = 1`; no left ends are shared.  With `P 1 = 1`, `ε = 1`, the promoted value
of `0` is `1`, while the unweighted value (`P` only where already shared) is `0`; the unweighted
functional breaks `κ (gR 0) = ε κ 0`. -/
theorem naive_fails :
    let g : Fin 3 → Fin 3 := ![1, 1, 2]
    let shared : Fin 3 → Prop := fun c => c = 1
    let P : Fin 3 → ℚ := ![0, 1, 0]
    promoted g shared P 1 (g 0) = 1 * promoted g shared P 1 0 ∧
      (if shared (g 0) then P (g 0) else 0) ≠ 1 * (if shared 0 then P 0 else 0) := by
  intro g shared P
  refine ⟨promoted_comp one_ne_zero (fun c hc => by simp_all [shared, g])
    (fun c hc => by subst hc; simp [P, g]) 0, ?_⟩
  simp [g, shared, P]

end Naive

/-! ### The witness `01/122/201` -/

section Witness

/-- `01/122/201`: `0 ↦ 01`, `1 ↦ 122`, `2 ↦ 201`; `det M = +1`. -/
def seamSubst : Fin 3 → List (Fin 3) := ![[0, 1], [1, 2, 2], [2, 0, 1]]

theorem seam_det : (incZ seamSubst).det = 1 := by decide

/-- Last-letter map `gR` and first-letter map `gL`. -/
def seamLast : Fin 3 → Fin 3 := ![1, 2, 1]
def seamFirst : Fin 3 → Fin 3 := ![0, 1, 2]

theorem seam_endpoint_maps :
    (∀ a, (seamSubst a).getLast? = some (seamLast a)) ∧
      ∀ a, (seamSubst a).head? = some (seamFirst a) := by decide

/-- The six bigrams with left letter in `{1,2}` are legal (factors of `σ³` of a letter) and are
fixed by `(gR × gL)²`; `0` is not in the range of `gR`. -/
theorem seam_bigram_legal :
    ∀ a c : Fin 3, a ≠ 0 → ∃ x : Fin 3, [a, c] <:+: power seamSubst 3 x := by decide

theorem seam_bigram_cyclic :
    (∀ a : Fin 3, a ≠ 0 → seamLast (seamLast a) = a) ∧ (∀ c, seamFirst c = c) ∧
      ∀ a, seamLast a ≠ 0 := by decide

/-- **Four interior addresses of period 4** (`(M⁴ − I) v = p(P)`, `σ⁴(e) = P e Q`). -/
theorem seam_isInteriorAddress_1 :
    IsInteriorAddress seamSubst 4 1 ((power seamSubst 4 1).take 8)
      ((power seamSubst 4 1).drop 9) ![0, 1, -1] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem seam_isInteriorAddress_2 :
    IsInteriorAddress seamSubst 4 1 ((power seamSubst 4 1).take 22)
      ((power seamSubst 4 1).drop 23) ![-1, 0, 1] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem seam_isInteriorAddress_3 :
    IsInteriorAddress seamSubst 4 1 ((power seamSubst 4 1).take 60)
      ((power seamSubst 4 1).drop 61) ![0, 0, 1] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

theorem seam_isInteriorAddress_4 :
    IsInteriorAddress seamSubst 4 2 ((power seamSubst 4 2).take 38)
      ((power seamSubst 4 2).drop 39) ![1, 0, 0] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Fixed seam edges, last-letter germs and first-letter germs of six bigrams
`{1,2} × {0,1,2}` copied over a 4-cycle `ZMod 4` of interior states, at power `n`. -/
def seamU (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 3 × Fin 3 × ZMod 4 =>
    x.1 ≠ 0 ∧ seamLast^[n] x.1 = x.1 ∧ seamFirst^[n] x.2.1 = x.2.1 ∧ x.2.2 + n = x.2.2).card

def seamL (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 3 × ZMod 4 =>
    x.1 ≠ 0 ∧ seamLast^[n] x.1 = x.1 ∧ x.2 + n = x.2).card

def seamR (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 3 × ZMod 4 => seamFirst^[n] x.1 = x.1 ∧ x.2 + n = x.2).card

/-- **The `+1` control**: `U(n) − L(n) − R(n) = 4·[4 ∣ n]` for `n = 1, …, 12`. -/
theorem seam_trace :
    ∀ n : Fin 13, 0 < n.val →
      (seamU n : ℤ) - seamL n - seamR n = if 4 ∣ n.val then 4 else 0 := by decide

end Witness

end Psc.NeutralRankSeam
