/-
# Theorem FC1 (3) and the equivalences: the strict system of the blocks between common vertices

`docs/c4-geometric-f-class-2026-11-16.md` §3 (Theorem FC1, item 3, proof step (S), and
"The equivalences"); `docs/c4-cut-pair-productivity-2026-11-04.md` §2 (Theorem A, used
through `Psc.StrictSystem.no_strictSystem_of_strongCoincidence`) and §3, the "Powers"
paragraph, whose direction "a strict system for `σ^m` gives one for `σ`" was prose only and
is proved here (`strictSystem_of_power`).  Continues `PscVerif.GeometricFInclusion` (items
1 and 2); the setting and notation are those of its docstring.

**Definitions.**
* `cutBlocks X X'`: the irreducible balanced pairs (`Psc.Reduction.IsBlock`)
  `(X[a, a + d), X'[a, a + d))` that start at a common cut index `a`
  (`Equiv1 (win X 0 a) (win X' 0 a)`): the blocks of `(X, X')` between consecutive common
  vertices;
* `powerBlocks s m C`: the irreducible factors of `σ^r(C)`, `0 ≤ r < m`;
* `IsPeriodicLetter s c`: `σ^k(c)` begins with `c` for some `k ≥ 1`
  (`isPeriodicLetter_iff`: `g^k(c) = c` for the first-letter map `g`);
* `lenHom ℓ` (`v ↦ ℓ·v`), `tmL`, `tmNu` (the Thue–Morse control), `cd1Subst`, `cd2Subst`,
  `minusOneSubst`, `carrierRevSubst` (reducible strict controls).

**Proved here, in full** (`propext`, `Classical.choice`, `Quot.sound` only):
* `cutBlocks_closed` (stable under the children of every substitution fixing both words:
  the complete balanced factorisation of `(τ u, τ v)` cuts exactly at the common vertices
  in between), `cutBlocks_length_le`, `cutBlocks_finite`, `cutBlocks_nonempty` (from
  bounded gaps), `witness_of_coincident_cutBlock` (a coincident block is a left
  strong-coincidence witness, `Psc.StrictSystem.StrongCoincidenceWitness`, for the first
  letters; uses `β > 1`);
* **`strictSystem_power_of_inclusion`**: if `M^{mN} V_X ⊆ V_{X'}` and the first letters have
  no witness, `cutBlocks X X'` is a `Psc.StrictSystem.StrictSystem` for `power s m`;
* **`strictSystem_of_power`** (Powers): for nonerasing `σ`, `m ≥ 1`, a strict system `C` for
  `σ^m` gives the strict system `powerBlocks s m C` for `σ`;
* **`fc1_strictSystem`** (Theorem FC1 (3), abstract form: length data with `β > 1`, two
  `σ^m`-fixed words, (Fin), (F) on `R`, no witness for the first letters);
* the rays: `isFixed_limit` (the limit word of `Psc.FixedPointLimit` is
  `Psc.BPrimeBinding.IsFixed` for the power substitution), `exists_fixed_ray`;
* `iterate_first`, `witness_of_iterate_first`, `witness_of_iterate_first_eq`,
  `exists_periodic_pair` (the last paragraph of the proof of Theorem FC1);
* **`fc1_equivalence`** and **`fc1_equivalence_of_contraction`** (the equivalences: `σ` has a
  strict system iff some pair of distinct `g`-periodic letters has no left
  strong-coincidence witness iff left strong coincidence fails for some pair; the second
  form takes `LengthData`, `β > 1`, `ContractionData` and `PropertyF`);
* binding: `lengthData_of_left_eigen` (a positive left eigenvector `ℓ M = β ℓ`, `β > 0`,
  gives `LengthData s (lenHom ℓ) β`) and `exists_lengthData_of_primitive` (through
  `Psc.PerronExistence.exists_pos_left_eigen_inc`);
* non-vacuity: `tm_lengthData`, `tm_contractionData`, `tm_propertyF`, **`tm_fc1`**,
  `tm_periodic_pair`: every hypothesis of `fc1_equivalence_of_contraction` holds for
  Thue–Morse `01/10` (with `ℓ = (1, 1)`, `β = 2`, `ν v = |v₀ − v₁|`, `ρ = 0`), and its three
  statements are true there (`Psc.StrictSystem.tm_strictSystem`);
* negative controls: `not_contractionData_of_unit_eigenvector` (a nonzero integer
  eigenvector of `M` for `1` or `−1` excludes `ContractionData` for every length data with
  `β > 1`), `carrier_not_contractionData` (`10/102/211`, whose strict system is
  `Psc.StrictSystem.carrier_strictSystem`; length data exist there, `carrier_lengthData`)
  and `reducible_controls_not_contractionData` (`011/120/2012`, `010/1222/2012`,
  `01/201/112`, `1/012/101`): on the reducible strict controls the argument stops at the
  contraction/properness hypothesis.

**Hypotheses and where they enter.**  `β > 1`: the images `σ^{mn}(c)` grow (`exists_long`),
so the rays exist and a coincident block lies in `σ^{mn}(c)`, `σ^{mn}(c')` for one `n`.
Nonerasure (from `LengthData`): Powers.  (Fin), (F): only through
`Psc.GeometricF.inclusion`.  The implication "strict system ⟹ left strong coincidence
fails" is Theorem A (1), (4) of the cut-pair note and uses no hypothesis.

**Not proved here.**  That a PIP3 substitution satisfies `ContractionData` and `β > 1`: both
are hypotheses here; `PscVerif.GeometricFPisot` proves them and states the equivalence on the
standing class; the equivalence of (F) for `σ` and `σ^m` or `σ^R` (Lemma 4); the
converse direction of the Powers paragraph; Theorem FC2 and everything after it; the strict
systems of the four controls defined here (pinned in Mojo only); the singular controls other
than Thue–Morse and the control `a → aaaab, b → abbbb` are not treated.  Thue–Morse
is a negative control of the note (not PIP3: `ℓ` is not injective, the eigenvalue `0`);
`tm_fc1` shows only that the abstract hypotheses are jointly satisfiable and that the
conclusion is then the true one, as the note's control table says ("FC1 predicts a strict
system when a periodic pair is not coincident").  Universal C4 is open: nothing here
excludes a strict system on PIP3.
-/
import PscVerif.GeometricFInclusion
import PscVerif.GeometricFLength
import PscVerif.StrictSystem

namespace Psc.GeometricF

open Matrix Psc.Binomial Psc.Incidence Psc.Reduction Psc.Descendants Psc.BPrimeBinding
open Psc.StrictSystem (StrictSystem StrongCoincidenceWitness)

variable {α : Type*} [DecidableEq α]

/-! ### Windows -/

omit [DecidableEq α] in
/-- A window that factors as `p ++ w` splits at `|p|`. -/
theorem win_split {X : ℕ → α} {b n : ℕ} {p w : List α}
    (h : win X b (p.length + n) = p ++ w) :
    win X b p.length = p ∧ win X (b + p.length) n = w := by
  rw [win_add] at h
  exact List.append_inj h (by simp)

/-! ### The blocks between consecutive common cuts -/

/-- The **blocks of `(X, X')` between consecutive common vertices**: the irreducible balanced
pairs `(X[a, a + d), X'[a, a + d))` that start at a common cut index `a` (the prefixes of
length `a` of `X` and `X'` have equal Parikh vectors).  Irreducibility (`IsBlock`) says that
no common cut lies strictly between `a` and `a + d`. -/
def cutBlocks (X X' : ℕ → α) : Set (List α × List α) :=
  {T | IsBlock T ∧ ∃ a, Equiv1 (win X 0 a) (win X' 0 a) ∧
    T.1 = win X a T.1.length ∧ T.2 = win X' a T.1.length}

/-- The blocks are stable under the children of every substitution that fixes both words:
the complete balanced factorisation of `(τ u, τ v)` cuts it exactly at the common vertices
in between. -/
theorem cutBlocks_closed {t : α → List α} {X X' : ℕ → α} (hX : IsFixed t X)
    (hX' : IsFixed t X') {T : List α × List α} (hT : T ∈ cutBlocks X X')
    {U : List α × List α} (hU : U ∈ red (subst t T.1) (subst t T.2)) : U ∈ cutBlocks X X' := by
  obtain ⟨hB, a, hcut, h1, h2⟩ := hT
  have hbal : Equiv1 (subst t T.1) (subst t T.2) := equiv1_subst t hB.2.1
  have hcut' : Equiv1 (subst t (win X 0 a)) (subst t (win X' 0 a)) := equiv1_subst t hcut
  rw [subst_win_zero hX, subst_win_zero hX'] at hcut'
  have hb : phi t X a = phi t X' a := by simpa using hcut'.length_eq
  have e1 := subst_win hX a T.1.length
  rw [← h1] at e1
  have e2 := subst_win hX' a T.1.length
  rw [← h2, ← hb] at e2
  rw [← hb] at hcut'
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hU
  have htop := red_top hbal.length_eq
  have hbot := red_bot hbal.length_eq
  rw [hl] at htop hbot
  simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons] at htop hbot
  have hUB : IsBlock U := red_isBlock hbal U hU
  have hp : Equiv1 (l₁.map Prod.fst).flatten (l₁.map Prod.snd).flatten :=
    equiv1_join l₁ fun V hV =>
      (red_isBlock hbal V (by rw [hl]; exact List.mem_append_left _ hV)).2.1
  generalize (l₁.map Prod.fst).flatten = p at htop hp
  generalize (l₁.map Prod.snd).flatten = p' at hbot hp
  generalize (l₂.map Prod.fst).flatten = q at htop
  generalize (l₂.map Prod.snd).flatten = q' at hbot
  have hlen1 : (subst t T.1).length = p.length + (U.1.length + q.length) := by
    rw [← htop]; simp
  have hlen2 : (subst t T.2).length = p.length + (U.1.length + q'.length) := by
    rw [← hbot, hp.length_eq, hUB.2.1.length_eq]; simp
  rw [hlen1, ← htop] at e1
  rw [hlen2, ← hbot] at e2
  obtain ⟨hpX, hrX⟩ := win_split e1.symm
  obtain ⟨hU1, -⟩ := win_split hrX
  rw [hp.length_eq] at e2
  obtain ⟨hpX', hrX'⟩ := win_split e2.symm
  rw [hUB.2.1.length_eq] at hrX'
  obtain ⟨hU2, -⟩ := win_split hrX'
  refine ⟨hUB, phi t X a + p.length, ?_, hU1.symm, ?_⟩
  · rw [win_zero_add, win_zero_add, hpX]
    rw [hp.length_eq, hpX']
    exact hcut'.append hp
  · rw [hp.length_eq, hUB.2.1.length_eq]
    exact hU2.symm

/-- With bounded gaps between common cuts, the blocks have bounded length. -/
theorem cutBlocks_length_le {X X' : ℕ → α} {G : ℕ}
    (hG : ∀ k, ∃ k', k < k' ∧ k' ≤ k + G ∧ Equiv1 (win X 0 k') (win X' 0 k'))
    {T : List α × List α} (hT : T ∈ cutBlocks X X') : T.1.length ≤ G := by
  obtain ⟨hB, a, hcut, h1, h2⟩ := hT
  obtain ⟨k', hlt, hle, hk'⟩ := hG a
  by_contra hcon
  have hk : k' - a < T.1.length := by omega
  apply hB.2.2 (k' - a) (by omega) hk
  have e : k' = a + (k' - a) := by omega
  rw [e, win_zero_add, win_zero_add] at hk'
  have h3 := equiv1_cancel hcut hk'
  rw [h1, h2, take_win X a hk.le, take_win X' a hk.le]
  exact h3

theorem cutBlocks_finite [Finite α] {X X' : ℕ → α} {G : ℕ}
    (hG : ∀ k, ∃ k', k < k' ∧ k' ≤ k + G ∧ Equiv1 (win X 0 k') (win X' 0 k')) :
    (cutBlocks X X').Finite := by
  refine ((List.finite_length_le α G).prod (List.finite_length_le α G)).subset ?_
  intro T hT
  have h := cutBlocks_length_le hG hT
  exact ⟨h, by show T.2.length ≤ G; rw [← hT.1.2.1.length_eq]; exact h⟩

theorem cutBlocks_nonempty {X X' : ℕ → α} {G : ℕ}
    (hG : ∀ k, ∃ k', k < k' ∧ k' ≤ k + G ∧ Equiv1 (win X 0 k') (win X' 0 k')) :
    (cutBlocks X X').Nonempty := by
  classical
  have hex : ∃ k, 0 < k ∧ Equiv1 (win X 0 k) (win X' 0 k) := by
    obtain ⟨k', h1, -, h3⟩ := hG 0
    exact ⟨k', h1, h3⟩
  refine ⟨(win X 0 (Nat.find hex), win X' 0 (Nat.find hex)),
    ⟨?_, (Nat.find_spec hex).2, ?_⟩, 0, fun _ => rfl, ?_, ?_⟩
  · intro h0
    have := congrArg List.length h0
    simp only [length_win, List.length_nil] at this
    exact absurd this (Nat.find_spec hex).1.ne'
  · intro k hk hk' hE
    simp only [length_win] at hk'
    rw [take_win X 0 hk'.le, take_win X' 0 hk'.le] at hE
    exact Nat.find_min hex hk' ⟨hk, hE⟩
  · simp
  · simp

/-! ### Coincident blocks give left strong-coincidence witnesses -/

section Witness

variable [Fintype α] {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

/-- For `β > 1` the images `σ^{mn}(c)` of all letters become arbitrarily long. -/
theorem exists_long (hL : LengthData s L β) (hβ : 1 < β) {m : ℕ} (hm : 1 ≤ m) (a : ℕ) :
    ∃ n, ∀ c : α, a < ((subst s)^[m * n] [c]).length := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨0, fun c => (hα.false c).elim⟩
  obtain ⟨δ, hδ0, hδ⟩ := exists_min_len hL.pos
  obtain ⟨a₁, h₁⟩ := Finite.exists_max fun a : α => L (pvec [a])
  have hmax0 : 0 < L (pvec [a₁]) := hL.pos a₁
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a * L (pvec [a₁]) / δ) hβ
  refine ⟨n, fun c => ?_⟩
  have h2 : β ^ n ≤ β ^ (m * n) :=
    pow_le_pow_right₀ hβ.le (Nat.le_mul_of_pos_left n hm)
  have h3 := L_pvec_le h₁ ((subst s)^[m * n] [c])
  rw [pvec_iterate, hL.eigen_pow] at h3
  have h4 : (a : ℝ) * L (pvec [a₁]) < β ^ n * δ := (div_lt_iff₀ hδ0).1 hn
  have h5 : β ^ n * δ ≤ β ^ (m * n) * L (pvec [c]) :=
    mul_le_mul h2 (hδ c) hδ0.le (pow_pos hL.beta_pos _).le
  have h6 : (a : ℝ) * L (pvec [a₁]) < ((subst s)^[m * n] [c]).length * L (pvec [a₁]) := by
    linarith
  exact Nat.cast_lt.1 (lt_of_mul_lt_mul_right h6 hmax0.le)

omit [DecidableEq α] [Fintype α] in
/-- The iterated images of the first letter of a `σ^m`-fixed word are prefixes of it. -/
theorem prefixOf_iterate_first {m : ℕ} {X : ℕ → α} (hX : IsFixed (power s m) X) (n : ℕ) :
    PrefixOf X ((subst s)^[m * n] [X 0]) := by
  have h0 : PrefixOf X [X 0] := by simp [PrefixOf, win]
  have h := prefixOf_iterate hX h0 n
  rwa [subst_power, ← Function.iterate_mul] at h

omit [DecidableEq α] [Fintype α] in
/-- A prefix of `X` longer than `a` splits at index `a`. -/
theorem prefix_split {X : ℕ → α} {W : List α} (hW : PrefixOf X W) {a : ℕ} (ha : a < W.length) :
    W = win X 0 a ++ X a :: win X (a + 1) (W.length - a - 1) := by
  have e : W.length = a + (1 + (W.length - a - 1)) := by omega
  have h : win X 0 W.length = W := hW
  rw [← h]
  simp only [length_win]
  conv_lhs => rw [e, win_zero_add, win_add]
  simp [win]

/-- **Noncoincidence** (step (S)): a coincident block `(x, x)` between common vertices of
two `σ^m`-fixed words gives a left strong-coincidence witness for their first letters. -/
theorem witness_of_coincident_cutBlock (hL : LengthData s L β) (hβ : 1 < β) {m : ℕ}
    (hm : 1 ≤ m) {X X' : ℕ → α} (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    {T : List α × List α} (hT : T ∈ cutBlocks X X') (he : T.1 = T.2) :
    StrongCoincidenceWitness s (X 0) (X' 0) := by
  obtain ⟨hB, a, hcut, h1, h2⟩ := hT
  obtain ⟨c, rfl⟩ := eq_coincidence_of_isBlock hB he
  have hc : X a = c := by
    have : [c] = [X a] := by simpa [win] using h1
    simpa using this.symm
  have hc' : X' a = c := by
    have : [c] = [X' a] := by simpa [win] using h2
    simpa using this.symm
  obtain ⟨n, hn⟩ := exists_long hL hβ hm a
  have e1 := prefix_split (prefixOf_iterate_first hX n) (hn (X 0))
  have e2 := prefix_split (prefixOf_iterate_first hX' n) (hn (X' 0))
  rw [hc] at e1
  rw [hc'] at e2
  exact ⟨m * n, _, _, _, _, c, e1, e2, hcut⟩

end Witness

/-! ### The strict system for `τ = σ^m` -/

section Strict

variable [Fintype α] {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

/-- **Step (S) for `τ = σ^m`.**  If `M^{mN} V_X ⊆ V_{X'}` and the first letters of the two
`σ^m`-fixed words have no left strong-coincidence witness, the blocks between consecutive
common vertices form a strict system for the power substitution `Psc.Binomial.power s m`. -/
theorem strictSystem_power_of_inclusion (hL : LengthData s L β) (hβ : 1 < β) {m : ℕ}
    (hm : 1 ≤ m) {X X' : ℕ → α} (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    {N : ℕ} (hincl : ∀ y ∈ vertexSet X, incZ s ^ (m * N) *ᵥ y ∈ vertexSet X')
    (hnw : ¬ StrongCoincidenceWitness s (X 0) (X' 0)) :
    ∃ C : Finset (List α × List α), (↑C : Set (List α × List α)) = cutBlocks X X' ∧
      StrictSystem (power s m) C := by
  obtain ⟨G, hG⟩ := syndetic_cuts hL hX hincl
  have hfin := cutBlocks_finite hG
  refine ⟨hfin.toFinset, hfin.coe_toFinset, ?_, ?_, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := cutBlocks_nonempty hG
    exact ⟨T, hfin.mem_toFinset.2 hT⟩
  · intro T hT
    exact (hfin.mem_toFinset.1 hT).1
  · intro T hT he
    exact hnw (witness_of_coincident_cutBlock hL hβ hm hX hX' (hfin.mem_toFinset.1 hT) he)
  · intro T hT U hU
    exact hfin.mem_toFinset.2 (cutBlocks_closed hX hX' (hfin.mem_toFinset.1 hT) hU)

end Strict

/-! ### Powers: from a strict system for `σ^m` to one for `σ` -/

section Powers

variable {s : α → List α}

/-- The irreducible factors of `σ^r(C)`, `0 ≤ r < m`. -/
def powerBlocks (s : α → List α) (m : ℕ) (C : Finset (List α × List α)) :
    Finset (List α × List α) :=
  (Finset.range m).biUnion fun r => C.biUnion fun T =>
    (red ((subst s)^[r] T.1) ((subst s)^[r] T.2)).toFinset

theorem mem_powerBlocks {m : ℕ} {C : Finset (List α × List α)} {U : List α × List α} :
    U ∈ powerBlocks s m C ↔
      ∃ r < m, ∃ T ∈ C, U ∈ red ((subst s)^[r] T.1) ((subst s)^[r] T.2) := by
  simp [powerBlocks]

/-- **The "Powers" paragraph** of the cut-pair note §3, in the direction used by Theorem FC1:
for nonerasing `σ` and `m ≥ 1`, the irreducible factors of `σ^r(C)`, `0 ≤ r < m`, of a strict
system `C` for `σ^m` form a strict system for `σ`. -/
theorem strictSystem_of_power (hs : ∀ a, s a ≠ []) {m : ℕ} (hm : 1 ≤ m)
    {C : Finset (List α × List α)} (h : StrictSystem (power s m) C) :
    StrictSystem s (powerBlocks s m C) := by
  have hC : ∀ T ∈ C, T ∈ powerBlocks s m C := fun T hT =>
    mem_powerBlocks.2 ⟨0, hm, T, hT, by
      rw [Function.iterate_zero_apply, Function.iterate_zero_apply,
        red_of_isBlock (h.isBlock T hT)]
      exact List.mem_singleton.2 rfl⟩
  have hlevel : ∀ T ∈ C, ∀ V ∈ red ((subst s)^[m] T.1) ((subst s)^[m] T.2), V ∈ C := by
    intro T hT V hV
    rw [← subst_power] at hV
    exact h.closed T hT V hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := h.nonempty
    exact ⟨T, hC T hT⟩
  · intro U hU
    obtain ⟨r, -, T, hT, hU⟩ := mem_powerBlocks.1 hU
    exact red_isBlock (equiv1_iterate_subst s r (h.equiv1 T hT)) U hU
  · intro U hU he
    obtain ⟨r, hr, T, hT, hU⟩ := mem_powerBlocks.1 hU
    have hbal := equiv1_iterate_subst s r (h.equiv1 T hT)
    have hUB := red_isBlock hbal U hU
    -- the factors of `σ^{m-r}(U)` are factors of `σ^m(T)`, hence states of `C`
    have hsub : ∀ V ∈ red ((subst s)^[m - r] U.1) ((subst s)^[m - r] U.2), V ∈ C := by
      intro V hV
      apply hlevel T hT V
      have e : m = (m - r) + r := by omega
      rw [e, Function.iterate_add_apply, Function.iterate_add_apply,
        red_iterate_subst s (m - r) hbal]
      exact List.mem_flatMap.2 ⟨U, hU, hV⟩
    rw [← he, red_self] at hsub
    obtain ⟨c, w, hw⟩ := List.exists_cons_of_ne_nil
      (Psc.FixedPointLimit.iterate_subst_ne_nil s hs (m - r) hUB.1)
    have hmem : (([c], [c]) : List α × List α) ∈ C := hsub _ (by rw [hw]; simp)
    exact h.noncoincident _ hmem rfl
  · intro U hU V hV
    obtain ⟨r, hr, T, hT, hU⟩ := mem_powerBlocks.1 hU
    have hbal := equiv1_iterate_subst s r (h.equiv1 T hT)
    have hV' : V ∈ red ((subst s)^[r + 1] T.1) ((subst s)^[r + 1] T.2) := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', red_subst s hbal]
      exact List.mem_flatMap.2 ⟨U, hU, hV⟩
    by_cases hlt : r + 1 < m
    · exact mem_powerBlocks.2 ⟨r + 1, hlt, T, hT, hV'⟩
    · have e : r + 1 = m := by omega
      rw [e] at hV'
      exact hC V (hlevel T hT V hV')

end Powers

/-! ### Theorem FC1 (3) -/

section Main

variable [Fintype α] {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}

/-- **Theorem FC1 (3)**, in abstract form.  Let `L` be length data for `σ` with `β > 1`, let
`X`, `X'` be fixed by `σ^m`, `m ≥ 1`, and assume (Fin) the set of relative states is finite
and (F) each of them reaches a vertex state under the prototile state map.  If the first
letters of `X`, `X'` have no left strong-coincidence witness
(`Psc.StrictSystem.StrongCoincidenceWitness`), then the blocks of `(X, X')` between
consecutive common vertices are a strict system (`Psc.StrictSystem.StrictSystem`) for
`σ^m`, and `σ` has a strict system. -/
theorem fc1_strictSystem (hL : LengthData s L β) (hβ : 1 < β) {m : ℕ} (hm : 1 ≤ m)
    {X X' : ℕ → α} (hX : IsFixed (power s m) X) (hX' : IsFixed (power s m) X')
    (hFin : (relStates L X X').Finite)
    (hF : ∀ x ∈ relStates L X X', ∃ n a, StepN s L n x (a, 0))
    (hnw : ¬ StrongCoincidenceWitness s (X 0) (X' 0)) :
    (∃ C : Finset (List α × List α), (↑C : Set (List α × List α)) = cutBlocks X X' ∧
      StrictSystem (power s m) C) ∧ ∃ C : Finset (List α × List α), StrictSystem s C := by
  obtain ⟨N, hN⟩ := inclusion hL hm hX hX' hFin hF
  obtain ⟨C, hC, hstrict⟩ := strictSystem_power_of_inclusion hL hβ hm hX hX'
    (N := N) (fun y hy => (hN y (Or.inl hy)).2) hnw
  exact ⟨⟨C, hC, hstrict⟩, _, strictSystem_of_power hL.nonerasing hm hstrict⟩

end Main

/-! ### Periodic letters, their fixed rays, and the equivalence on (F) -/

section Equivalence

variable {s : α → List α}

/-- `c` is a **`g`-periodic letter**: `σ^k(c)` begins with `c` for some `k ≥ 1`
(`isPeriodicLetter_iff`: `g^k(c) = c` for the first-letter map `g`). -/
def IsPeriodicLetter {α : Type*} (s : α → List α) (c : α) : Prop :=
  ∃ k, 1 ≤ k ∧ [c] <+: (subst s)^[k] [c]

omit [DecidableEq α] in
/-- The first letter of `σ^k(c)` is `g^k(c)`, `g(a)` the first letter of `σ(a)`. -/
theorem iterate_first (hs : ∀ a, s a ≠ []) (k : ℕ) (c : α) :
    ∃ w, (subst s)^[k] [c] = (fun a => (s a).head (hs a))^[k] c :: w := by
  induction k generalizing c with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih ((s c).head (hs c))
    refine ⟨w ++ (subst s)^[k] (s c).tail, ?_⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have e : subst s [c] = [(s c).head (hs c)] ++ (s c).tail := by
      simp [subst]
    rw [e, iterate_subst_append, hw]
    rfl

omit [DecidableEq α] in
theorem isPeriodicLetter_iff (hs : ∀ a, s a ≠ []) (c : α) :
    IsPeriodicLetter s c ↔ ∃ k, 1 ≤ k ∧ (fun a => (s a).head (hs a))^[k] c = c := by
  constructor
  · rintro ⟨k, hk, hp⟩
    obtain ⟨w, hw⟩ := iterate_first hs k c
    rw [hw] at hp
    obtain ⟨t, ht⟩ := hp
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
    exact ⟨k, hk, ht.1.symm⟩
  · rintro ⟨k, hk, hg⟩
    obtain ⟨w, hw⟩ := iterate_first hs k c
    exact ⟨k, hk, by rw [hw, hg]; exact ⟨w, rfl⟩⟩

theorem prefix_iterate_mul {c : α} {k : ℕ} (h : [c] <+: (subst s)^[k] [c]) (n : ℕ) :
    [c] <+: (subst s)^[k * n] [c] := by
  have := Psc.FixedPointLimit.chain_mono s h 0 n (Nat.zero_le n)
  simpa using this

/-- The limit word of `Psc.FixedPointLimit` is a fixed point of the power substitution in
the sense of `Psc.BPrimeBinding.IsFixed`. -/
theorem isFixed_limit {u : List α} {p : ℕ} (hu : u <+: (subst s)^[p] u)
    (hgrow : ∀ m, ∃ n, m < ((subst s)^[p * n] u).length) :
    IsFixed (power s p) (Psc.FixedPointLimit.limit s u p hgrow) := by
  intro N
  unfold PrefixOf
  rw [subst_power, win_zero_eq, win_zero_eq]
  exact Psc.FixedPointLimit.limit_fixed_eq s hu hgrow N

/-- **The rays exist**: a letter `c` such that `σ^m(c)` begins with `c` is the first letter of
a `σ^m`-fixed right-infinite word (length data with `β > 1`, `m ≥ 1`). -/
theorem exists_fixed_ray [Fintype α] {L : (α → ℤ) →+ ℝ} {β : ℝ} (hL : LengthData s L β)
    (hβ : 1 < β) {m : ℕ} (hm : 1 ≤ m) {c : α} (hc : [c] <+: (subst s)^[m] [c]) :
    ∃ X : ℕ → α, IsFixed (power s m) X ∧ X 0 = c := by
  have hgrow : ∀ M, ∃ n, M < ((subst s)^[m * n] [c]).length := fun M =>
    let ⟨n, hn⟩ := exists_long hL hβ hm M
    ⟨n, hn c⟩
  refine ⟨Psc.FixedPointLimit.limit s [c] m hgrow, isFixed_limit hc hgrow, ?_⟩
  rw [Psc.FixedPointLimit.limit_zero s hc hgrow (by simp)]
  rfl

/-- A left strong-coincidence witness for `gⁿ(a), gⁿ(b)` is one for `a, b`, read in the
first images. -/
theorem witness_of_iterate_first (hs : ∀ a, s a ≠ []) (n : ℕ) {a b : α}
    (h : StrongCoincidenceWitness s ((fun a => (s a).head (hs a))^[n] a)
      ((fun a => (s a).head (hs a))^[n] b)) : StrongCoincidenceWitness s a b := by
  obtain ⟨k, P, Q, P', Q', x, h1, h2, hP⟩ := h
  obtain ⟨w, hw⟩ := iterate_first hs n a
  obtain ⟨w', hw'⟩ := iterate_first hs n b
  refine ⟨k + n, P, Q ++ (subst s)^[k] w, P', Q' ++ (subst s)^[k] w', x, ?_, ?_, hP⟩
  · rw [Function.iterate_add_apply, hw,
      show ∀ (y : α) (t : List α), y :: t = [y] ++ t from fun _ _ => rfl,
      iterate_subst_append, h1]
    simp
  · rw [Function.iterate_add_apply, hw',
      show ∀ (y : α) (t : List α), y :: t = [y] ++ t from fun _ _ => rfl,
      iterate_subst_append, h2]
    simp

/-- Equal first letters of `σⁿ(a)`, `σⁿ(b)` are a witness with empty prefixes. -/
theorem witness_of_iterate_first_eq (hs : ∀ a, s a ≠ []) (n : ℕ) {a b : α}
    (h : (fun a => (s a).head (hs a))^[n] a = (fun a => (s a).head (hs a))^[n] b) :
    StrongCoincidenceWitness s a b := by
  obtain ⟨w, hw⟩ := iterate_first hs n a
  obtain ⟨w', hw'⟩ := iterate_first hs n b
  rw [← h] at hw'
  exact ⟨n, [], w, [], w', _, hw, hw', fun _ => rfl⟩

/-- A pair of distinct letters that is not left strongly coincident is carried by the
first-letter map to a pair of distinct `g`-periodic letters that is not left strongly
coincident (the last paragraph of the proof of Theorem FC1). -/
theorem exists_periodic_pair [Finite α] (hs : ∀ a, s a ≠ []) {a b : α}
    (hnw : ¬ StrongCoincidenceWitness s a b) :
    ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
      ¬ StrongCoincidenceWitness s c c' := by
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => ((fun a => (s a).head (hs a))^[n] a, (fun a => (s a).head (hs a))^[n] b))
  wlog h : i < j generalizing i j
  · exact this j i hij.symm he.symm (lt_of_le_of_ne (not_lt.1 h) hij.symm)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  simp only [Prod.mk.injEq] at he
  have e : d + 1 + i = i + d + 1 := by omega
  refine ⟨_, _, fun e => hnw (witness_of_iterate_first_eq hs i e),
    (isPeriodicLetter_iff hs _).2 ⟨d + 1, by omega, ?_⟩,
    (isPeriodicLetter_iff hs _).2 ⟨d + 1, by omega, ?_⟩,
    fun hw => hnw (witness_of_iterate_first hs i hw)⟩
  · rw [← Function.iterate_add_apply, e]
    exact he.1.symm
  · rw [← Function.iterate_add_apply, e]
    exact he.2.symm

variable [Fintype α] {L : (α → ℤ) →+ ℝ} {β : ℝ}

/-- **Theorem FC1 (3) for periodic letters.**  Under length data with `β > 1`, (Fin) and
"every state reaches a vertex state": two `g`-periodic letters without a left
strong-coincidence witness give a strict system. -/
theorem strictSystem_of_periodic_pair (hL : LengthData s L β) (hβ : 1 < β)
    (hFin : ∀ m, 1 ≤ m → ∀ X X' : ℕ → α, IsFixed (power s m) X → IsFixed (power s m) X' →
      (relStates L X X').Finite)
    (hF : ∀ x, IsState L x → ∃ n a, StepN s L n x (a, 0)) {c c' : α}
    (hc : IsPeriodicLetter s c) (hc' : IsPeriodicLetter s c')
    (hnw : ¬ StrongCoincidenceWitness s c c') :
    ∃ C : Finset (List α × List α), StrictSystem s C := by
  obtain ⟨k, hk, hp⟩ := hc
  obtain ⟨k', hk', hp'⟩ := hc'
  have hm : 1 ≤ k * k' := Nat.mul_pos hk hk'
  have h1 := prefix_iterate_mul hp k'
  have h2 := prefix_iterate_mul hp' k
  rw [Nat.mul_comm] at h2
  obtain ⟨X, hX, hX0⟩ := exists_fixed_ray hL hβ hm h1
  obtain ⟨X', hX', hX'0⟩ := exists_fixed_ray hL hβ hm h2
  rw [← hX0, ← hX'0] at hnw
  exact (fc1_strictSystem hL hβ hm hX hX' (hFin _ hm X X' hX hX')
    (fun x hx => hF x (relStates_isState hx)) hnw).2

/-- **Theorem FC1, the equivalences**, in abstract form: under length data with `β > 1`,
(Fin) for every pair of fixed rays, and "every state reaches a vertex state", the following
are equivalent: `σ` has a strict system; some pair of distinct `g`-periodic letters has no
left strong-coincidence witness; left strong coincidence fails for some pair of distinct
letters.  The implication from a strict system is Theorem A of the cut-pair note
(`Psc.StrictSystem.no_strictSystem_of_strongCoincidence`) and uses none of the hypotheses. -/
theorem fc1_equivalence (hL : LengthData s L β) (hβ : 1 < β)
    (hFin : ∀ m, 1 ≤ m → ∀ X X' : ℕ → α, IsFixed (power s m) X → IsFixed (power s m) X' →
      (relStates L X X').Finite)
    (hF : ∀ x, IsState L x → ∃ n a, StepN s L n x (a, 0)) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') := by
  have h13 : (∃ C : Finset (List α × List α), StrictSystem s C) →
      ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c' :=
    fun ⟨C, hC⟩ hw => Psc.StrictSystem.no_strictSystem_of_strongCoincidence hw C hC
  have h32 : (¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') →
      ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
        ¬ StrongCoincidenceWitness s c c' := by
    intro h
    obtain ⟨a, h⟩ := not_forall.1 h
    obtain ⟨b, h⟩ := not_forall.1 h
    obtain ⟨-, hnw⟩ := Classical.not_imp.1 h
    exact exists_periodic_pair hL.nonerasing hnw
  have h21 : (∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
      ¬ StrongCoincidenceWitness s c c') → ∃ C : Finset (List α × List α), StrictSystem s C :=
    fun ⟨_, _, _, hc, hc', hnw⟩ => strictSystem_of_periodic_pair hL hβ hFin hF hc hc' hnw
  exact ⟨⟨fun h => h32 (h13 h), h21⟩, ⟨h13, fun h => h21 (h32 h)⟩⟩

/-- **Theorem FC1**, with (Fin) discharged from contraction data and (F) in the note's form
(`PropertyF`: no `f`-periodic state has `v ≠ 0`): `σ` has a strict system iff some pair of
distinct `g`-periodic letters is not left strongly coincident iff left strong coincidence
fails. -/
theorem fc1_equivalence_of_contraction {ν : (α → ℤ) → ℝ} {ρ : ℝ} (hL : LengthData s L β)
    (hβ : 1 < β) (hc : ContractionData s L ν ρ) (hF : PropertyF s L) :
    ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter s c ∧ IsPeriodicLetter s c' ∧
          ¬ StrongCoincidenceWitness s c c') ∧
      ((∃ C : Finset (List α × List α), StrictSystem s C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness s c c') :=
  fc1_equivalence hL hβ
    (fun _ hm _ _ hX hX' => relStates_finite_of_contraction hL hc hm hX hX')
    (fun _ hx => reaches_vertex_of_propertyF hL hc hF hx)

end Equivalence

/-! ### Binding: length data from a positive left eigenvector -/

section Binding

variable [Fintype α]

/-- **Length data from the left Perron eigenvector of a primitive substitution**
(`Psc.PerronExistence.exists_pos_left_eigen_inc`). -/
theorem exists_lengthData_of_primitive (s : α → List α)
    (hprim : ∃ k ≥ 1, ∀ a c, 0 < (inc s ^ k) a c) :
    ∃ (β : ℝ) (ℓ : α → ℝ), (∀ a, 0 < ℓ a) ∧ LengthData s (lenHom ℓ) β := by
  obtain ⟨β, hβ, ℓ, hℓ, h⟩ := Psc.PerronExistence.exists_pos_left_eigen_inc s hprim
  exact ⟨β, ℓ, hℓ, lengthData_of_left_eigen hβ hℓ h⟩

/-! ### Non-vacuity: the hypotheses hold jointly on Thue–Morse -/

/-- Tile lengths `(1, 1)` for Thue–Morse. -/
noncomputable def tmL : (Fin 2 → ℤ) →+ ℝ := lenHom fun _ => 1

/-- The stable size `|v₀ − v₁|` for Thue–Morse (`M` kills the antidiagonal). -/
def tmNu (v : Fin 2 → ℤ) : ℝ := |((v 0 - v 1 : ℤ) : ℝ)|

theorem tmL_apply (v : Fin 2 → ℤ) : tmL v = ((v 0 + v 1 : ℤ) : ℝ) := by
  simp [tmL, lenHom_apply, Fin.sum_univ_two]

theorem tm_mulVec (v : Fin 2 → ℤ) (a : Fin 2) : (incZ thueMorseSubst *ᵥ v) a = v 0 + v 1 := by
  fin_cases a <;> simp [incZ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, thueMorseSubst]

theorem tm_lengthData : LengthData thueMorseSubst tmL 2 := by
  refine lengthData_of_left_eigen (by norm_num) (fun _ => by norm_num) ?_
  funext c
  fin_cases c <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, thueMorseSubst] <;> norm_num

theorem tm_contractionData : ContractionData thueMorseSubst tmL tmNu 0 where
  rho_nonneg := le_rfl
  rho_lt_one := by norm_num
  add_le v w := by
    have e : ((((v + w) 0 - (v + w) 1 : ℤ)) : ℝ) =
        ((v 0 - v 1 : ℤ) : ℝ) + ((w 0 - w 1 : ℤ) : ℝ) := by
      push_cast [Pi.add_apply]; ring
    simp only [tmNu]
    rw [e]
    exact abs_add_le _ _
  neg v := by
    have e : ((((-v) 0 - (-v) 1 : ℤ)) : ℝ) = -((v 0 - v 1 : ℤ) : ℝ) := by
      push_cast [Pi.neg_apply]; ring
    simp only [tmNu]
    rw [e, abs_neg]
  contract v := by
    simp [tmNu, tm_mulVec]
  proper a b := by
    refine (Set.Finite.pi fun _ : Fin 2 => Set.finite_Icc (-⌈a + b⌉) ⌈a + b⌉).subset ?_
    intro v hv
    obtain ⟨h1, h2⟩ := hv
    rw [tmL_apply] at h1
    simp only [tmNu] at h2
    rw [abs_le] at h1 h2
    push_cast at h1 h2
    have hc := Int.le_ceil (a + b)
    have hv0 : ((v 0 : ℤ) : ℝ) ≤ ((⌈a + b⌉ : ℤ) : ℝ) ∧
        ((-⌈a + b⌉ : ℤ) : ℝ) ≤ ((v 0 : ℤ) : ℝ) := by
      push_cast
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hv1 : ((v 1 : ℤ) : ℝ) ≤ ((⌈a + b⌉ : ℤ) : ℝ) ∧
        ((-⌈a + b⌉ : ℤ) : ℝ) ≤ ((v 1 : ℤ) : ℝ) := by
      push_cast
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    intro i _
    have hi : ((v i : ℤ) : ℝ) ≤ ((⌈a + b⌉ : ℤ) : ℝ) ∧
        ((-⌈a + b⌉ : ℤ) : ℝ) ≤ ((v i : ℤ) : ℝ) := by
      fin_cases i
      · exact hv0
      · exact hv1
    exact Set.mem_Icc.2 ⟨Int.cast_le.1 hi.2, Int.cast_le.1 hi.1⟩

theorem tm_step_vertex {x y : Fin 2 × (Fin 2 → ℤ)} (hx : IsState tmL x)
    (h : Step thueMorseSubst tmL x y) : y.2 = 0 := by
  have hx0 : x.2 0 + x.2 1 = 0 := by
    obtain ⟨h0, h1⟩ := hx
    rw [tmL_apply] at h0 h1
    have e1 : tmL (pvec [x.1]) = 1 := by simp [tmL, lenHom_single]
    rw [e1] at h1
    have h0' : (0 : ℤ) ≤ x.2 0 + x.2 1 := by exact_mod_cast h0
    have h1' : x.2 0 + x.2 1 < (1 : ℤ) := by exact_mod_cast h1
    omega
  have hM : incZ thueMorseSubst *ᵥ x.2 = 0 := by
    funext a
    rw [tm_mulVec, hx0]; rfl
  obtain ⟨P, S, -, hy, hs0, -⟩ := h
  rw [hM, zero_sub] at hy
  rw [hy, map_neg] at hs0
  have hP : P = [] := by
    by_contra hne
    linarith [L_pvec_pos tm_lengthData.pos hne]
  rw [hy, hP, pvec_nil, neg_zero]

/-- Thue–Morse satisfies property (F) in the abstract sense (every state is mapped to a
vertex state by one application of `f`). -/
theorem tm_propertyF : PropertyF thueMorseSubst tmL := by
  intro x hx k hk hper
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm] at hper
  obtain ⟨z, hz, hzx⟩ := hper
  exact tm_step_vertex (stepN_isState hx k hz) hzx

/-- **Non-vacuity of Theorem FC1.**  All hypotheses of `fc1_equivalence_of_contraction`
hold jointly for Thue–Morse `01/10` (a negative control of the note, §9: not PIP3, `ℓ = (1,1)`
is not injective), and its three equivalent statements are all true there
(`Psc.StrictSystem.tm_strictSystem`, `tm_no_witness`). -/
theorem tm_fc1 :
    ((∃ C : Finset (List (Fin 2) × List (Fin 2)), StrictSystem thueMorseSubst C) ↔
        ∃ c c', c ≠ c' ∧ IsPeriodicLetter thueMorseSubst c ∧
          IsPeriodicLetter thueMorseSubst c' ∧
          ¬ StrongCoincidenceWitness thueMorseSubst c c') ∧
      ((∃ C : Finset (List (Fin 2) × List (Fin 2)), StrictSystem thueMorseSubst C) ↔
        ¬ ∀ c c', c ≠ c' → StrongCoincidenceWitness thueMorseSubst c c') :=
  fc1_equivalence_of_contraction tm_lengthData (by norm_num) tm_contractionData tm_propertyF

/-- The conclusion of `tm_fc1` is not vacuous: Thue–Morse has a pair of distinct
`g`-periodic letters without a left strong-coincidence witness. -/
theorem tm_periodic_pair : ∃ c c' : Fin 2, c ≠ c' ∧ IsPeriodicLetter thueMorseSubst c ∧
    IsPeriodicLetter thueMorseSubst c' ∧ ¬ StrongCoincidenceWitness thueMorseSubst c c' :=
  tm_fc1.1.1 ⟨_, Psc.StrictSystem.tm_strictSystem⟩

end Binding

/-! ### Negative controls: an eigenvalue `±1` excludes contraction data -/

section Controls

variable [Fintype α]

/-- **Negative control.**  If `M` has a nonzero integer eigenvector for the eigenvalue `1` or
`−1`, then no contraction data exist for any length data with `β > 1`: the multiples of the
eigenvector have length `0` and size `0`, against properness.  This is where the proof of
Theorem FC1 stops on the reducible strict controls (the eigenvalue `±1` is not contracted
and `ℓ` is not injective). -/
theorem not_contractionData_of_unit_eigenvector {s : α → List α} {L : (α → ℤ) →+ ℝ} {β : ℝ}
    {ν : (α → ℤ) → ℝ} {ρ : ℝ} (hL : LengthData s L β) (hβ : 1 < β) {w : α → ℤ} (hw : w ≠ 0)
    (h : incZ s *ᵥ w = w ∨ incZ s *ᵥ w = -w) : ¬ ContractionData s L ν ρ := by
  intro hc
  have hν : ν w = 0 := by
    have h1 : ν (incZ s *ᵥ w) = ν w := by
      rcases h with h | h
      · rw [h]
      · rw [h, hc.neg]
    have h2 := hc.contract w
    rw [h1] at h2
    by_contra hne
    have h3 : 0 < ν w := lt_of_le_of_ne (hc.nonneg w) (Ne.symm hne)
    have h4 := mul_lt_mul_of_pos_right hc.rho_lt_one h3
    linarith
  have hLw : L w = 0 := by
    have h1 := hL.eigen w
    rcases h with h | h
    · rw [h] at h1
      have h2 : (β - 1) * L w = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · exact h3
    · rw [h, map_neg] at h1
      have h2 : (β + 1) * L w = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h3 | h3
      · linarith
      · exact h3
  have hmul : ∀ k : ℕ, ν (k • w) ≤ 0 ∧ L (k • w) = 0 := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, by simp⟩
      have h1 := hc.add_le w (-w)
      rw [add_neg_cancel, hc.neg, hν] at h1
      simpa using h1
    | succ k ih =>
      refine ⟨?_, by rw [map_nsmul, hLw, smul_zero]⟩
      rw [succ_nsmul]
      have h1 := hc.add_le (k • w) w
      rw [hν] at h1
      linarith [ih.1]
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hw
  have hinj : Function.Injective fun k : ℕ => k • w := by
    intro k k' hkk
    have h1 := congrFun hkk a
    simp only [Pi.smul_apply, nsmul_eq_mul] at h1
    have h2 : (k : ℤ) = k' := mul_right_cancel₀ ha h1
    exact_mod_cast h2
  refine (Set.infinite_range_of_injective hinj) ((hc.proper 0 0).subset ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨by rw [(hmul k).2]; simp, (hmul k).1⟩

/-- The reducible strict control `10/102/211` (`Psc.StrictSystem.carrierSubst`,
`χ = (x − 1)(x² − 2x − 2)`, a four-state strict sink): `M (2, 0, −1) = (2, 0, −1)`, so no
contraction data exist, whatever the length data. -/
theorem carrier_not_contractionData {L : (Fin 3 → ℤ) →+ ℝ} {β : ℝ} {ν : (Fin 3 → ℤ) → ℝ}
    {ρ : ℝ} (hL : LengthData Psc.StrictSystem.carrierSubst L β) (hβ : 1 < β) :
    ¬ ContractionData Psc.StrictSystem.carrierSubst L ν ρ :=
  not_contractionData_of_unit_eigenvector hL hβ (w := ![2, 0, -1]) (by decide)
    (Or.inl (by decide))

/-- Length data exist on `10/102/211` (it is primitive, `Psc.StrictSystem.carrier_primitive`),
so `carrier_not_contractionData` is not vacuous: the hypothesis of Theorem FC1 that fails on
this strict control is the contraction one. -/
theorem carrier_lengthData : ∃ (β : ℝ) (ℓ : Fin 3 → ℝ), (∀ a, 0 < ℓ a) ∧
    LengthData Psc.StrictSystem.carrierSubst (lenHom ℓ) β :=
  exists_lengthData_of_primitive _ Psc.StrictSystem.carrier_primitive

/-- C-D1 `011/120/2012` (`χ = (x − 1)(x² − 3x − 1)`; its strict system is pinned in
`kernel/tests/test_c4_reducible_pisot_controls.mojo`, not in Lean). -/
def cd1Subst : Fin 3 → List (Fin 3) := ![[0, 1, 1], [1, 2, 0], [2, 0, 1, 2]]

/-- C-D2 `010/1222/2012` (`χ = (x − 1)(x² − 4x + 1)`; pinned in the same Mojo test). -/
def cd2Subst : Fin 3 → List (Fin 3) := ![[0, 1, 0], [1, 2, 2, 2], [2, 0, 1, 2]]

/-- `1/012/101` (`χ = (x + 1)(x² − 2x − 1)`; pinned in the same Mojo test). -/
def minusOneSubst : Fin 3 → List (Fin 3) := ![[1], [0, 1, 2], [1, 0, 1]]

/-- `01/201/112`, the image-wise reversal of `10/102/211` (the same incidence matrix). -/
def carrierRevSubst : Fin 3 → List (Fin 3) := ![[0, 1], [2, 0, 1], [1, 1, 2]]

/-- **Where Theorem FC1 stops on the reducible strict controls with an irrational Pisot
inflation**: on `011/120/2012`, `010/1222/2012`, `01/201/112` (eigenvalue `1`) and
`1/012/101` (eigenvalue `−1`) no contraction data exist, whatever the length data.  The
eigenvectors are `(1, 2, −2)`, `(3, 1, −3)`, `(2, 0, −1)` and `(0, 1, −1)`. -/
theorem reducible_controls_not_contractionData {L : (Fin 3 → ℤ) →+ ℝ} {β : ℝ}
    {ν : (Fin 3 → ℤ) → ℝ} {ρ : ℝ} (hβ : 1 < β) :
    (LengthData cd1Subst L β → ¬ ContractionData cd1Subst L ν ρ) ∧
      (LengthData cd2Subst L β → ¬ ContractionData cd2Subst L ν ρ) ∧
      (LengthData carrierRevSubst L β → ¬ ContractionData carrierRevSubst L ν ρ) ∧
      (LengthData minusOneSubst L β → ¬ ContractionData minusOneSubst L ν ρ) :=
  ⟨fun hL => not_contractionData_of_unit_eigenvector hL hβ (w := ![1, 2, -2]) (by decide)
      (Or.inl (by decide)),
    fun hL => not_contractionData_of_unit_eigenvector hL hβ (w := ![3, 1, -3]) (by decide)
      (Or.inl (by decide)),
    fun hL => not_contractionData_of_unit_eigenvector hL hβ (w := ![2, 0, -1]) (by decide)
      (Or.inl (by decide)),
    fun hL => not_contractionData_of_unit_eigenvector hL hβ (w := ![0, 1, -1]) (by decide)
      (Or.inr (by decide))⟩

end Controls

end Psc.GeometricF
