/-
# The literal occurrence graph

The middle layer of the packet square (roadmap immediate-sequence item 2;
`docs/packet-square-stop-go-2026-11-10.md`).  A vertex is a literal occurrence
pair `Occ`: an ordered block `(u, v)` (no side-swap normalisation), one selected
letter occurrence on each track, and the birth record of the block (the oriented
parent block and the ordinal of the block among the children
`red (σ parent.1) (σ parent.2)`; `none` at a root).  On it:

* `occStep s x d e`: the literal one-step descendant of `x` along the digit pair
  `(d, e)`; both inflated positions are located in the blocks of
  `red (σ u) (σ v)`, and the outcome is the child occurrence pair (both in one
  block, birth record included) or a `split` with the two ordinals;
  `occStep_child_iff` is the outcome as arithmetic on `blockStart`, and
  `mem_occStar` says the star `occStar s x` of a noncoincident `x` lists exactly
  the digit pairs that have an outcome, each with its outcome;
* the addendum's fields as definitions and lemmas: both source occurrence
  addresses (`Occ.topAddr`, `Occ.botAddr`; `occStep_addr`: on every literal
  edge they are `(x.top, d, global, local)` and `(x.bot, e, global, local)`),
  the chosen indices (the digits; `occStep_digits_unique`), ordered parent /
  ordinal / child (`Occ.Valid`, `occChild.valid`), orientation (`Occ.swap`,
  `occStep_swap`, `Occ.residual_swap`), residual Parikh (`Occ.residual`, a
  definition), strict interior / boundary (`Occ.Interior`, `Occ.Boundary`, both
  decidable, `Occ.atStart_iff`) and the target (`Occ.Coincident`,
  `Occ.SuccessFor`);
* `residual_step`: along every literal edge `r' = M r + λ`, derived from the
  committed `Psc.OccurrenceAddress.residual_transport` with the balanced cut at
  the start of the child block; `residual_step_vec`, `residual_atStart`
  (`M r + λ = 0` at a child start) and `residual_iterate_lt` (along the first
  `n` steps of a path, which may end there, for instance at a dead end or at a
  coincidence block) are its vector, start and iterated forms;
  `residual_iterate` is the iterated form for an infinite literal lineage;
* `occChild_finite`: finitely many literal children; `occChild.childNC`: every
  literal edge lies over a `ChildNC` edge of the balanced-pair automaton;
* `occGraph s` (target: the coincidence blocks, as in `bpaGraph`) and
  `occGraphFor s target` (target: the packet success, an interior coincidence,
  on the diagonal `c/c` when `target = some c`) as
  `Psc.QuantifierInterface.ChildGraph` values;
* `occStep_isSome` and `length_occStar`: at a balanced block every digit pair in
  range has an outcome, so the star of a noncoincident occurrence pair has
  exactly `|σ a| · |σ b|` entries, children and splits together;
  `occStep_split_iff` locates a split; `rs_unbalanced_step_none` shows that the
  balance hypothesis is needed (a digit pair in range with no outcome at an
  unbalanced block, which is not the block of any valid occurrence pair);
* controls: `fibDead_star` (Fibonacci `0 ↦ 01, 1 ↦ 0`, the valid occurrence
  pair at positions `(1, 0)` of the root `(01, 10)` has a single digit pair,
  which splits, while the block has a balanced-pair child,
  `fibDead_block_child`), and the archived rows 209 and 429 of the
  real-secondary specimen `1/02/202`
  (`evidence/target-aware-bpa-2026-10-02/real-secondary.jsonl`) decoded as
  literal occurrence pairs: both valid, the two literal steps
  `209 -(0,0)-> 429 -(0,2)-> 209` (`rs_rows_edges`), out of noncoincident
  blocks, hence a 2-cycle of `occGraph` (`rs_rows_occGraph`), both full stars,
  the archived addresses, letters, residuals `(-1,1,0)`, `(1,-1,1)`, forcings
  and interior bits re-derived from the definitions, and the transport law on
  both edges.

The definitions and most lemmas were first checked in the scratch files of the
packet-square design pass; `cutAddr`, `blockStart`, `getElem_red`,
`take_subst_digit` and `residual_transport` are imported from
`Psc.OccurrenceAddress`, not redefined.

Not proved here: that any packet table or Mojo packet graph is sound or complete
with respect to this graph (no packet row is read by a theorem of this module);
any statement about absolute occurrences in the iterates `σⁿ(T₀)` or about
reading them as occurrence pairs; any refinement statement for the block
projection `Occ.block` beyond `occChild.childNC` (soundness from some or from
every source is not stated; the Fibonacci control records one dead end over a
state with a child, and the refinement consequence belongs to the realisation
layer); that any occurrence pair is productive, inevitable or realised by an
infinite lineage; that the Mojo `interior`/`success` bits equal
`Occ.Interior`/`Occ.SuccessFor`; anything about C4, G1 or the Pisot
substitution conjecture, none of which is advanced here.  The rows 209 and 429
are a calibration of the definitions on two hand-decoded archived rows, not a
check of the archive.
-/
import PscVerif.QuantifierBinding
import PscVerif.Incidence
import PscVerif.OccurrenceAddress

namespace Psc.OccurrenceGraph

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.Incidence
open Psc.QuantifierInterface Psc.QuantifierBinding
open Psc.OccurrenceAddress

variable {α : Type*} [DecidableEq α]

/-! ### Definitions -/

/-- `imgStart s w i = |σ(w[:i])|`: the offset in `σ w` of the image of the letter `w[i]`. -/
def imgStart (s : α → List α) (w : List α) (i : ℕ) : ℕ := (subst s (w.take i)).length

/-- The ordinal of the block covering position `p`; `none` beyond the last block. -/
def blockAt : List (List α × List α) → ℕ → Option ℕ
  | [], _ => none
  | T :: bs, p => if p < T.1.length then some 0 else (blockAt bs (p - T.1.length)).map (· + 1)

/-- Birth record of a block occurrence: the oriented parent block and the ordinal of the
child among the blocks of `red (σ parent.1) (σ parent.2)`. -/
structure Birth (α : Type*) where
  parent : List α × List α
  ordinal : ℕ
  deriving DecidableEq

/-- A literal occurrence pair: an ordered block (no side-swap normalisation), one selected
letter occurrence on each track, and the birth record of the block (`none` at a root). -/
structure Occ (α : Type*) where
  block : List α × List α
  top : ℕ
  bot : ℕ
  birth : Option (Birth α)
  deriving DecidableEq

/-- What a digit pair does to an occurrence pair. -/
inductive Outcome (α : Type*) where
  /-- both descendants lie in one block: the child occurrence pair -/
  | child (y : Occ α)
  /-- the descendants lie in different blocks, with ordinals `kTop ≠ kBot` -/
  | split (kTop kBot : ℕ)
  deriving DecidableEq

/-- The literal one-step descendant of `x` along the digit pair `(d, e)`.
`none`: a position or a digit is out of range, or (only at an unbalanced block; see
`occStep_isSome` and `rs_unbalanced_step_none`) an inflated position lies in no block of the
reduction. -/
def occStep (s : α → List α) (x : Occ α) (d e : ℕ) : Option (Outcome α) :=
  match x.block.1[x.top]?, x.block.2[x.bot]? with
  | some a, some b =>
    if d < (s a).length ∧ e < (s b).length then
      let bs := red (subst s x.block.1) (subst s x.block.2)
      let ti := imgStart s x.block.1 x.top + d
      let bi := imgStart s x.block.2 x.bot + e
      match blockAt bs ti, blockAt bs bi with
      | some k, some k' =>
        if k = k' then
          some (.child ⟨bs.getD k ([], []), ti - blockStart bs k, bi - blockStart bs k,
            some ⟨x.block, k⟩⟩)
        else some (.split k k')
      | _, _ => none
    else none
  | _, _ => none

/-- The digit star of `x`, row-major in `(d, e)`: the digit pairs in range that have an
outcome, each with its outcome (`mem_occStar`).  Empty at a coincidence block and at an
out-of-range position.  At an unbalanced block it may omit digit pairs in range (those with
no outcome); at a balanced noncoincident block with both positions in range it is full, with
`|σ a| · |σ b|` entries (`length_occStar`). -/
def occStar (s : α → List α) (x : Occ α) : List (ℕ × ℕ × Outcome α) :=
  if x.block.1 = x.block.2 then [] else
    match x.block.1[x.top]?, x.block.2[x.bot]? with
    | some a, some b =>
      (List.range (s a).length).flatMap fun d =>
        (List.range (s b).length).filterMap fun e => (occStep s x d e).map fun o => (d, e, o)
    | _, _ => []

/-- The literal child relation: a digit pair keeps both descendants in one block.
Coincidence blocks are terminal, as in `ChildNC`. -/
def occChild (s : α → List α) (x y : Occ α) : Prop :=
  x.block.1 ≠ x.block.2 ∧ ∃ d e, occStep s x d e = some (.child y)

/-- The residual Parikh vector: the prefix defect at the two selected positions. -/
def Occ.residual (x : Occ α) (a : α) : ℤ :=
  ((x.block.1.take x.top).count a : ℤ) - ((x.block.2.take x.bot).count a : ℤ)

/-- The forcing (correction digit) of a digit pair at `x`. -/
def forcing (s : α → List α) (x : Occ α) (d e : ℕ) (a : α) : ℤ :=
  match x.block.1[x.top]?, x.block.2[x.bot]? with
  | some b, some c => (((s b).take d).count a : ℤ) - (((s c).take e).count a : ℤ)
  | _, _ => 0

/-- Both selected occurrences sit at the start of their block. -/
def Occ.AtStart (x : Occ α) : Prop := x.top = 0 ∧ x.bot = 0

/-- Strict interior: at the start of a block that is not the first child of its parent. -/
def Occ.Interior (x : Occ α) : Prop :=
  x.top = 0 ∧ x.bot = 0 ∧ ∃ b, x.birth = some b ∧ 0 < b.ordinal

/-- Outer boundary: at the start of a root block or of the first child of its parent. -/
def Occ.Boundary (x : Occ α) : Prop :=
  x.top = 0 ∧ x.bot = 0 ∧ ∀ b, x.birth = some b → b.ordinal = 0

/-- The block is a coincidence. -/
def Occ.Coincident (x : Occ α) : Prop := x.block.1 = x.block.2

instance (x : Occ α) : Decidable x.AtStart := by unfold Occ.AtStart; infer_instance
instance (x : Occ α) : Decidable x.Coincident := by unfold Occ.Coincident; infer_instance
instance (x : Occ α) : Decidable x.Interior :=
  decidable_of_iff
    (x.top = 0 ∧ x.bot = 0 ∧ (x.birth.any fun b => decide (0 < b.ordinal)) = true)
    (by
      unfold Occ.Interior
      cases h : x.birth <;> simp)
instance (x : Occ α) : Decidable x.Boundary :=
  decidable_of_iff
    (x.top = 0 ∧ x.bot = 0 ∧ (x.birth.all fun b => decide (b.ordinal = 0)) = true)
    (by
      unfold Occ.Boundary
      cases h : x.birth <;> simp)

/-- `x` is a literal occurrence pair of `s`: an irreducible block with two positions, born
(when it is not a root) as the recorded ordinal child of a noncoincident irreducible parent. -/
def Occ.Valid (s : α → List α) (x : Occ α) : Prop :=
  IsBlock x.block ∧ x.top < x.block.1.length ∧ x.bot < x.block.2.length ∧
    match x.birth with
    | none => True
    | some b => IsBlock b.parent ∧ b.parent.1 ≠ b.parent.2 ∧
        (red (subst s b.parent.1) (subst s b.parent.2))[b.ordinal]? = some x.block

instance [Fintype α] (s : α → List α) (x : Occ α) : Decidable (x.Valid s) := by
  unfold Occ.Valid
  cases x.birth <;> infer_instance

/-- Full address of the top selected occurrence in the inflated parent:
`(source_occurrence i, within_image r, global_position, local_position)`; `none` at a root. -/
def Occ.topAddr (s : α → List α) (x : Occ α) : Option (ℕ × ℕ × ℕ × ℕ) :=
  x.birth.map fun b =>
    let g := blockStart (red (subst s b.parent.1) (subst s b.parent.2)) b.ordinal + x.top
    ((cutAddr s b.parent.1 g).1, (cutAddr s b.parent.1 g).2, g, x.top)

/-- Full address of the bottom selected occurrence: `(j, s, global, local)`. -/
def Occ.botAddr (s : α → List α) (x : Occ α) : Option (ℕ × ℕ × ℕ × ℕ) :=
  x.birth.map fun b =>
    let g := blockStart (red (subst s b.parent.1) (subst s b.parent.2)) b.ordinal + x.bot
    ((cutAddr s b.parent.2 g).1, (cutAddr s b.parent.2 g).2, g, x.bot)

/-- Packet success for a target: `none` = any diagonal, `some c` = the diagonal `c/c`. -/
def Occ.SuccessFor (target : Option α) (x : Occ α) : Prop :=
  x.Interior ∧ x.Coincident ∧ (target.all fun c => decide (x.block.1[0]? = some c)) = true

instance (target : Option α) (x : Occ α) : Decidable (x.SuccessFor target) := by
  unfold Occ.SuccessFor; infer_instance

/-- Side swap of an occurrence pair (and of its parent). -/
def Occ.swap (x : Occ α) : Occ α :=
  ⟨x.block.swap, x.bot, x.top, x.birth.map fun b => ⟨b.parent.swap, b.ordinal⟩⟩

/-- Side swap of an outcome: the child is swapped, the two split ordinals exchange. -/
def Outcome.swap : Outcome α → Outcome α
  | .child y => .child y.swap
  | .split k k' => .split k' k

/-- The incidence matrix over `ℤ`. -/
def incZ [Fintype α] (s : α → List α) : Matrix α α ℤ := (inc s).map (↑)

/-! ### Addresses in `σ w` -/

omit [DecidableEq α] in
theorem imgStart_le (s : α → List α) (w : List α) (i : ℕ) :
    imgStart s w i ≤ (subst s w).length := by
  unfold imgStart
  conv_rhs => rw [← List.take_append_drop i w, subst_append, List.length_append]
  exact Nat.le_add_right _ _

omit [DecidableEq α] in
/-- `σ w` split at the image of `w[i]`. -/
theorem subst_split (s : α → List α) (w : List α) {i : ℕ} (hi : i < w.length) :
    subst s w = subst s (w.take i) ++ (s w[i] ++ subst s (w.drop (i + 1))) := by
  conv_lhs => rw [← List.take_append_drop i w, ← List.getElem_cons_drop hi]
  rw [subst_append, Psc.Incidence.subst_cons]

omit [DecidableEq α] in
/-- The prefix of `σ w` ending at digit `d` of the image of `w[i]`: the committed
`take_subst_digit`, with the offset written as `imgStart`. -/
theorem take_subst_add (s : α → List α) (w : List α) {i : ℕ} (hi : i < w.length) {d : ℕ}
    (hd : d ≤ (s w[i]).length) :
    (subst s w).take (imgStart s w i + d) = subst s (w.take i) ++ (s w[i]).take d :=
  take_subst_digit s w i d hi hd

omit [DecidableEq α] in
theorem imgStart_add_lt (s : α → List α) (w : List α) {i : ℕ} (hi : i < w.length) {d : ℕ}
    (hd : d < (s w[i]).length) : imgStart s w i + d < (subst s w).length := by
  rw [subst_split s w hi]
  unfold imgStart
  simp only [List.length_append]
  omega

omit [DecidableEq α] in
/-- The letter at digit `d` of the image of `w[i]`. -/
theorem getElem_subst_add (s : α → List α) (w : List α) {i : ℕ} (hi : i < w.length) {d : ℕ}
    (hd : d < (s w[i]).length) :
    (subst s w)[imgStart s w i + d]? = (s w[i])[d]? := by
  rw [subst_split s w hi]
  unfold imgStart
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hd]

omit [DecidableEq α] in
/-- **The chosen indices.**  Position `imgStart s w i + d` of `σ w` has the address
`(i, d)`: source letter `w[i]`, digit `d` of its image. -/
theorem cutAddr_imgStart_add (s : α → List α) {w : List α} {i d : ℕ} (hi : i < w.length)
    (hd : d < (s w[i]).length) : cutAddr s w (imgStart s w i + d) = (i, d) := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih =>
    cases i with
    | zero =>
      have hd' : d < (s a).length := by simpa using hd
      simp [imgStart, subst, cutAddr, hd']
    | succ i =>
      have hi' : i < w.length := by simpa using hi
      have hd' : d < (s w[i]).length := by simpa using hd
      have e : imgStart s (a :: w) (i + 1) + d = (s a).length + (imgStart s w i + d) := by
        simp only [imgStart, List.take_succ_cons, Psc.Incidence.subst_cons, List.length_append]
        omega
      rw [e]
      simp only [cutAddr]
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ih hi' hd']

/-! ### Blocks of a reduction -/

omit [DecidableEq α] in
theorem blockStart_succ (bs : List (List α × List α)) {k : ℕ} (hk : k < bs.length) :
    blockStart bs (k + 1) = blockStart bs k + bs[k].1.length := by
  unfold blockStart
  rw [← List.take_concat_get' bs k hk, List.map_append, List.sum_append]
  simp

omit [DecidableEq α] in
/-- `blockAt` locates a position in the block list. -/
theorem blockAt_spec : ∀ (bs : List (List α × List α)) (p k : ℕ),
    blockAt bs p = some k ↔
      ∃ hk : k < bs.length, blockStart bs k ≤ p ∧ p < blockStart bs k + bs[k].1.length
  | [], p, k => by simp [blockAt]
  | T :: bs, p, k => by
    unfold blockAt
    by_cases h : p < T.1.length
    · rw [ite_eq_left h]
      constructor
      · intro hk
        obtain rfl : 0 = k := by simpa using hk
        exact ⟨by simp, by simp [blockStart], by simpa [blockStart] using h⟩
      · rintro ⟨hk, h1, h2⟩
        cases k with
        | zero => rfl
        | succ k =>
          exfalso
          simp only [blockStart, List.take_succ_cons, List.map_cons, List.sum_cons] at h1
          omega
    · rw [ite_eq_right h]
      cases k with
      | zero =>
        constructor
        · intro hk
          simp at hk
        · rintro ⟨_, _, h2⟩
          exact absurd (by simpa [blockStart] using h2) h
      | succ k =>
        have ih := blockAt_spec bs (p - T.1.length) k
        constructor
        · intro hk
          obtain ⟨k', hk', hkk⟩ := Option.map_eq_some_iff.1 hk
          obtain rfl : k' = k := by omega
          obtain ⟨hk1, h1, h2⟩ := ih.1 hk'
          refine ⟨by simpa using hk1, ?_, ?_⟩
          · simp only [blockStart, List.take_succ_cons, List.map_cons, List.sum_cons]
            simp only [blockStart] at h1
            omega
          · simp only [blockStart, List.take_succ_cons, List.map_cons, List.sum_cons,
              List.getElem_cons_succ]
            simp only [blockStart] at h2
            omega
        · rintro ⟨hk, h1, h2⟩
          simp only [blockStart, List.take_succ_cons, List.map_cons, List.sum_cons,
            List.getElem_cons_succ] at h1 h2
          have hk1 : k < bs.length := by simpa using hk
          rw [ih.2 ⟨hk1, by simp only [blockStart]; omega, by simp only [blockStart]; omega⟩]
          rfl

/-- Block starts lie inside the word. -/
theorem blockStart_le {u v : List α} (h : u.length = v.length) (k : ℕ) :
    blockStart (red u v) k ≤ u.length := by
  have h1 := congrArg List.length (take_red_top h k)
  rw [List.length_take, List.length_flatten, List.map_map] at h1
  have h2 : (List.map (List.length ∘ Prod.fst) (List.take k (red u v))).sum =
      blockStart (red u v) k := rfl
  rw [h2] at h1
  unfold blockStart at h1 ⊢
  omega

/-- The `k`-th block ends inside the word. -/
theorem blockStart_add_le {u v : List α} (h : u.length = v.length) {k : ℕ}
    (hk : k < (red u v).length) :
    blockStart (red u v) k + (red u v)[k].1.length ≤ u.length := by
  rw [← blockStart_succ _ hk]
  exact blockStart_le h (k + 1)

/-- Block starts are zero returns. -/
theorem equiv1_take_blockStart {u v : List α} (h : Equiv1 u v) (k : ℕ) :
    Equiv1 (u.take (blockStart (red u v) k)) (v.take (blockStart (red u v) k)) := by
  by_cases hk : blockStart (red u v) k ≤ u.length
  · exact (zero_return_iff h hk).2 ⟨k, rfl⟩
  · rw [List.take_of_length_le (by omega), List.take_of_length_le (by rw [← h.length_eq]; omega)]
    exact h

omit [DecidableEq α] in
/-- A prefix that ends inside an aligned factor. -/
theorem take_add_of_factor {w B : List α} {lo : ℕ} (hB : (w.drop lo).take B.length = B)
    (p : ℕ) (hp : p ≤ B.length) : w.take (lo + p) = w.take lo ++ B.take p := by
  rw [List.take_add, ← hB, List.take_take, min_eq_left hp]

/-- A prefix of the top track of the `k`-th block of `red u v` is the factor of `u` read from
the block start (from `getElem_red`). -/
theorem take_getElem_red_fst {u v : List α} (h : Equiv1 u v) {k : ℕ}
    (hk : k < (red u v).length) {p : ℕ} (hp : p ≤ (red u v)[k].1.length) :
    (red u v)[k].1.take p = (u.drop (blockStart (red u v) k)).take p := by
  have hg := congrArg Prod.fst (getElem_red h k hk)
  rw [hg, List.take_take, min_eq_left hp]

/-- The same for the bottom track. -/
theorem take_getElem_red_snd {u v : List α} (h : Equiv1 u v) {k : ℕ}
    (hk : k < (red u v).length) {q : ℕ} (hq : q ≤ (red u v)[k].1.length) :
    (red u v)[k].2.take q = (v.drop (blockStart (red u v) k)).take q := by
  have hg := congrArg Prod.snd (getElem_red h k hk)
  rw [hg, List.take_take, min_eq_left hq]

/-- **Translation by a zero return.**  Inside the `k`-th block of `red u v`, the prefix
defect of `(u, v)` at `(lo + p, lo + q)` is the prefix defect of the block at `(p, q)`. -/
theorem count_take_block {u v : List α} (h : Equiv1 u v) {k : ℕ} (hk : k < (red u v).length)
    {p q : ℕ} (hp : p ≤ (red u v)[k].1.length) (hq : q ≤ (red u v)[k].1.length) (a : α) :
    ((u.take (blockStart (red u v) k + p)).count a : ℤ) -
        ((v.take (blockStart (red u v) k + q)).count a : ℤ) =
      (((red u v)[k].1.take p).count a : ℤ) - (((red u v)[k].2.take q).count a : ℤ) := by
  have hg := getElem_red h k hk
  have h1 : ((u.drop (blockStart (red u v) k)).take (red u v)[k].1.length) = (red u v)[k].1 :=
    (congrArg Prod.fst hg).symm
  have h2 : ((v.drop (blockStart (red u v) k)).take (red u v)[k].1.length) = (red u v)[k].2 :=
    (congrArg Prod.snd hg).symm
  have hl : (red u v)[k].2.length = (red u v)[k].1.length :=
    ((red_isBlock h _ (List.getElem_mem hk)).2.1.length_eq).symm
  rw [take_add_of_factor h1 p hp, take_add_of_factor (hl ▸ h2) q (hl ▸ hq),
    List.count_append, List.count_append, equiv1_take_blockStart h k a]
  push_cast
  ring

/-! ### The step -/

/-- A step that has an outcome reads two letters in range and two digits in range. -/
theorem occStep_some {s : α → List α} {x : Occ α} {d e : ℕ} {o : Outcome α}
    (h : occStep s x d e = some o) :
    ∃ (hP : x.top < x.block.1.length) (hQ : x.bot < x.block.2.length),
      d < (s x.block.1[x.top]).length ∧ e < (s x.block.2[x.bot]).length := by
  unfold occStep at h
  split at h
  · rename_i a b ha hb
    obtain ⟨hP, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hQ, rfl⟩ := List.getElem?_eq_some_iff.1 hb
    split_ifs at h with hde
    exact ⟨hP, hQ, hde⟩
  · exact absurd h (by simp)

/-- The digit pair `(d, e)` at `x` leads into block `k` at local positions `(p, q)`. -/
theorem occStep_child_iff {s : α → List α} {x y : Occ α} {d e : ℕ} :
    occStep s x d e = some (.child y) ↔
      ∃ (hP : x.top < x.block.1.length) (hQ : x.bot < x.block.2.length) (k : ℕ)
        (hk : k < (red (subst s x.block.1) (subst s x.block.2)).length),
        d < (s x.block.1[x.top]).length ∧ e < (s x.block.2[x.bot]).length ∧
        blockStart (red (subst s x.block.1) (subst s x.block.2)) k ≤
          imgStart s x.block.1 x.top + d ∧
        imgStart s x.block.1 x.top + d <
          blockStart (red (subst s x.block.1) (subst s x.block.2)) k +
            (red (subst s x.block.1) (subst s x.block.2))[k].1.length ∧
        blockStart (red (subst s x.block.1) (subst s x.block.2)) k ≤
          imgStart s x.block.2 x.bot + e ∧
        imgStart s x.block.2 x.bot + e <
          blockStart (red (subst s x.block.1) (subst s x.block.2)) k +
            (red (subst s x.block.1) (subst s x.block.2))[k].1.length ∧
        y = ⟨(red (subst s x.block.1) (subst s x.block.2))[k],
          imgStart s x.block.1 x.top + d -
            blockStart (red (subst s x.block.1) (subst s x.block.2)) k,
          imgStart s x.block.2 x.bot + e -
            blockStart (red (subst s x.block.1) (subst s x.block.2)) k,
          some ⟨x.block, k⟩⟩ := by
  unfold occStep
  constructor
  · intro h
    split at h
    · rename_i a b ha hb
      obtain ⟨hP, rfl⟩ := List.getElem?_eq_some_iff.1 ha
      obtain ⟨hQ, rfl⟩ := List.getElem?_eq_some_iff.1 hb
      split_ifs at h with hde
      simp only at h
      split at h
      · rename_i k k' hk hk'
        split_ifs at h with hkk
        · subst hkk
          obtain ⟨hk1, h1, h2⟩ := (blockAt_spec _ _ _).1 hk
          obtain ⟨_, h3, h4⟩ := (blockAt_spec _ _ _).1 hk'
          refine ⟨hP, hQ, k, hk1, hde.1, hde.2, h1, h2, h3, h4, ?_⟩
          have := Option.some.inj h
          rw [Outcome.child.injEq] at this
          rw [← this, List.getD_eq_getElem _ _ hk1]
        · exact absurd (Option.some.inj h) (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rintro ⟨hP, hQ, k, hk, hd, he, h1, h2, h3, h4, rfl⟩
    rw [List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
    simp only [hd, he, and_self, ite_true]
    rw [(blockAt_spec _ _ k).2 ⟨hk, h1, h2⟩, (blockAt_spec _ _ k).2 ⟨hk, h3, h4⟩]
    simp only [ite_true, List.getD_eq_getElem _ _ hk]

/-- The digit pair `(d, e)` at `x` splits: both inflated positions are located, in blocks
with different ordinals. -/
theorem occStep_split_iff {s : α → List α} {x : Occ α} {d e k k' : ℕ} :
    occStep s x d e = some (.split k k') ↔
      ∃ (hP : x.top < x.block.1.length) (hQ : x.bot < x.block.2.length),
        d < (s x.block.1[x.top]).length ∧ e < (s x.block.2[x.bot]).length ∧
        blockAt (red (subst s x.block.1) (subst s x.block.2)) (imgStart s x.block.1 x.top + d) =
          some k ∧
        blockAt (red (subst s x.block.1) (subst s x.block.2)) (imgStart s x.block.2 x.bot + e) =
          some k' ∧
        k ≠ k' := by
  unfold occStep
  constructor
  · intro h
    split at h
    · rename_i a b ha hb
      obtain ⟨hP, rfl⟩ := List.getElem?_eq_some_iff.1 ha
      obtain ⟨hQ, rfl⟩ := List.getElem?_eq_some_iff.1 hb
      split_ifs at h with hde
      simp only at h
      split at h
      · rename_i k1 k2 hk hk'
        split_ifs at h with hkk
        · exact absurd (Option.some.inj h) (by simp)
        · simp only [Option.some.injEq, Outcome.split.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hP, hQ, hde.1, hde.2, hk, hk', hkk⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rintro ⟨hP, hQ, hd, he, hk, hk', hkk⟩
    rw [List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
    simp only [hd, he, and_self, ite_true]
    rw [hk, hk']
    simp only [hkk, ite_false]

/-- A split separates two different blocks. -/
theorem occStep_split_ne {s : α → List α} {x : Occ α} {d e k k' : ℕ}
    (h : occStep s x d e = some (.split k k')) : k ≠ k' := by
  obtain ⟨-, -, -, -, -, -, hkk⟩ := occStep_split_iff.1 h
  exact hkk

omit [DecidableEq α] in
/-- Every position below the total length lies in some block. -/
theorem blockAt_isSome : ∀ (bs : List (List α × List α)) (p : ℕ),
    p < (bs.map fun T => T.1.length).sum → (blockAt bs p).isSome
  | [], p, h => by simp at h
  | T :: bs, p, h => by
    unfold blockAt
    by_cases hp : p < T.1.length
    · rw [ite_eq_left hp]
      rfl
    · rw [ite_eq_right hp]
      simp only [List.map_cons, List.sum_cons] at h
      have := blockAt_isSome bs (p - T.1.length) (by omega)
      simpa using this

/-- **No digit pair in range is lost**: at a balanced block, every digit pair in range has an
outcome (a child or a split). -/
theorem occStep_isSome {s : α → List α} {x : Occ α} (hx : Equiv1 x.block.1 x.block.2)
    {d e : ℕ} (hP : x.top < x.block.1.length) (hQ : x.bot < x.block.2.length)
    (hd : d < (s x.block.1[x.top]).length) (he : e < (s x.block.2[x.bot]).length) :
    (occStep s x d e).isSome := by
  have hE : Equiv1 (subst s x.block.1) (subst s x.block.2) := equiv1_subst s hx
  have hsum : ((red (subst s x.block.1) (subst s x.block.2)).map fun T => T.1.length).sum =
      (subst s x.block.1).length := by
    have := congrArg List.length (red_top hE.length_eq)
    rw [List.length_flatten, List.map_map] at this
    exact this
  have ht := blockAt_isSome _ _
    (hsum ▸ imgStart_add_lt s x.block.1 hP hd :
      imgStart s x.block.1 x.top + d <
        ((red (subst s x.block.1) (subst s x.block.2)).map fun T => T.1.length).sum)
  have hb := blockAt_isSome _ _
    ((hsum.trans hE.length_eq) ▸ imgStart_add_lt s x.block.2 hQ he :
      imgStart s x.block.2 x.bot + e <
        ((red (subst s x.block.1) (subst s x.block.2)).map fun T => T.1.length).sum)
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 ht
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 hb
  unfold occStep
  rw [List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
  simp only [hd, he, and_self, ite_true]
  rw [hk, hk']
  by_cases hkk : k = k' <;> simp [hkk]

/-- **Completeness of the block projection**: an occurrence edge lies over a child edge of
the balanced-pair automaton. -/
theorem occChild.childNC {s : α → List α} {x y : Occ α} (h : occChild s x y) :
    ChildNC s x.block y.block := by
  obtain ⟨hne, d, e, hstep⟩ := h
  obtain ⟨-, -, k, hk, -, -, -, -, -, -, rfl⟩ := occStep_child_iff.1 hstep
  exact ⟨hne, List.getElem_mem hk⟩

/-- Literal occurrence pairs are closed under literal children: the child is an irreducible
block with both positions inside it, born as the recorded ordinal child of `x.block`. -/
theorem occChild.valid {s : α → List α} {x y : Occ α} (hx : x.Valid s) (h : occChild s x y) :
    y.Valid s := by
  obtain ⟨hne, d, e, hstep⟩ := h
  obtain ⟨-, -, k, hk, -, -, h1, h2, h3, h4, rfl⟩ := occStep_child_iff.1 hstep
  have hE : Equiv1 (subst s x.block.1) (subst s x.block.2) := equiv1_subst s hx.1.2.1
  have hB : IsBlock (red (subst s x.block.1) (subst s x.block.2))[k] :=
    red_isBlock hE _ (List.getElem_mem hk)
  have hl := hB.2.1.length_eq
  refine ⟨hB, ?_, ?_, hx.1, hne, List.getElem?_eq_getElem hk⟩
  · dsimp only
    omega
  · dsimp only
    rw [← hl]
    omega

/-- **No parallel edges**: the digit pair of a literal edge is determined by its two ends. -/
theorem occStep_digits_unique {s : α → List α} {x y : Occ α} {d e d' e' : ℕ}
    (h : occStep s x d e = some (.child y)) (h' : occStep s x d' e' = some (.child y)) :
    d = d' ∧ e = e' := by
  obtain ⟨-, -, k, hk, -, -, h1, -, h3, -, rfl⟩ := occStep_child_iff.1 h
  obtain ⟨-, -, k', hk', -, -, h1', -, h3', -, heq⟩ := occStep_child_iff.1 h'
  have hkk : k = k' := by
    have := congrArg Occ.birth heq
    simpa using this
  subst hkk
  have ht := congrArg Occ.top heq
  have hb := congrArg Occ.bot heq
  simp only at ht hb
  unfold imgStart at *
  omega

/-- **The star lists exactly the digit pairs that have an outcome, each with its outcome**
(and nothing at a coincidence block).  A digit pair with an outcome is in range
(`occStep_some`); at an unbalanced block a digit pair in range may have none. -/
theorem mem_occStar {s : α → List α} {x : Occ α} {d e : ℕ} {o : Outcome α} :
    (d, e, o) ∈ occStar s x ↔ x.block.1 ≠ x.block.2 ∧ occStep s x d e = some o := by
  unfold occStar
  by_cases hc : x.block.1 = x.block.2
  · simp [hc]
  · rw [ite_eq_right hc]
    constructor
    · intro hm
      refine ⟨hc, ?_⟩
      split at hm
      · simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap,
          Option.map_eq_some_iff] at hm
        obtain ⟨d', -, e', -, o', ho', heq⟩ := hm
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact ho'
      · simp at hm
    · rintro ⟨-, h⟩
      obtain ⟨hP, hQ, hd, he⟩ := occStep_some h
      rw [List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
      simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.map_eq_some_iff]
      exact ⟨d, hd, e, he, o, h, rfl⟩

/-- **The star is full**: at a balanced noncoincident block with both positions in range,
the star has one entry for each of the `|σ a| · |σ b|` digit pairs, children and splits
together. -/
theorem length_occStar {s : α → List α} {x : Occ α} (hx : Equiv1 x.block.1 x.block.2)
    (hne : x.block.1 ≠ x.block.2) (hP : x.top < x.block.1.length)
    (hQ : x.bot < x.block.2.length) :
    (occStar s x).length = (s x.block.1[x.top]).length * (s x.block.2[x.bot]).length := by
  unfold occStar
  rw [ite_eq_right hne]
  simp only [List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
  rw [List.length_flatMap]
  have hrow : ∀ d ∈ List.range (s x.block.1[x.top]).length,
      ((List.range (s x.block.2[x.bot]).length).filterMap
        fun e => (occStep s x d e).map fun o => (d, e, o)).length =
        (s x.block.2[x.bot]).length := by
    intro d hd
    rw [(List.filterMap_length_eq_length).2, List.length_range]
    intro e he
    rw [Option.isSome_map]
    exact occStep_isSome hx hP hQ (List.mem_range.1 hd) (List.mem_range.1 he)
  rw [List.map_congr_left hrow, List.map_const', List.sum_replicate_nat, List.length_range]

/-- The literal children of `x`, read off its star. -/
def occChildren (s : α → List α) (x : Occ α) : List (Occ α) :=
  (occStar s x).filterMap fun t =>
    match t.2.2 with
    | .child y => some y
    | .split _ _ => none

theorem mem_occChildren {s : α → List α} {x y : Occ α} :
    y ∈ occChildren s x ↔ occChild s x y := by
  unfold occChildren
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨⟨d, e, o⟩, hm, ho⟩
    obtain ⟨hc, hs⟩ := mem_occStar.1 hm
    cases o with
    | child y' =>
      simp only [Option.some.injEq] at ho
      subst ho
      exact ⟨hc, d, e, hs⟩
    | split _ _ => simp at ho
  · rintro ⟨hc, d, e, hs⟩
    exact ⟨(d, e, .child y), mem_occStar.2 ⟨hc, hs⟩, rfl⟩

/-- **Finite branching**: the literal children of `x` are the child entries of its star. -/
theorem occChild_finite (s : α → List α) (x : Occ α) : {y | occChild s x y}.Finite := by
  have : {y | occChild s x y} = {y | y ∈ occChildren s x} := by
    ext y
    exact mem_occChildren.symm
  rw [this]
  exact (occChildren s x).finite_toSet

/-! ### Both source occurrence addresses -/

/-- **Every literal edge carries both source occurrences and both chosen digits**: the top
selected occurrence of the child is digit `d` of the image of the letter at `x.top`, at
global position `imgStart s x.block.1 x.top + d` of the inflated parent; likewise at the
bottom with `x.bot` and `e`. -/
theorem occStep_addr {s : α → List α} {x y : Occ α} {d e : ℕ}
    (h : occStep s x d e = some (.child y)) :
    y.topAddr s = some (x.top, d, imgStart s x.block.1 x.top + d, y.top) ∧
      y.botAddr s = some (x.bot, e, imgStart s x.block.2 x.bot + e, y.bot) := by
  obtain ⟨hP, hQ, k, hk, hd, he, h1, -, h3, -, rfl⟩ := occStep_child_iff.1 h
  simp only [Occ.topAddr, Occ.botAddr, Option.map_some]
  rw [Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h3, cutAddr_imgStart_add s hP hd,
    cutAddr_imgStart_add s hQ he]
  exact ⟨rfl, rfl⟩

/-! ### Orientation -/

omit [DecidableEq α] in
theorem Occ.swap_swap (x : Occ α) : x.swap.swap = x := by
  rcases x with ⟨⟨u, v⟩, P, Q, _ | ⟨⟨p, q⟩, k⟩⟩ <;> rfl

omit [DecidableEq α] in
theorem Outcome.swap_swap (o : Outcome α) : o.swap.swap = o := by
  cases o <;> simp [Outcome.swap, Occ.swap_swap]

/-- Swapping the sides negates the residual. -/
theorem Occ.residual_swap (x : Occ α) : x.swap.residual = -x.residual := by
  funext a
  simp [Occ.residual, Occ.swap]

omit [DecidableEq α] in
theorem blockAt_map_swap : ∀ (bs : List (List α × List α)),
    (∀ T ∈ bs, T.2.length = T.1.length) → ∀ p, blockAt (bs.map Prod.swap) p = blockAt bs p
  | [], _, _ => rfl
  | T :: bs, h, p => by
    simp only [List.map_cons, blockAt, Prod.fst_swap]
    rw [h T List.mem_cons_self,
      blockAt_map_swap bs (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))]

omit [DecidableEq α] in
theorem blockStart_map_swap (bs : List (List α × List α))
    (h : ∀ T ∈ bs, T.2.length = T.1.length) (k : ℕ) :
    blockStart (bs.map Prod.swap) k = blockStart bs k := by
  unfold blockStart
  rw [← List.map_take, List.map_map]
  congr 1
  apply List.map_congr_left
  intro T hT
  exact h T (List.mem_of_mem_take hT)

omit [DecidableEq α] in
theorem getD_map_swap (bs : List (List α × List α)) (k : ℕ) :
    (bs.map Prod.swap).getD k ([], []) = (bs.getD k ([], [])).swap :=
  List.getD_map bs ([], []) Prod.swap

/-- **Orientation equivariance** (from `red_swap`): swapping the sides swaps the digits and
the outcome; no orientation is hidden in a normalisation. -/
theorem occStep_swap {s : α → List α} {x : Occ α} (hx : Equiv1 x.block.1 x.block.2)
    (d e : ℕ) :
    occStep s x.swap e d = (occStep s x d e).map Outcome.swap := by
  rcases x with ⟨⟨u, v⟩, P, Q, birth⟩
  have hE : Equiv1 (subst s u) (subst s v) := equiv1_subst s hx
  have hl : ∀ T ∈ red (subst s u) (subst s v), T.2.length = T.1.length :=
    fun T hT => ((red_isBlock hE T hT).2.1.length_eq).symm
  simp only [occStep, Occ.swap, Prod.fst_swap, Prod.snd_swap]
  rw [red_swap (subst s u) (subst s v), blockAt_map_swap _ hl, blockAt_map_swap _ hl]
  cases hu : u[P]? with
  | none => simp
  | some a =>
    cases hv : v[Q]? with
    | none => simp
    | some b =>
      simp only
      by_cases hde : d < (s a).length ∧ e < (s b).length
      · rw [ite_eq_left ⟨hde.2, hde.1⟩, ite_eq_left hde]
        cases hk : blockAt (red (subst s u) (subst s v)) (imgStart s u P + d) with
        | none =>
          cases blockAt (red (subst s u) (subst s v)) (imgStart s v Q + e) <;> simp
        | some k =>
          cases hk' : blockAt (red (subst s u) (subst s v)) (imgStart s v Q + e) with
          | none => simp
          | some k' =>
            simp only
            by_cases hkk : k = k'
            · subst hkk
              simp only [ite_true, Option.map_some, Outcome.swap, Occ.swap, Option.map_some,
                getD_map_swap, blockStart_map_swap _ hl]
            · rw [ite_eq_right (Ne.symm hkk), ite_eq_right hkk]
              simp [Outcome.swap]
      · rw [ite_eq_right (fun h => hde ⟨h.2, h.1⟩), ite_eq_right hde]
        simp

/-- A literal edge, swapped, is a literal edge. -/
theorem occChild.swap {s : α → List α} {x y : Occ α} (hx : Equiv1 x.block.1 x.block.2)
    (h : occChild s x y) : occChild s x.swap y.swap := by
  obtain ⟨hne, d, e, hs⟩ := h
  refine ⟨fun h' => hne h'.symm, e, d, ?_⟩
  rw [occStep_swap hx, hs]
  rfl

theorem occChild_swap_iff {s : α → List α} {x y : Occ α} (hx : Equiv1 x.block.1 x.block.2) :
    occChild s x.swap y.swap ↔ occChild s x y := by
  refine ⟨fun h => ?_, occChild.swap hx⟩
  have h' := occChild.swap (x := x.swap) (y := y.swap) (fun c => (hx c).symm) h
  rwa [Occ.swap_swap, Occ.swap_swap] at h'

/-- Literal occurrence pairs are closed under the side swap. -/
theorem Occ.Valid.swap {s : α → List α} {x : Occ α} (hx : x.Valid s) : x.swap.Valid s := by
  rcases x with ⟨blk, P, Q, _ | ⟨par, k⟩⟩
  · obtain ⟨hB, hP, hQ, -⟩ := hx
    exact ⟨Psc.StrictSystem.isBlock_swap hB, hQ, hP, trivial⟩
  · obtain ⟨hB, hP, hQ, hpB, hpne, hk⟩ := hx
    refine ⟨Psc.StrictSystem.isBlock_swap hB, hQ, hP, Psc.StrictSystem.isBlock_swap hpB,
      fun h => hpne h.symm, ?_⟩
    show (red (subst s par.2) (subst s par.1))[k]? = some blk.swap
    rw [red_swap, List.getElem?_map, hk]
    rfl

omit [DecidableEq α] in
theorem Occ.interior_swap (x : Occ α) : x.swap.Interior ↔ x.Interior := by
  rcases x with ⟨blk, P, Q, _ | ⟨par, k⟩⟩
  · simp [Occ.swap, Occ.Interior]
  · simp only [Occ.swap, Occ.Interior, Option.map_some, Option.some.injEq, exists_eq_left']
    tauto

omit [DecidableEq α] in
theorem Occ.boundary_swap (x : Occ α) : x.swap.Boundary ↔ x.Boundary := by
  rcases x with ⟨blk, P, Q, _ | ⟨par, k⟩⟩
  · simp only [Occ.swap, Occ.Boundary, Option.map_none]
    tauto
  · simp only [Occ.swap, Occ.Boundary, Option.map_some, Option.some.injEq, forall_eq']
    tauto

omit [DecidableEq α] in
theorem Occ.coincident_swap (x : Occ α) : x.swap.Coincident ↔ x.Coincident := by
  simp [Occ.swap, Occ.Coincident, eq_comm]

/-! ### The residual transport law along literal edges -/

section Transport

variable [Fintype α]

/-- **The residual transport law**, as a theorem about literal data:
`r' = M r + λ` along every literal occurrence edge.  Derived from the committed
`residual_transport` with the balanced cut `lo` at the start of the child block
(`equiv1_take_blockStart`); `getElem_red` turns "measured from `lo`" into the child's own
words.  Hypotheses: the parent block is balanced and the step is a literal child; no
primitivity, irreducibility or Pisot hypothesis. -/
theorem residual_step {s : α → List α} {x y : Occ α} {d e : ℕ}
    (hx : Equiv1 x.block.1 x.block.2) (h : occStep s x d e = some (.child y)) (a : α) :
    y.residual a = (∑ c, (inc s a c : ℤ) * x.residual c) + forcing s x d e a := by
  obtain ⟨hP, hQ, k, hk, hd, he, h1, h2, h3, h4, rfl⟩ := occStep_child_iff.1 h
  have hE : Equiv1 (subst s x.block.1) (subst s x.block.2) := equiv1_subst s hx
  have hT := residual_transport s x.block.1 x.block.2 x.top x.bot d e
    (blockStart (red (subst s x.block.1) (subst s x.block.2)) k) hP hQ hd.le he.le h1 h3
    (equiv1_take_blockStart hE k) a
  unfold Occ.residual forcing
  simp only [List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
  rw [take_getElem_red_fst hE hk (by omega), take_getElem_red_snd hE hk (by omega)]
  exact hT

/-- Vector form of `residual_step`. -/
theorem residual_step_vec {s : α → List α} {x y : Occ α} {d e : ℕ}
    (hx : Equiv1 x.block.1 x.block.2) (h : occStep s x d e = some (.child y)) :
    y.residual = (incZ s).mulVec x.residual + forcing s x d e := by
  funext a
  rw [residual_step hx h a]
  simp [incZ, Matrix.mulVec, dotProduct]

/-- At a child start the residual vanishes, so `M r + λ = 0` (`cor:one-step`,
`M E + c = 0`). -/
theorem residual_atStart {s : α → List α} {x y : Occ α} {d e : ℕ}
    (hx : Equiv1 x.block.1 x.block.2) (h : occStep s x d e = some (.child y)) (hy : y.AtStart) :
    (incZ s).mulVec x.residual + forcing s x d e = 0 := by
  rw [← residual_step_vec hx h]
  funext a
  simp [Occ.residual, hy.1, hy.2]

/-- The iterated law (the level-scaled address certificate) along the first `n` steps of a
literal path: `r_n = Mⁿ r₀ + ∑_{t<n} M^{n-1-t} λ_t`.  Only the steps `t < n` are assumed
(balanced source, literal child), so the path may end at `p n`, for instance at a dead end or
at a coincidence block, where no further step exists. -/
theorem residual_iterate_lt {s : α → List α} (p : ℕ → Occ α) (ds : ℕ → ℕ × ℕ) (n : ℕ)
    (hbal : ∀ t < n, Equiv1 (p t).block.1 (p t).block.2)
    (hp : ∀ t < n, occStep s (p t) (ds t).1 (ds t).2 = some (.child (p (t + 1)))) :
    (p n).residual = (incZ s ^ n).mulVec (p 0).residual +
      ∑ t ∈ Finset.range n,
        (incZ s ^ (n - 1 - t)).mulVec (forcing s (p t) (ds t).1 (ds t).2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [residual_step_vec (hbal n (by omega)) (hp n (by omega)),
      ih (fun t ht => hbal t (by omega)) (fun t ht => hp t (by omega)), Finset.sum_range_succ,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ', Matrix.mulVec_sum, add_assoc]
    congr 2
    · refine Finset.sum_congr rfl fun t ht => ?_
      rw [Matrix.mulVec_mulVec, ← pow_succ']
      congr 2
      have := Finset.mem_range.1 ht
      omega
    · simp

/-- The iterated law along an infinite literal lineage (every step balanced and literal);
the corollary of `residual_iterate_lt` in the form of the design brief. -/
theorem residual_iterate {s : α → List α} (p : ℕ → Occ α) (ds : ℕ → ℕ × ℕ)
    (hbal : ∀ n, Equiv1 (p n).block.1 (p n).block.2)
    (hp : ∀ n, occStep s (p n) (ds n).1 (ds n).2 = some (.child (p (n + 1)))) (n : ℕ) :
    (p n).residual = (incZ s ^ n).mulVec (p 0).residual +
      ∑ t ∈ Finset.range n,
        (incZ s ^ (n - 1 - t)).mulVec (forcing s (p t) (ds t).1 (ds t).2) :=
  residual_iterate_lt p ds n (fun t _ => hbal t) (fun t _ => hp t)

end Transport

/-! ### Start classification -/

omit [DecidableEq α] in
/-- At a start, an occurrence pair is strictly interior or on the outer boundary. -/
theorem Occ.atStart_iff (x : Occ α) : x.AtStart ↔ x.Interior ∨ x.Boundary := by
  unfold Occ.AtStart Occ.Interior Occ.Boundary
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : ∃ b, x.birth = some b ∧ 0 < b.ordinal
    · exact Or.inl ⟨h1, h2, h⟩
    · refine Or.inr ⟨h1, h2, fun b hb => ?_⟩
      by_contra hne
      exact h ⟨b, hb, Nat.pos_of_ne_zero hne⟩
  · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩

omit [DecidableEq α] in
/-- Strict interior and outer boundary exclude each other. -/
theorem Occ.not_interior_and_boundary (x : Occ α) : ¬ (x.Interior ∧ x.Boundary) := by
  rintro ⟨⟨-, -, b, hb, hpos⟩, -, -, hB⟩
  exact absurd (hB b hb) (Nat.pos_iff_ne_zero.1 hpos)

/-- The literal occurrence graph; targets are the occurrence pairs in a coincidence block
(the target of `bpaGraph`). -/
def occGraph (s : α → List α) : ChildGraph (Occ α) where
  child := occChild s
  target := Occ.Coincident

/-- The packet-target occurrence graph for a target letter: same child relation, targets the
packet successes `Occ.SuccessFor target`. -/
def occGraphFor (s : α → List α) (target : Option α) : ChildGraph (Occ α) where
  child := occChild s
  target x := x.SuccessFor target

theorem occGraph_child (s : α → List α) : (occGraph s).child = occChild s := rfl

theorem occGraphFor_child (s : α → List α) (target : Option α) :
    (occGraphFor s target).child = occChild s := rfl

/-- The default packet target `none` is "any interior coincidence". -/
theorem occGraphFor_none_target (s : α → List α) (x : Occ α) :
    (occGraphFor s none).target x ↔ x.Interior ∧ x.Coincident := by
  simp [occGraphFor, Occ.SuccessFor]

/-- Every packet success is a target of `occGraph`.  The converse is not stated: by
definition a coincidence that is not strictly interior (or, for `some c`, not on the
diagonal `c/c`) is not a packet success. -/
theorem occGraphFor_target_le (s : α → List α) (target : Option α) (x : Occ α)
    (h : (occGraphFor s target).target x) : (occGraph s).target x :=
  h.2.1

/-! ### Controls -/

/-- Fibonacci `0 ↦ 01, 1 ↦ 0` (`Psc.Descendants.fibSubst`): the occurrence pair at positions
`(1, 0)` of the root `(01, 10)` (`Psc.Binomial.tmPair`).  Fibonacci satisfies the standing
primitive, irreducible, Pisot hypotheses (as recorded in `Psc.QuantifierBinding`, whose
`fib_lasso` is the balanced-pair control on the same root; this module proves no spectral
fact about it); it is binary, hence outside the three-letter census corpus. -/
def fibDead : Occ (Fin 2) := ⟨tmPair, 1, 0, none⟩

/-- `fibDead` is a literal occurrence pair (a root reading of an irreducible block). -/
theorem fibDead_valid : fibDead.Valid fibSubst := by decide

/-- **A literal dead end.**  The letters at positions `(1, 0)` of `(01, 10)` are `1` and `1`,
each with a one-letter image, so there is a single digit pair, and it splits: the two
inflated positions `2` and `0` of `σ(01, 10) = (010, 001)` lie in the blocks
`1 = (10, 01)` and `0 = (0, 0)` of its reduction. -/
theorem fibDead_star : occStar fibSubst fibDead = [(0, 0, .split 1 0)] := by decide

/-- Hence `fibDead` has no literal child (`mem_occChildren`). -/
theorem fibDead_children : occChildren fibSubst fibDead = [] := by decide

/-- Its block `(01, 10)` has the balanced-pair child `(0, 0)`: a literal dead end over a
state with a child.  That the block projection is therefore not sound from every source is
a statement about `Psc.GraphRefinement.SoundEvery` and is not made in this module. -/
theorem fibDead_block_child : (bpaGraph fibSubst).child fibDead.block ([0], [0]) :=
  ⟨by decide, show _ ∈ _ by decide⟩

/-! #### Calibration on two archived rows of `1/02/202`

The rows are those of `evidence/target-aware-bpa-2026-10-02/real-secondary.jsonl`: packets
209 (line 248) and 429 (line 468), factors 16 and 19 (lines 29, 32), states 7 and 8
(lines 10, 11), edges 396, 397 and 818-823 (lines 942, 943, 1364-1369).  The decoding into
`Occ` was done by hand: packet 209 is state 8 in orientation `-1` at positions `(4, 4)`,
born through factor 16 (parent 7, ordinal 0, factor orientation `-1`, so the parent is read
in orientation `+1`); packet 429 is state 7 in orientation `+1` at positions `(2, 1)`, born
through factor 19 (parent 8, ordinal 2, factor orientation `-1`, so the parent is read in
orientation `-1`).  The statements below derive the archived fields from the definitions of
this module by `decide`; they are a calibration of the definitions on two rows, not a check
of the archive. -/

/-- The real-secondary specimen `1/02/202`: `0 ↦ 1, 1 ↦ 02, 2 ↦ 202`. -/
def rsSubst : Fin 3 → List (Fin 3) := ![[1], [0, 2], [2, 0, 2]]

/-- Archived state 7, `(021, 120)`. -/
def rsState7 : List (Fin 3) × List (Fin 3) := ([0, 2, 1], [1, 2, 0])

/-- Archived state 8, `(022021, 120202)`. -/
def rsState8 : List (Fin 3) × List (Fin 3) := ([0, 2, 2, 0, 2, 1], [1, 2, 0, 2, 0, 2])

/-- Packet 209 as a literal occurrence pair. -/
def x209 : Occ (Fin 3) := ⟨rsState8.swap, 4, 4, some ⟨rsState7, 0⟩⟩

/-- Packet 429 as a literal occurrence pair. -/
def x429 : Occ (Fin 3) := ⟨rsState7, 2, 1, some ⟨rsState8.swap, 2⟩⟩

theorem rs_rows_valid : x209.Valid rsSubst ∧ x429.Valid rsSubst := by decide

/-- Both literal steps of the archived cycle `209 -(0,0)-> 429 -(0,2)-> 209` (edges 396 and
820), birth records included.  That they are edges of `occGraph` (their source blocks are
noncoincident) is `rs_rows_occGraph`. -/
theorem rs_rows_edges :
    occStep rsSubst x209 0 0 = some (.child x429) ∧
      occStep rsSubst x429 0 2 = some (.child x209) := by
  decide

/-- The archived rows 209 and 429 form a 2-cycle of the literal occurrence graph: both steps
of `rs_rows_edges` leave noncoincident blocks, so both are `occChild` edges. -/
theorem rs_rows_occGraph :
    (occGraph rsSubst).child x209 x429 ∧ (occGraph rsSubst).child x429 x209 :=
  ⟨⟨by decide, 0, 0, rs_rows_edges.1⟩, ⟨by decide, 0, 2, rs_rows_edges.2⟩⟩

/-- The full digit stars of both rows.  Packet 209 has the archived edges `(0,0) -> 429`,
`(0,1) -> 430` and one split; packet 429 has the six archived edges `-> 207 … 212`
(edges 818-823) and no split. -/
theorem rs_rows_stars :
    occStar rsSubst x209 =
        [(0, 0, .child x429), (0, 1, .child ⟨rsState7, 2, 2, some ⟨rsState8.swap, 2⟩⟩),
          (0, 2, .split 2 3)] ∧
      occStar rsSubst x429 =
        [(0, 0, .child ⟨rsState8.swap, 4, 2, some ⟨rsState7, 0⟩⟩),
          (0, 1, .child ⟨rsState8.swap, 4, 3, some ⟨rsState7, 0⟩⟩),
          (0, 2, .child x209),
          (1, 0, .child ⟨rsState8.swap, 5, 2, some ⟨rsState7, 0⟩⟩),
          (1, 1, .child ⟨rsState8.swap, 5, 3, some ⟨rsState7, 0⟩⟩),
          (1, 2, .child ⟨rsState8.swap, 5, 4, some ⟨rsState7, 0⟩⟩)] := by
  decide

/-- The carried fields of the two archived rows, re-derived from the definitions: both
addresses, both letters, the residuals `(-1,1,0)` and `(1,-1,1)`, the forcings of the two
cycle edges (the archived `lambda` of edges 396 and 820) and the interior bits. -/
theorem rs_rows_fields :
    x209.topAddr rsSubst = some (2, 0, 4, 4) ∧ x209.botAddr rsSubst = some (1, 2, 4, 4) ∧
      x429.topAddr rsSubst = some (4, 0, 9, 2) ∧ x429.botAddr rsSubst = some (4, 0, 8, 1) ∧
      x209.block.1[x209.top]? = some 0 ∧ x209.block.2[x209.bot]? = some 2 ∧
      x429.block.1[x429.top]? = some 1 ∧ x429.block.2[x429.bot]? = some 2 ∧
      x209.residual = ![-1, 1, 0] ∧ x429.residual = ![1, -1, 1] ∧
      forcing rsSubst x209 0 0 = ![0, 0, 0] ∧ forcing rsSubst x429 0 2 = ![-1, 0, -1] ∧
      ¬ x209.Interior ∧ ¬ x429.Interior := by
  decide

/-- The transport law on both edges, as instances of the proved `residual_step`. -/
theorem rs_rows_transport (a : Fin 3) :
    x429.residual a =
        (∑ c, (inc rsSubst a c : ℤ) * x209.residual c) + forcing rsSubst x209 0 0 a ∧
      x209.residual a =
        (∑ c, (inc rsSubst a c : ℤ) * x429.residual c) + forcing rsSubst x429 0 2 a :=
  ⟨residual_step (by decide) rs_rows_edges.1 a, residual_step (by decide) rs_rows_edges.2 a⟩

/-- Its value: `M = inc rsSubst = [[0,1,1],[1,0,0],[0,1,2]]`, `M(-1,1,0) = (1,-1,1)` and
`M(1,-1,1) + (-1,0,-1) = (-1,1,0)`. -/
theorem rs_rows_transport_values :
    (fun a => ∑ c, (inc rsSubst a c : ℤ) * ![-1, 1, 0] c) = ![1, -1, 1] ∧
      (fun a => (∑ c, (inc rsSubst a c : ℤ) * ![1, -1, 1] c) + ![-1, 0, -1] a) =
        ![-1, 1, 0] := by
  decide

/-- **The balance hypothesis of `occStep_isSome` is needed.**  At the unbalanced block
`(0, 1)` of `1/02/202`, both positions and the digit pair `(0, 1)` are in range, yet the step
has no outcome: `red (σ 0) (σ 1) = red [1] [0, 2] = [([1], [0])]` covers only position `0`
of `σ 1 = 02`, and the inflated bottom position is `1`.  The block is not balanced, so this
is not a valid occurrence pair; a valid one has a balanced block, where `occStep_isSome`
applies. -/
theorem rs_unbalanced_step_none :
    ¬ Equiv1 ([0] : List (Fin 3)) [1] ∧
      ¬ (⟨([0], [1]), 0, 0, none⟩ : Occ (Fin 3)).Valid rsSubst ∧
      0 < (rsSubst 0).length ∧ 1 < (rsSubst 1).length ∧
      red (subst rsSubst [0]) (subst rsSubst [1]) = [([1], [0])] ∧
      occStep rsSubst ⟨([0], [1]), 0, 0, none⟩ 0 1 = none := by
  decide

end Psc.OccurrenceGraph
