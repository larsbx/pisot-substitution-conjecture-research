/-
# The absolute occurrence layer and its reading

The top layer of the packet square (roadmap immediate-sequence item 2;
`docs/packet-square-stop-go-2026-11-10.md`; `README.llm.txt`, 2026-11-09 addendum "P0
OCCURRENCE REFINEMENT").  The middle layer, the literal occurrence graph `occGraph s` on
`Occ`, is `Psc.OccurrenceGraph`; this module puts under it the *actual substitution-child
occurrence edges* of the iterates of a root pair, and over it the block projection onto the
balanced-pair automaton.

## The absolute layer `A(σ, T₀)`

* `AbsOcc`: a pair of absolute positions `(level, top, bot)` in `σⁿ(T₀.1)`, `σⁿ(T₀.2)`;
  `absStep s T₀ x d e`: its literal child along the digit pair `(d, e)`, pure position
  arithmetic (`imgStart`), no reduction formed; `absStep_inj`: the source and the digits are the
  `cutAddr` addresses of the target; `exists_absStep_parent`: every absolute pair of positive
  level whose positions lie inside the iterates has an absolute parent.
* `Anchor s T₀ x y off`: the block-local datum `y : Occ α` reads the absolute pair `x`: `y.block`
  is the aligned factor of the iterates at the zero return `off` and the positions are
  `off + y.top`, `off + y.bot`.  `Anchor` asks for neither irreducibility, nor positions inside
  the block, nor a birth record, so `Anchored s T₀` (absolute pair together with a reading) is
  a *pair type*, not the declared universe.
* `anchoredGraph s T₀`: the **retained** edges, an absolute edge `absStep` whose readings are
  joined by a literal occurrence edge with the same digits, out of a noncoincident block;
  targets: a coincidence block.

## The top square ρ = `reading`

In the vocabulary of `docs/packet-square-stop-go-2026-11-10.md` (§1: `Complete`, `SoundSome`,
`SoundEvery`, `TargetDown`, `TargetUp`), "soundness" of this arrow is `SoundEvery` with the
anchored pairs as the actual side and `occGraph s` as the quotient.

* `reading_complete` (definitional), `reading_soundEvery` (from `anchor_step`: every literal
  edge out of the reading of *any* anchored pair, at any level and offset, is the reading of an
  absolute edge out of it), `reading_targetDown`, `reading_targetUp`, hence `reading_refines`;
  no hypothesis on `s` or `T₀`.  `reading_readings`: (E), (AE), (A), (A⁺) agree between an
  anchored pair and its reading, and (AE°) pulls back.  These are stated on the pair type
  `Anchored s T₀`, which also holds junk readings (for instance an empty block at a zero
  return); the same square on the declared universe is `universe_refines` below.
* The success target: `anchoredGraphFor s T₀ target` (the retained edges, targets the packet
  successes `Occ.SuccessFor target`) and `reading_refines_for` onto `occGraphFor s target`.
* Infinite-path lifting: `reading_liftsPaths` (dependent choice, from `SoundEvery`) and the
  choice-free `absLineage_anchor` (the lift of a digit-labelled path is the recursion
  `absLineage` on `absStep`).  It is not cycle realisation: levels increase
  (`anchored_no_cycle`), so (AE°) holds at every anchored pair vacuously
  (`anchored_cyclicProductive`).
* `Anchor.letters`, `Anchor.residual`: the letters and the absolute prefix defect at an anchored
  pair are those of its reading.

## Splits are final; irreducible readings

* `Separated`: a zero return of the iterates lies between the two positions.  It is inherited by
  every absolute child (`Separated.step`, from `lem:inherited`) and excludes every irreducible
  reading containing both positions (`Separated.not_anchor`).  A split of the reading separates
  the absolute child (`Anchor.split_separated`), hence `anchor_split` and
  `split_never_rejoins`: no absolute descendant of a split child, along any digits at any
  depth, has an irreducible reading.  This is a Lean counterpart, for the absolute pairs of this
  module, of the prose justification "their disjoint balanced spans remain disjoint on
  inflation" in the module docstring of `kernel/psc/target_packets.mojo`; it reads no Mojo code
  and says nothing about the Mojo split counter.
* `anchor_unique`: two irreducible readings of one absolute pair containing its top position
  have the same offset, block and positions.  `Anchor.mem_red`: for a balanced root, an
  irreducible reading is a block of `red (σⁿ T₀.1) (σⁿ T₀.2)`; `anchor_of_red`: conversely,
  each block of that reduction reads the absolute pairs inside it.
* `anchor_parent_inside` / `anchor_parent` (parent closure): if the absolute child of `x` has an
  irreducible reading containing both positions, so does `x`, and the child's reading is the
  literal child of `x`'s reading along the same digits, with the birth record of that block.

## The declared occurrence universe

* `Universe s T₀`: the anchored pairs reached by retained edges from a root reading
  `⟨T₀, P, Q, none⟩` at level `0`; `universe_closed`, `rootAnchored_mem`.
* `universe_reading_unique`: on the universe the reading, birth record included, is a function
  of the absolute pair (no hypothesis on `s` or `T₀`).  `universe_birth`: above level `0` the
  birth record of an element of the universe is the block of the reading of an element of the
  universe over its absolute parent (that parent is unique, `absStep_inj`, and so is the
  element over it, `universe_reading_unique`).
* ρ on the universe: `universeGraph s T₀`, the actual graph induced on `Universe s T₀`, and
  `universe_refines`: the reading is a refinement of it onto `occGraph s`, and the absolute
  pair is injective on the universe; `universe_readings` (the transfers);
  `universeGraphFor`, `universe_refines_for` (the success target).
* For an irreducible root: `universe_valid` (every reading is `Occ.Valid`),
  `universe_block_mem_red` (its block is a block of the reduction of the iterates), and
  **completeness relative to the declared universe at the absolute level**:
  `anchored_cover_universe`, `anchored_cover` (the weaker reachability form) and
  `anchored_cover_red`: every absolute pair whose two positions lie in one **noncoincident**
  block of `red (σⁿ T₀.1) (σⁿ T₀.2)` is the absolute pair of an element of the universe read at
  that block (its birth record is then fixed, by `universe_reading_unique`).  At a coincidence
  block the universe holds only the retained children of noncoincident pairs, not every
  absolute pair of the block, and the noncoincidence hypothesis cannot be dropped:
  `anchored_cover_needs_hnc` (Fibonacci, root `(01, 10)`: the pair `(2, 0, 0)` lies in the
  irreducible coincidence block `(0, 0)` of `red (01001) (01010)`, and no element of the
  universe lies over it, `fib_lvl2_not_universe`).  `universe_absStep`: an absolute edge out of
  an element of the universe with a noncoincident block is a retained edge into the universe,
  or a split, after which no descendant has an irreducible reading; out of a coincidence block
  no edge is retained.
* `reading_image_universe` (balanced root): the readings of the universe are exactly the
  literal occurrence pairs reachable in `occGraph s` from the root pairs of `T₀`;
  `universe_reading_mem_of_closed`: the universe is read inside every child-closed set of
  literal occurrence pairs holding those root pairs (the generic step of `universe_covered`).
* Frame change: `AbsOcc.swap`, `Anchor.swap`, `absStep_swap`, `Anchored.swap`,
  `anchoredGraph_child_swap`, `universe_swap` (the universe of `T₀.swap` contains the swap of
  the universe of `T₀`) and its converse `universe_swap_iff`.

## The block projection β = `Occ.block` onto `bpaGraph s`

`block_complete`, `block_targets`, `block_productive` ((E) projects), `block_inevitable`
((A) pulls back), `block_soundSome_at` (soundness from some source, **from irreducible sources
only**: the root occurrence pair at the `cutAddr` addresses of the child's start).  The literal
control `fib_block_readings` (Fibonacci `0 ↦ 01, 1 ↦ 0`, which the repository records inside the
standing primitive, irreducible, Pisot class, `Psc.QuantifierBinding.fib_lasso`; binary, hence
outside the three-letter census corpus): `fibDead` is valid, (AE) holds at its block while (E)
fails at it, (A) holds at it (vacuously; `fibDead_no_child`) while (A) fails at its block, and
β is not sound from every source.

## Calibration

The archived 2-cycle `209 -(0,0)-> 429 -(0,2)-> 209` of the real-secondary specimen `1/02/202`
(rows `x209`, `x429` of `Psc.OccurrenceGraph`) is read off the retained absolute lineage
`(3,4,4) → (4,9,8) → (5,20,20)` of the seed `(01, 10)`, which lies in the universe (reached from
the root reading at `(1, 0)`): `rs_cycle_lineage` (every universe element over `(3,4,4)` reads
as 209, over `(4,9,8)` as 429; the two readings of 209 are at levels 3 and 5) and
`rs_infinite_lineage` (the choice-free infinite lift along the cycle digits).  Derived by
`decide` from the definitions; a calibration on one lineage whose edge `(3,4,4) → (4,9,8)` was
located by hand, not a check of the archive.  No Tribonacci control for ρ is given here (a
`decide` replay of one Tribonacci absolute lineage from the seed `(01, 10)` matched to a packet
path): it needs packet data, which this module does not read.

Hypotheses are stated per theorem; none of this module assumes primitivity, irreducibility of
the incidence matrix, the Pisot property, or that `s` is nonerasing.

Not proved here: that any packet table or Mojo packet graph is sound or complete with respect
to these graphs (no packet row is read; `universe_covered`, `packet_square` and the composite
statements belong to the packet-square module); that the universe of any root is finite, or that
any reading is productive, hereditarily productive or inevitable; that a root pair is legal, or
that an absolute lineage yields a legal context, a point of the hull `X_σ`, or one infinite
desubstitution history (backward compactness); `SoundSome` of the block projection from
reducible or unbalanced sources, or any statement for a root that is not balanced beyond the
theorems that take no root hypothesis; which seeds a given occurrence pair is read in; that the
universe holds every absolute pair of a coincidence block of the reduction of the iterates (it
does not, `anchored_cover_needs_hnc`); a Tribonacci positive control for ρ.  Nothing here
advances, proves or closes C4, G1, #84, #138, #139 or the Pisot substitution conjecture.
-/
import PscVerif.OccurrenceGraph
import PscVerif.GraphEmbedding

namespace Psc.OccurrenceRealisation

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.Incidence
open Psc.QuantifierInterface Psc.QuantifierBinding
open Psc.OccurrenceAddress Psc.OccurrenceGraph Psc.GraphRefinement

variable {α : Type*} [DecidableEq α]

/-! ### Absolute occurrence pairs and the literal substitution-child edge -/

/-- A pair of letter occurrences in the `level`-th iterates of a root pair: absolute
positions, no blocks. -/
structure AbsOcc where
  level : ℕ
  top : ℕ
  bot : ℕ
  deriving DecidableEq

/-- The literal substitution-child occurrence edge with digits `(d, e)`: position
arithmetic in the iterates of `T₀`; no reduction is formed. -/
def absStep (s : α → List α) (T₀ : List α × List α) (x : AbsOcc) (d e : ℕ) : Option AbsOcc :=
  match ((subst s)^[x.level] T₀.1)[x.top]?, ((subst s)^[x.level] T₀.2)[x.bot]? with
  | some a, some b =>
    if d < (s a).length ∧ e < (s b).length then
      some ⟨x.level + 1, imgStart s ((subst s)^[x.level] T₀.1) x.top + d,
        imgStart s ((subst s)^[x.level] T₀.2) x.bot + e⟩
    else none
  | _, _ => none

/-- `y` is the block-local reading of the absolute pair `x`: `y.block` is the aligned factor
of the `x.level`-th iterates of `T₀` at the zero return `off`, and the selected positions
are `off + y.top`, `off + y.bot`.  No irreducibility, no bound on the positions and no birth
record is asked for. -/
structure Anchor (s : α → List α) (T₀ : List α × List α) (x : AbsOcc) (y : Occ α) (off : ℕ) :
    Prop where
  balanced : Equiv1 y.block.1 y.block.2
  zero : Equiv1 (((subst s)^[x.level] T₀.1).take off) (((subst s)^[x.level] T₀.2).take off)
  top_factor : (((subst s)^[x.level] T₀.1).drop off).take y.block.1.length = y.block.1
  bot_factor : (((subst s)^[x.level] T₀.2).drop off).take y.block.2.length = y.block.2
  top_pos : x.top = off + y.top
  bot_pos : x.bot = off + y.bot

omit [DecidableEq α] in
/-- A word around an aligned factor `B` at offset `off`. -/
theorem factor_eq {w B : List α} {off : ℕ} (hB : (w.drop off).take B.length = B) :
    w = w.take off ++ (B ++ w.drop (off + B.length)) := by
  conv_lhs =>
    rw [← List.take_append_drop off w, ← List.take_append_drop B.length (w.drop off), hB,
      List.drop_drop]

omit [DecidableEq α] in
/-- The letters of an aligned factor. -/
theorem getElem?_of_factor {w B : List α} {off : ℕ} (hB : (w.drop off).take B.length = B)
    {p : ℕ} (hp : p < B.length) : w[off + p]? = B[p]? := by
  conv_lhs => rw [factor_eq hB]
  have hoff : (w.take off).length = off := by
    rw [List.length_take]
    have : B.length ≤ (w.drop off).length := by
      have := congrArg List.length hB
      rw [List.length_take] at this
      omega
    rw [List.length_drop] at this
    omega
  rw [List.getElem?_append_right (by omega), hoff, Nat.add_sub_cancel_left,
    List.getElem?_append_left hp]

omit [DecidableEq α] in
/-- Image offsets inside an aligned factor. -/
theorem imgStart_add_of_factor (s : α → List α) {w B : List α} {off : ℕ}
    (hB : (w.drop off).take B.length = B) {p : ℕ} (hp : p ≤ B.length) :
    imgStart s w (off + p) = imgStart s w off + imgStart s B p := by
  unfold imgStart
  rw [take_add_of_factor hB p hp, subst_append, List.length_append]

/-- The root: every position pair of `T₀` is anchored at offset `0`, level `0`. -/
theorem anchor_root (s : α → List α) {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2) (P Q : ℕ) :
    Anchor s T₀ ⟨0, P, Q⟩ ⟨T₀, P, Q, none⟩ 0 where
  balanced := hT
  zero := by simp [Equiv1]
  top_factor := by simp
  bot_factor := by simp
  top_pos := by simp
  bot_pos := by simp

/-- **The square, child case.**  If `y` is the block-local reading of `x` and the digit
pair `(d, e)` keeps both descendants of `y` in one block, then the absolute child of `x`
with the same digits exists and `y'` is its block-local reading. -/
theorem anchor_step {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y y' : Occ α}
    {off d e : ℕ} (ha : Anchor s T₀ x y off) (h : occStep s y d e = some (.child y')) :
    ∃ x' off', absStep s T₀ x d e = some x' ∧ Anchor s T₀ x' y' off' := by
  obtain ⟨hP, hQ, k, hk, hd, he, h1, h2, h3, h4, rfl⟩ := occStep_child_iff.1 h
  obtain ⟨hbal, hzero, htop, hbot, hxt, hxb⟩ := ha
  have hE : Equiv1 (subst s y.block.1) (subst s y.block.2) := equiv1_subst s hbal
  have hlen : imgStart s ((subst s)^[x.level] T₀.2) off =
      imgStart s ((subst s)^[x.level] T₀.1) off := ((equiv1_subst s hzero).length_eq).symm
  have hblk := red_isBlock hE _ (List.getElem_mem hk)
  have hg := getElem_red hE k hk
  have hl2 : (red (subst s y.block.1) (subst s y.block.2))[k].2.length =
      (red (subst s y.block.1) (subst s y.block.2))[k].1.length := (hblk.2.1.length_eq).symm
  refine ⟨⟨x.level + 1, imgStart s ((subst s)^[x.level] T₀.1) x.top + d,
      imgStart s ((subst s)^[x.level] T₀.2) x.bot + e⟩,
    imgStart s ((subst s)^[x.level] T₀.1) off +
      blockStart (red (subst s y.block.1) (subst s y.block.2)) k, ?_, ?_⟩
  · unfold absStep
    rw [hxt, hxb, getElem?_of_factor htop hP, getElem?_of_factor hbot hQ,
      List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
    simp [hd, he]
  · have hu : (subst s)^[x.level + 1] T₀.1 = subst s ((subst s)^[x.level] T₀.1) :=
      Function.iterate_succ_apply' _ _ _
    have hv : (subst s)^[x.level + 1] T₀.2 = subst s ((subst s)^[x.level] T₀.2) :=
      Function.iterate_succ_apply' _ _ _
    -- the inflated words, split at the inflated block
    have hsu : subst s ((subst s)^[x.level] T₀.1) =
        subst s (((subst s)^[x.level] T₀.1).take off) ++ (subst s y.block.1 ++
          subst s (((subst s)^[x.level] T₀.1).drop (off + y.block.1.length))) := by
      conv_lhs => rw [factor_eq htop]
      rw [subst_append, subst_append]
    have hsv : subst s ((subst s)^[x.level] T₀.2) =
        subst s (((subst s)^[x.level] T₀.2).take off) ++ (subst s y.block.2 ++
          subst s (((subst s)^[x.level] T₀.2).drop (off + y.block.2.length))) := by
      conv_lhs => rw [factor_eq hbot]
      rw [subst_append, subst_append]
    have hlo1 : blockStart (red (subst s y.block.1) (subst s y.block.2)) k +
        (red (subst s y.block.1) (subst s y.block.2))[k].1.length ≤ (subst s y.block.1).length :=
      blockStart_add_le hE.length_eq hk
    have hlo2 : blockStart (red (subst s y.block.1) (subst s y.block.2)) k +
        (red (subst s y.block.1) (subst s y.block.2))[k].1.length ≤ (subst s y.block.2).length :=
      hE.length_eq ▸ hlo1
    refine ⟨hblk.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · -- the new offset is a zero return
      show Equiv1 (((subst s)^[x.level + 1] T₀.1).take _) (((subst s)^[x.level + 1] T₀.2).take _)
      rw [hu, hv]
      have e1 : (subst s ((subst s)^[x.level] T₀.1)).take
          (imgStart s ((subst s)^[x.level] T₀.1) off +
            blockStart (red (subst s y.block.1) (subst s y.block.2)) k) =
          subst s (((subst s)^[x.level] T₀.1).take off) ++
            (subst s y.block.1).take
              (blockStart (red (subst s y.block.1) (subst s y.block.2)) k) := by
        rw [hsu]
        unfold imgStart
        rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left, List.take_append_of_le_length (by omega)]
      have e2 : (subst s ((subst s)^[x.level] T₀.2)).take
          (imgStart s ((subst s)^[x.level] T₀.1) off +
            blockStart (red (subst s y.block.1) (subst s y.block.2)) k) =
          subst s (((subst s)^[x.level] T₀.2).take off) ++
            (subst s y.block.2).take
              (blockStart (red (subst s y.block.1) (subst s y.block.2)) k) := by
        rw [hsv, ← hlen]
        unfold imgStart
        rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left, List.take_append_of_le_length (by omega)]
      rw [e1, e2]
      exact (equiv1_subst s hzero).append (equiv1_take_blockStart hE k)
    · -- the child block is the aligned factor on top
      show (((subst s)^[x.level + 1] T₀.1).drop _).take
        (red (subst s y.block.1) (subst s y.block.2))[k].1.length = _
      rw [hu, hsu]
      have e0 : (subst s (((subst s)^[x.level] T₀.1).take off)).length =
          imgStart s ((subst s)^[x.level] T₀.1) off := rfl
      rw [List.drop_append, List.drop_of_length_le (by rw [e0]; exact Nat.le_add_right _ _),
        e0, Nat.add_sub_cancel_left, List.nil_append, List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
      exact (congrArg Prod.fst hg).symm
    · show (((subst s)^[x.level + 1] T₀.2).drop _).take
        (red (subst s y.block.1) (subst s y.block.2))[k].2.length = _
      rw [hv, hsv, ← hlen]
      have e0 : (subst s (((subst s)^[x.level] T₀.2).take off)).length =
          imgStart s ((subst s)^[x.level] T₀.2) off := rfl
      rw [List.drop_append, List.drop_of_length_le (by rw [e0]; exact Nat.le_add_right _ _),
        e0, Nat.add_sub_cancel_left, List.nil_append, List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega), hl2]
      exact (congrArg Prod.snd hg).symm
    · show imgStart s ((subst s)^[x.level] T₀.1) x.top + d =
        imgStart s ((subst s)^[x.level] T₀.1) off +
            blockStart (red (subst s y.block.1) (subst s y.block.2)) k +
          (imgStart s y.block.1 y.top + d -
            blockStart (red (subst s y.block.1) (subst s y.block.2)) k)
      rw [hxt, imgStart_add_of_factor s htop hP.le]
      omega
    · show imgStart s ((subst s)^[x.level] T₀.2) x.bot + e =
        imgStart s ((subst s)^[x.level] T₀.1) off +
            blockStart (red (subst s y.block.1) (subst s y.block.2)) k +
          (imgStart s y.block.2 y.bot + e -
            blockStart (red (subst s y.block.1) (subst s y.block.2)) k)
      rw [hxb, imgStart_add_of_factor s hbot hQ.le, hlen]
      omega

/-- The letters at an anchored pair are the letters of the block. -/
theorem Anchor.letters {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y : Occ α}
    {off : ℕ} (ha : Anchor s T₀ x y off) (hP : y.top < y.block.1.length)
    (hQ : y.bot < y.block.2.length) :
    ((subst s)^[x.level] T₀.1)[x.top]? = y.block.1[y.top]? ∧
      ((subst s)^[x.level] T₀.2)[x.bot]? = y.block.2[y.bot]? :=
  ⟨by rw [ha.top_pos]; exact getElem?_of_factor ha.top_factor hP,
    by rw [ha.bot_pos]; exact getElem?_of_factor ha.bot_factor hQ⟩

/-- The absolute prefix defect at an anchored pair is the residual of the block-local
reading. -/
theorem Anchor.residual {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y : Occ α}
    {off : ℕ} (ha : Anchor s T₀ x y off) (hP : y.top ≤ y.block.1.length)
    (hQ : y.bot ≤ y.block.2.length) (a : α) :
    ((((subst s)^[x.level] T₀.1).take x.top).count a : ℤ) -
        ((((subst s)^[x.level] T₀.2).take x.bot).count a : ℤ) = y.residual a := by
  rw [ha.top_pos, ha.bot_pos, take_add_of_factor ha.top_factor _ hP,
    take_add_of_factor ha.bot_factor _ hQ, List.count_append, List.count_append, ha.zero a]
  unfold Occ.residual
  push_cast
  ring

/-! ### Elementary facts about `absStep`, `imgStart` and `blockStart` -/

omit [DecidableEq α] in
/-- A step that has an outcome reads two letters in range and two digits in range, and its
outcome is the position arithmetic of `absStep`. -/
theorem absStep_some {s : α → List α} {T₀ : List α × List α} {x x' : AbsOcc} {d e : ℕ}
    (h : absStep s T₀ x d e = some x') :
    ∃ (hP : x.top < ((subst s)^[x.level] T₀.1).length)
      (hQ : x.bot < ((subst s)^[x.level] T₀.2).length),
      d < (s ((subst s)^[x.level] T₀.1)[x.top]).length ∧
      e < (s ((subst s)^[x.level] T₀.2)[x.bot]).length ∧
      x' = ⟨x.level + 1, imgStart s ((subst s)^[x.level] T₀.1) x.top + d,
        imgStart s ((subst s)^[x.level] T₀.2) x.bot + e⟩ := by
  unfold absStep at h
  split at h
  · rename_i a b ha hb
    obtain ⟨hP, rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hQ, rfl⟩ := List.getElem?_eq_some_iff.1 hb
    split_ifs at h with hde
    exact ⟨hP, hQ, hde.1, hde.2, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

omit [DecidableEq α] in
/-- The converse of `absStep_some`. -/
theorem absStep_of {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {d e : ℕ}
    (hP : x.top < ((subst s)^[x.level] T₀.1).length)
    (hQ : x.bot < ((subst s)^[x.level] T₀.2).length)
    (hd : d < (s ((subst s)^[x.level] T₀.1)[x.top]).length)
    (he : e < (s ((subst s)^[x.level] T₀.2)[x.bot]).length) :
    absStep s T₀ x d e = some ⟨x.level + 1, imgStart s ((subst s)^[x.level] T₀.1) x.top + d,
        imgStart s ((subst s)^[x.level] T₀.2) x.bot + e⟩ := by
  unfold absStep
  rw [List.getElem?_eq_getElem hP, List.getElem?_eq_getElem hQ]
  simp [hd, he]

omit [DecidableEq α] in
/-- `absStep` raises the level by one. -/
theorem absStep_level {s : α → List α} {T₀ : List α × List α} {x x' : AbsOcc} {d e : ℕ}
    (h : absStep s T₀ x d e = some x') : x'.level = x.level + 1 := by
  obtain ⟨-, -, -, -, rfl⟩ := absStep_some h
  rfl

omit [DecidableEq α] in
/-- **`absStep` is injective in (source, digits)**: the source positions and the digits of an
absolute step are the `cutAddr` addresses of its target positions. -/
theorem absStep_inj {s : α → List α} {T₀ : List α × List α} {x₁ x₂ x' : AbsOcc}
    {d₁ e₁ d₂ e₂ : ℕ} (h₁ : absStep s T₀ x₁ d₁ e₁ = some x')
    (h₂ : absStep s T₀ x₂ d₂ e₂ = some x') : x₁ = x₂ ∧ d₁ = d₂ ∧ e₁ = e₂ := by
  obtain ⟨hP₁, hQ₁, hd₁, he₁, rfl⟩ := absStep_some h₁
  obtain ⟨hP₂, hQ₂, hd₂, he₂, heq⟩ := absStep_some h₂
  have hl : x₂.level = x₁.level := by
    have := congrArg AbsOcc.level heq
    simp only at this
    omega
  rcases x₁ with ⟨n, P₁, Q₁⟩
  rcases x₂ with ⟨n₂, P₂, Q₂⟩
  simp only at hl
  subst hl
  simp only [AbsOcc.mk.injEq, true_and] at heq
  have ht := cutAddr_imgStart_add s hP₁ hd₁
  have ht' := cutAddr_imgStart_add s hP₂ hd₂
  have hb := cutAddr_imgStart_add s hQ₁ he₁
  have hb' := cutAddr_imgStart_add s hQ₂ he₂
  simp only at ht ht' hb hb'
  rw [heq.1] at ht
  rw [heq.2] at hb
  rw [ht] at ht'
  rw [hb] at hb'
  simp only [Prod.mk.injEq] at ht' hb'
  exact ⟨by rw [ht'.1, hb'.1], ht'.2, hb'.2⟩

omit [DecidableEq α] in
/-- The image offset of the next letter. -/
theorem imgStart_succ (s : α → List α) (w : List α) {i : ℕ} (hi : i < w.length) :
    imgStart s w (i + 1) = imgStart s w i + (s w[i]).length := by
  unfold imgStart
  rw [List.take_add_one, List.getElem?_eq_getElem hi, subst_append, List.length_append]
  simp [subst]

omit [DecidableEq α] in
/-- Image offsets are monotone. -/
theorem imgStart_mono (s : α → List α) (w : List α) {i j : ℕ} (h : i ≤ j) :
    imgStart s w i ≤ imgStart s w j := by
  unfold imgStart
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, subst_append, List.length_append]
  omega

/-- At a zero return the two image offsets agree. -/
theorem imgStart_eq_of_equiv1 (s : α → List α) {u v : List α} {Z : ℕ}
    (h : Equiv1 (u.take Z) (v.take Z)) : imgStart s u Z = imgStart s v Z :=
  (equiv1_subst s h).length_eq

omit [DecidableEq α] in
/-- Block starts are monotone. -/
theorem blockStart_mono (bs : List (List α × List α)) {i j : ℕ} (h : i ≤ j) :
    blockStart bs i ≤ blockStart bs j := by
  unfold blockStart
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  omega

/-- A digit pair with a child outcome out of a balanced block leads to an irreducible block
with both positions inside it. -/
theorem occStep_child_isBlock {s : α → List α} {y y' : Occ α} {d e : ℕ}
    (hy : Equiv1 y.block.1 y.block.2) (h : occStep s y d e = some (.child y')) :
    IsBlock y'.block ∧ y'.top < y'.block.1.length ∧ y'.bot < y'.block.2.length := by
  obtain ⟨-, -, k, hk, -, -, h1, h2, h3, h4, rfl⟩ := occStep_child_iff.1 h
  have hE : Equiv1 (subst s y.block.1) (subst s y.block.2) := equiv1_subst s hy
  have hB : IsBlock (red (subst s y.block.1) (subst s y.block.2))[k] :=
    red_isBlock hE _ (List.getElem_mem hk)
  have hl := hB.2.1.length_eq
  refine ⟨hB, ?_, ?_⟩
  · dsimp only
    omega
  · dsimp only
    rw [← hl]
    omega

/-- `occStep` does not read the birth record. -/
theorem occStep_congr {s : α → List α} {y y' : Occ α}
    (hb : y.block = y'.block) (ht : y.top = y'.top) (hq : y.bot = y'.bot) (d e : ℕ) :
    occStep s y d e = occStep s y' d e := by
  unfold occStep
  rw [hb, ht, hq]

/-- `Anchor` does not read the birth record. -/
theorem Anchor.congr {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y y' : Occ α}
    {off : ℕ} (ha : Anchor s T₀ x y off) (hb : y.block = y'.block) (ht : y.top = y'.top)
    (hq : y.bot = y'.bot) : Anchor s T₀ x y' off where
  balanced := hb ▸ ha.balanced
  zero := ha.zero
  top_factor := hb ▸ ha.top_factor
  bot_factor := hb ▸ ha.bot_factor
  top_pos := ht ▸ ha.top_pos
  bot_pos := hq ▸ ha.bot_pos

/-! ### The actual graph and its reading (the top square) -/

/-- An absolute occurrence pair of the iterates of `T₀` with a block-local reading.  This is a
*pair type*: an element is an absolute pair together with one reading of it.  The declared
occurrence universe is the subset `Universe s T₀` below. -/
def Anchored (s : α → List α) (T₀ : List α × List α) : Type _ :=
  {a : AbsOcc × Occ α // ∃ off, Anchor s T₀ a.1 a.2 off}

/-- The actual graph: literal position edges between anchored pairs whose block-local readings
are joined by a literal occurrence edge with the same digits (the **retained** edges).  Targets:
a coincidence block. -/
def anchoredGraph (s : α → List α) (T₀ : List α × List α) : ChildGraph (Anchored s T₀) where
  child a b := a.1.2.block.1 ≠ a.1.2.block.2 ∧
    ∃ d e, absStep s T₀ a.1.1 d e = some b.1.1 ∧ occStep s a.1.2 d e = some (.child b.1.2)
  target a := a.1.2.Coincident

/-- The block-local reading. -/
def reading (s : α → List α) (T₀ : List α × List α) (a : Anchored s T₀) : Occ α := a.1.2

/-- **Completeness** of the reading (definitional). -/
theorem reading_complete (s : α → List α) (T₀ : List α × List α) :
    Complete (anchoredGraph s T₀) (occGraph s) (reading s T₀) :=
  fun _ _ h => ⟨h.1, let ⟨d, e, _, h2⟩ := h.2; ⟨d, e, h2⟩⟩

/-- **Soundness from every source** (the top square): every literal occurrence edge out of
the reading of an anchored pair is the reading of an absolute edge out of that pair. -/
theorem reading_soundEvery (s : α → List α) (T₀ : List α × List α) :
    SoundEvery (anchoredGraph s T₀) (occGraph s) (reading s T₀) := by
  rintro ⟨⟨x, y⟩, off, ha⟩ y' ⟨hne, d, e, hstep⟩
  obtain ⟨x', off', hx', ha'⟩ := anchor_step ha hstep
  exact ⟨⟨(x', y'), off', ha'⟩, ⟨hne, d, e, hx', hstep⟩, rfl⟩

/-- The reading preserves targets: an anchored pair with a coincidence block reads as a
coincidence block (definitional). -/
theorem reading_targetDown (s : α → List α) (T₀ : List α × List α) :
    TargetDown (anchoredGraph s T₀) (occGraph s) (reading s T₀) :=
  fun _ h => h

/-- The reading reflects targets (definitional). -/
theorem reading_targetUp (s : α → List α) (T₀ : List α × List α) :
    TargetUp (anchoredGraph s T₀) (occGraph s) (reading s T₀) :=
  fun _ h => h

/-- The reading is a refinement of the actual graph onto the literal occurrence graph.  No
hypothesis on `s` or `T₀`. -/
theorem reading_refines (s : α → List α) (T₀ : List α × List α) :
    Refines (anchoredGraph s T₀) (occGraph s) (reading s T₀) :=
  ⟨reading_complete s T₀, reading_soundEvery s T₀, reading_targetDown s T₀,
    reading_targetUp s T₀⟩

/-- The actual graph for a packet target letter: the retained edges of `anchoredGraph s T₀`,
targets the anchored pairs whose reading is a packet success `Occ.SuccessFor target`. -/
def anchoredGraphFor (s : α → List α) (T₀ : List α × List α) (target : Option α) :
    ChildGraph (Anchored s T₀) where
  child := (anchoredGraph s T₀).child
  target a := a.1.2.SuccessFor target

/-- **The top square for the success target**: the reading is a refinement of
`anchoredGraphFor s T₀ target` onto `occGraphFor s target` (same child relations as
`reading_refines`, `occGraphFor_child`; the targets are read off the reading).  No hypothesis
on `s`, `T₀` or `target`. -/
theorem reading_refines_for (s : α → List α) (T₀ : List α × List α) (target : Option α) :
    Refines (anchoredGraphFor s T₀ target) (occGraphFor s target) (reading s T₀) :=
  ⟨reading_complete s T₀, reading_soundEvery s T₀, fun _ h => h, fun _ h => h⟩

/-- **Infinite-path lifting**: every infinite path of the literal occurrence graph from the
reading of an anchored pair is the reading of an infinite path of the actual graph (built by
dependent choice from `reading_soundEvery`; `absLineage_anchor` is the choice-free form). -/
theorem reading_liftsPaths (s : α → List α) (T₀ : List α × List α) (a : Anchored s T₀) :
    LiftsPaths (anchoredGraph s T₀) (occGraph s) (reading s T₀) a :=
  (reading_soundEvery s T₀).liftsPaths a

/-- The readings (E), (AE), (A), (A⁺) agree between an anchored pair and its reading, and
(AE°) pulls back from the reading (`Refines.cyclicProductive_of_quotient`; the actual side is
acyclic, `anchored_no_cycle`, so (AE°) holds there vacuously). -/
theorem reading_readings (s : α → List α) (T₀ : List α × List α) (a : Anchored s T₀) :
    ((anchoredGraph s T₀).Productive a ↔ (occGraph s).Productive (reading s T₀ a)) ∧
      ((anchoredGraph s T₀).HereditarilyProductive a ↔
        (occGraph s).HereditarilyProductive (reading s T₀ a)) ∧
      ((anchoredGraph s T₀).Inevitable a ↔ (occGraph s).Inevitable (reading s T₀ a)) ∧
      ((anchoredGraph s T₀).InevMax a ↔ (occGraph s).InevMax (reading s T₀ a)) ∧
      ((occGraph s).CyclicProductive (reading s T₀ a) →
        (anchoredGraph s T₀).CyclicProductive a) :=
  let h := reading_refines s T₀
  ⟨h.productive_iff, h.hereditarilyProductive_iff, h.inevitable_iff, h.inevMax_iff,
    h.cyclicProductive_of_quotient⟩

/-- An actual edge raises the level by one. -/
theorem anchoredGraph_level {s : α → List α} {T₀ : List α × List α} {a b : Anchored s T₀}
    (h : (anchoredGraph s T₀).child a b) : b.1.1.level = a.1.1.level + 1 := by
  obtain ⟨-, d, e, hx, -⟩ := h
  exact absStep_level hx

/-- Levels increase strictly along nonempty actual paths. -/
theorem anchoredGraph_transGen_level {s : α → List α} {T₀ : List α × List α}
    {a b : Anchored s T₀} (h : Relation.TransGen (anchoredGraph s T₀).child a b) :
    a.1.1.level < b.1.1.level := by
  induction h with
  | single h => rw [anchoredGraph_level h]; omega
  | tail _ h ih => rw [anchoredGraph_level h]; omega

/-- Levels along actual paths: `Reach` does not lower the level. -/
theorem anchoredGraph_reach_level {s : α → List α} {T₀ : List α × List α}
    {a b : Anchored s T₀} (h : (anchoredGraph s T₀).Reach a b) :
    a.1.1.level ≤ b.1.1.level := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => rw [anchoredGraph_level h]; omega

/-- **Levels increase: the actual graph has no cycle.**  A cycle of the literal occurrence
graph is therefore never the reading of an actual cycle; it is the reading of an infinite
actual lineage (`absLineage_anchor`) and of nothing else. -/
theorem anchored_no_cycle (s : α → List α) (T₀ : List α × List α) (a : Anchored s T₀) :
    ¬ Relation.TransGen (anchoredGraph s T₀).child a a :=
  fun h => lt_irrefl _ (anchoredGraph_transGen_level h)

/-- (AE°) holds at every anchored pair, vacuously: no state of the actual graph lies on a
cycle. -/
theorem anchored_cyclicProductive (s : α → List α) (T₀ : List α × List α) (a : Anchored s T₀) :
    (anchoredGraph s T₀).CyclicProductive a :=
  fun t _ ht => absurd ht (anchored_no_cycle s T₀ t)

/-! ### Choice-free infinite lifting -/

/-- The absolute lineage along a digit sequence, by recursion on `absStep`. -/
def absLineage (s : α → List α) (T₀ : List α × List α) (x : AbsOcc) (ds : ℕ → ℕ × ℕ) :
    ℕ → Option AbsOcc
  | 0 => some x
  | n + 1 => (absLineage s T₀ x ds n).bind fun z => absStep s T₀ z (ds n).1 (ds n).2

/-- **Choice-free infinite lifting**: a digit-labelled infinite path of the literal
occurrence graph from the reading of `x` is the reading of the absolute lineage of `x`
along the same digits, level by level. -/
theorem absLineage_anchor {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {off : ℕ}
    (p : ℕ → Occ α) (ds : ℕ → ℕ × ℕ) (ha : Anchor s T₀ x (p 0) off)
    (hp : ∀ n, occStep s (p n) (ds n).1 (ds n).2 = some (.child (p (n + 1)))) :
    ∀ n, ∃ z off', absLineage s T₀ x ds n = some z ∧ z.level = x.level + n ∧
      Anchor s T₀ z (p n) off' := by
  intro n
  induction n with
  | zero => exact ⟨x, off, rfl, rfl, ha⟩
  | succ n ih =>
    obtain ⟨z, off', hz, hl, haz⟩ := ih
    obtain ⟨z', off'', hz', haz'⟩ := anchor_step haz (hp n)
    refine ⟨z', off'', by simp [absLineage, hz, hz'], ?_, haz'⟩
    rw [absStep_level hz']
    omega

omit [DecidableEq α] in
/-- The lineage raises the level by its length. -/
theorem absLineage_level {s : α → List α} {T₀ : List α × List α} {x : AbsOcc}
    {ds : ℕ → ℕ × ℕ} : ∀ (n : ℕ) {z : AbsOcc}, absLineage s T₀ x ds n = some z →
      z.level = x.level + n
  | 0, z, h => by
    simp only [absLineage, Option.some.injEq] at h
    subst h
    rfl
  | n + 1, z, h => by
    simp only [absLineage] at h
    obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.1 h
    rw [absStep_level hz, absLineage_level n hw]
    omega

/-! ### Splits are final -/

/-- A zero return of the iterates strictly inside an anchored irreducible block contradicts
its irreducibility. -/
theorem Anchor.not_zero_inside {s : α → List α} {T₀ : List α × List α} {x : AbsOcc}
    {y : Occ α} {off : ℕ} (ha : Anchor s T₀ x y off)
    (hirr : IrreduciblePair y.block.1 y.block.2) {Z : ℕ}
    (hZ : Equiv1 (((subst s)^[x.level] T₀.1).take Z) (((subst s)^[x.level] T₀.2).take Z))
    (h1 : off < Z) (h2 : Z < off + y.block.1.length) : False := by
  have hl : y.block.2.length = y.block.1.length := ha.balanced.length_eq.symm
  obtain ⟨k, rfl⟩ : ∃ k, Z = off + k := ⟨Z - off, by omega⟩
  rw [take_add_of_factor ha.top_factor k (by omega),
    take_add_of_factor ha.bot_factor k (by omega)] at hZ
  exact hirr k (by omega) (by omega) (equiv1_cancel ha.zero hZ)

/-- Two absolute positions of one level are **separated**: a zero return of the iterates lies
strictly after one of them and at or before the other. -/
def Separated (s : α → List α) (T₀ : List α × List α) (x : AbsOcc) : Prop :=
  ∃ Z, Equiv1 (((subst s)^[x.level] T₀.1).take Z) (((subst s)^[x.level] T₀.2).take Z) ∧
    ((x.top < Z ∧ Z ≤ x.bot) ∨ (x.bot < Z ∧ Z ≤ x.top))

/-- Separation is inherited by every absolute child (`lem:inherited` on the separating zero
return). -/
theorem Separated.step {s : α → List α} {T₀ : List α × List α} {x x' : AbsOcc} {d e : ℕ}
    (hsep : Separated s T₀ x) (h : absStep s T₀ x d e = some x') : Separated s T₀ x' := by
  obtain ⟨hP, hQ, hd, he, rfl⟩ := absStep_some h
  obtain ⟨Z, hZ, hord⟩ := hsep
  refine ⟨imgStart s ((subst s)^[x.level] T₀.1) Z, ?_, ?_⟩
  · show Equiv1 (((subst s)^[x.level + 1] T₀.1).take _) (((subst s)^[x.level + 1] T₀.2).take _)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (inherited s hZ).2
  · have h1 := imgStart_succ s _ hP
    have h2 := imgStart_succ s _ hQ
    have hZe := imgStart_eq_of_equiv1 s hZ
    dsimp only
    rcases hord with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · left
      have := imgStart_mono s ((subst s)^[x.level] T₀.1) (show x.top + 1 ≤ Z by omega)
      have := imgStart_mono s ((subst s)^[x.level] T₀.2) h4
      omega
    · right
      have := imgStart_mono s ((subst s)^[x.level] T₀.2) (show x.bot + 1 ≤ Z by omega)
      have := imgStart_mono s ((subst s)^[x.level] T₀.1) h4
      omega

/-- Separation is inherited along every absolute lineage. -/
theorem Separated.lineage {s : α → List α} {T₀ : List α × List α} {x : AbsOcc}
    (hsep : Separated s T₀ x) (ds : ℕ → ℕ × ℕ) :
    ∀ (n : ℕ) {z : AbsOcc}, absLineage s T₀ x ds n = some z → Separated s T₀ z
  | 0, z, h => by
    simp only [absLineage, Option.some.injEq] at h
    exact h ▸ hsep
  | n + 1, z, h => by
    simp only [absLineage] at h
    obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.1 h
    exact (hsep.lineage ds n hw).step hz

/-- A separated absolute pair has no irreducible reading with both positions inside the
block. -/
theorem Separated.not_anchor {s : α → List α} {T₀ : List α × List α} {x : AbsOcc}
    (hsep : Separated s T₀ x) {y : Occ α} {off : ℕ} (ha : Anchor s T₀ x y off)
    (hy : IsBlock y.block) (hP : y.top < y.block.1.length) (hQ : y.bot < y.block.2.length) :
    False := by
  obtain ⟨Z, hZ, hord⟩ := hsep
  have hl : y.block.2.length = y.block.1.length := ha.balanced.length_eq.symm
  have ht := ha.top_pos
  have hb := ha.bot_pos
  refine ha.not_zero_inside hy.2.2 hZ ?_ ?_ <;> omega

/-- The prefix of the next iterate up to the image of an anchored block, cut at `b`. -/
theorem Anchor.take_inflate {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y : Occ α}
    {off : ℕ} (ha : Anchor s T₀ x y off) {b : ℕ} (hb : b ≤ (subst s y.block.1).length) :
    ((subst s)^[x.level + 1] T₀.1).take (imgStart s ((subst s)^[x.level] T₀.1) off + b) =
        subst s (((subst s)^[x.level] T₀.1).take off) ++ (subst s y.block.1).take b ∧
      ((subst s)^[x.level + 1] T₀.2).take (imgStart s ((subst s)^[x.level] T₀.1) off + b) =
        subst s (((subst s)^[x.level] T₀.2).take off) ++ (subst s y.block.2).take b := by
  have hE : Equiv1 (subst s y.block.1) (subst s y.block.2) := equiv1_subst s ha.balanced
  have hlen : imgStart s ((subst s)^[x.level] T₀.2) off =
      imgStart s ((subst s)^[x.level] T₀.1) off := ((equiv1_subst s ha.zero).length_eq).symm
  have hb2 : b ≤ (subst s y.block.2).length := hE.length_eq ▸ hb
  have hsu : subst s ((subst s)^[x.level] T₀.1) =
      subst s (((subst s)^[x.level] T₀.1).take off) ++ (subst s y.block.1 ++
        subst s (((subst s)^[x.level] T₀.1).drop (off + y.block.1.length))) := by
    conv_lhs => rw [factor_eq ha.top_factor]
    rw [subst_append, subst_append]
  have hsv : subst s ((subst s)^[x.level] T₀.2) =
      subst s (((subst s)^[x.level] T₀.2).take off) ++ (subst s y.block.2 ++
        subst s (((subst s)^[x.level] T₀.2).drop (off + y.block.2.length))) := by
    conv_lhs => rw [factor_eq ha.bot_factor]
    rw [subst_append, subst_append]
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  constructor
  · rw [hsu]
    unfold imgStart
    rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.take_append_of_le_length hb]
  · rw [hsv, ← hlen]
    unfold imgStart
    rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.take_append_of_le_length hb2]

/-- A split of the reading separates the absolute child. -/
theorem Anchor.split_separated {s : α → List α} {T₀ : List α × List α} {x : AbsOcc}
    {y : Occ α} {off d e k k' : ℕ} (ha : Anchor s T₀ x y off)
    (h : occStep s y d e = some (.split k k')) :
    ∃ x', absStep s T₀ x d e = some x' ∧ Separated s T₀ x' := by
  obtain ⟨hP, hQ, hd, he, hk, hk', hkk⟩ := occStep_split_iff.1 h
  have hE : Equiv1 (subst s y.block.1) (subst s y.block.2) := equiv1_subst s ha.balanced
  have hlen : imgStart s ((subst s)^[x.level] T₀.2) off =
      imgStart s ((subst s)^[x.level] T₀.1) off := ((equiv1_subst s ha.zero).length_eq).symm
  obtain ⟨hkl, hk1, hk2⟩ := (blockAt_spec _ _ _).1 hk
  obtain ⟨hkl', hk1', hk2'⟩ := (blockAt_spec _ _ _).1 hk'
  have htop : imgStart s ((subst s)^[x.level] T₀.1) x.top + d =
      imgStart s ((subst s)^[x.level] T₀.1) off + (imgStart s y.block.1 y.top + d) := by
    rw [ha.top_pos, imgStart_add_of_factor s ha.top_factor hP.le]
    omega
  have hbot : imgStart s ((subst s)^[x.level] T₀.2) x.bot + e =
      imgStart s ((subst s)^[x.level] T₀.1) off + (imgStart s y.block.2 y.bot + e) := by
    rw [ha.bot_pos, imgStart_add_of_factor s ha.bot_factor hQ.le, hlen]
    omega
  have hx : absStep s T₀ x d e = some ⟨x.level + 1,
      imgStart s ((subst s)^[x.level] T₀.1) x.top + d,
      imgStart s ((subst s)^[x.level] T₀.2) x.bot + e⟩ := by
    unfold absStep
    rw [ha.top_pos, ha.bot_pos, getElem?_of_factor ha.top_factor hP,
      getElem?_of_factor ha.bot_factor hQ, List.getElem?_eq_getElem hP,
      List.getElem?_eq_getElem hQ]
    simp [hd, he]
  refine ⟨_, hx, ?_⟩
  -- the separating zero return: the end of the earlier of the two blocks
  have hzero : ∀ m, Equiv1
      (((subst s)^[x.level + 1] T₀.1).take (imgStart s ((subst s)^[x.level] T₀.1) off +
        blockStart (red (subst s y.block.1) (subst s y.block.2)) m))
      (((subst s)^[x.level + 1] T₀.2).take (imgStart s ((subst s)^[x.level] T₀.1) off +
        blockStart (red (subst s y.block.1) (subst s y.block.2)) m)) := by
    intro m
    obtain ⟨e1, e2⟩ := ha.take_inflate (blockStart_le hE.length_eq m)
    rw [e1, e2]
    exact (equiv1_subst s ha.zero).append (equiv1_take_blockStart hE m)
  rcases Nat.lt_or_gt_of_ne hkk with hlt | hlt
  · refine ⟨_, hzero (k + 1), Or.inl ⟨?_, ?_⟩⟩
    · dsimp only
      rw [htop, blockStart_succ _ hkl]
      omega
    · dsimp only
      rw [hbot]
      have := blockStart_mono (red (subst s y.block.1) (subst s y.block.2))
        (show k + 1 ≤ k' by omega)
      omega
  · refine ⟨_, hzero (k' + 1), Or.inr ⟨?_, ?_⟩⟩
    · dsimp only
      rw [hbot, blockStart_succ _ hkl']
      omega
    · dsimp only
      rw [htop]
      have := blockStart_mono (red (subst s y.block.1) (subst s y.block.2))
        (show k' + 1 ≤ k by omega)
      omega

/-- **A split**: the absolute child exists and is not the reading of any irreducible block
containing both positions. -/
theorem anchor_split {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y : Occ α}
    {off d e k k' : ℕ} (ha : Anchor s T₀ x y off)
    (h : occStep s y d e = some (.split k k')) :
    ∃ x', absStep s T₀ x d e = some x' ∧
      ¬ ∃ (y' : Occ α) (off' : ℕ), IsBlock y'.block ∧ y'.top < y'.block.1.length ∧
        y'.bot < y'.block.2.length ∧ Anchor s T₀ x' y' off' := by
  obtain ⟨x', hx', hsep⟩ := ha.split_separated h
  exact ⟨x', hx', fun ⟨y', off', hB, hP, hQ, ha'⟩ => hsep.not_anchor ha' hB hP hQ⟩

/-- **Splits never rejoin**: no absolute descendant of a split child, along any digit sequence
and at any depth, has an irreducible reading containing both positions.  A Lean counterpart,
for absolute pairs, of the prose sentence "their disjoint balanced spans remain disjoint on
inflation" of `kernel/psc/target_packets.mojo`; no Mojo code is read.  No balance hypothesis
`Equiv1 T₀.1 T₀.2` on the root is needed, and none is assumed. -/
theorem split_never_rejoins {s : α → List α} {T₀ : List α × List α}
    {x : AbsOcc} {y : Occ α} {off d e k k' : ℕ} (ha : Anchor s T₀ x y off)
    (h : occStep s y d e = some (.split k k')) (ds : ℕ → ℕ × ℕ) (n : ℕ) {z : AbsOcc}
    (hz : (absStep s T₀ x d e).bind (fun x' => absLineage s T₀ x' ds n) = some z) :
    ¬ ∃ (y' : Occ α) (off' : ℕ), IsBlock y'.block ∧ y'.top < y'.block.1.length ∧
        y'.bot < y'.block.2.length ∧ Anchor s T₀ z y' off' := by
  obtain ⟨x', hx', hsep⟩ := ha.split_separated h
  rw [hx', Option.bind_some] at hz
  rintro ⟨y', off', hB, hP, hQ, ha'⟩
  exact (hsep.lineage ds n hz).not_anchor ha' hB hP hQ

/-! ### Irreducible readings: uniqueness, the block of the reduction, the parent -/

/-- The end of an anchored block is a zero return of the iterates. -/
theorem Anchor.zero_end {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y : Occ α}
    {off : ℕ} (ha : Anchor s T₀ x y off) :
    Equiv1 (((subst s)^[x.level] T₀.1).take (off + y.block.1.length))
      (((subst s)^[x.level] T₀.2).take (off + y.block.1.length)) := by
  have hl : y.block.2.length = y.block.1.length := ha.balanced.length_eq.symm
  rw [take_add_of_factor ha.top_factor _ le_rfl, List.take_length,
    take_add_of_factor ha.bot_factor _ hl.ge, ← hl, List.take_length]
  exact ha.zero.append ha.balanced

/-- **Irreducible readings are unique**: two readings of one absolute pair by irreducible
blocks containing the top position have the same offset, block and local positions (the birth
record is not compared: `Anchor` does not read it). -/
theorem anchor_unique {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y y' : Occ α}
    {off off' : ℕ} (ha : Anchor s T₀ x y off) (ha' : Anchor s T₀ x y' off')
    (hy : IsBlock y.block) (hy' : IsBlock y'.block) (hP : y.top < y.block.1.length)
    (hP' : y'.top < y'.block.1.length) :
    off = off' ∧ y.block = y'.block ∧ y.top = y'.top ∧ y.bot = y'.bot := by
  have ht := ha.top_pos
  have ht' := ha'.top_pos
  have hoff : off = off' := by
    rcases lt_trichotomy off off' with h | h | h
    · exact (ha.not_zero_inside hy.2.2 ha'.zero h (by omega)).elim
    · exact h
    · exact (ha'.not_zero_inside hy'.2.2 ha.zero h (by omega)).elim
  subst hoff
  have hpos := List.length_pos_iff.2 hy.1
  have hpos' := List.length_pos_iff.2 hy'.1
  have hlen : y.block.1.length = y'.block.1.length := by
    rcases lt_trichotomy y.block.1.length y'.block.1.length with h | h | h
    · exact (ha'.not_zero_inside hy'.2.2 ha.zero_end (by omega) (by omega)).elim
    · exact h
    · exact (ha.not_zero_inside hy.2.2 ha'.zero_end (by omega) (by omega)).elim
  have hl : y.block.2.length = y.block.1.length := ha.balanced.length_eq.symm
  have hl' : y'.block.2.length = y'.block.1.length := ha'.balanced.length_eq.symm
  have h1 : y.block.1 = y'.block.1 := by
    rw [← ha.top_factor, ← ha'.top_factor, hlen]
  have h2 : y.block.2 = y'.block.2 := by
    rw [← ha.bot_factor, ← ha'.bot_factor, hl, hl', hlen]
  have hb := ha.bot_pos
  have hb' := ha'.bot_pos
  exact ⟨rfl, Prod.ext h1 h2, by omega, by omega⟩

/-- **An irreducible reading is a block of the reduction of the iterates**: for a balanced root,
the block of an anchored irreducible reading is one of the blocks of
`red (σⁿ T₀.1) (σⁿ T₀.2)` (`n` the level). -/
theorem Anchor.mem_red {s : α → List α} {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2)
    {x : AbsOcc} {y : Occ α} {off : ℕ} (ha : Anchor s T₀ x y off) (hy : IsBlock y.block) :
    y.block ∈ red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2) := by
  have hW := equiv1_iterate_subst s x.level hT
  have hl : y.block.2.length = y.block.1.length := ha.balanced.length_eq.symm
  have h1 := factor_eq ha.top_factor
  have h2 := factor_eq ha.bot_factor
  rw [hl] at h2
  have hpre : Equiv1 (((subst s)^[x.level] T₀.1).take off ++ y.block.1)
      (((subst s)^[x.level] T₀.2).take off ++ y.block.2) := ha.zero.append ha.balanced
  have hrest : Equiv1 (((subst s)^[x.level] T₀.1).drop (off + y.block.1.length))
      (((subst s)^[x.level] T₀.2).drop (off + y.block.1.length)) := by
    refine equiv1_cancel hpre ?_
    rw [List.append_assoc, List.append_assoc, ← h1, ← h2]
    exact hW
  rw [h1, h2, red_append ha.zero (ha.balanced.append hrest),
    red_append ha.balanced hrest, red_of_isBlock hy]
  simp

omit [DecidableEq α] in
/-- Every position of `σ w` is digit `r` of the image of some letter `w[i]`. -/
theorem exists_imgStart_add (s : α → List α) (w : List α) {p : ℕ}
    (hp : p < (subst s w).length) :
    ∃ (i : ℕ) (hi : i < w.length) (r : ℕ), r < (s w[i]).length ∧ p = imgStart s w i + r := by
  obtain ⟨hi, hr, ht⟩ := cutAddr_spec s w p hp
  refine ⟨_, hi, _, hr, ?_⟩
  have := congrArg List.length ht
  rw [List.length_take, List.length_append, List.length_take, min_eq_left hp.le,
    min_eq_left hr.le] at this
  exact this

omit [DecidableEq α] in
/-- Every absolute pair of positive level inside the iterates is the absolute child of an
absolute pair one level below. -/
theorem exists_absStep_parent {s : α → List α} {T₀ : List α × List α} {x' : AbsOcc} {n : ℕ}
    (hl : x'.level = n + 1) (hP : x'.top < ((subst s)^[x'.level] T₀.1).length)
    (hQ : x'.bot < ((subst s)^[x'.level] T₀.2).length) :
    ∃ (x : AbsOcc) (d e : ℕ), x.level = n ∧ absStep s T₀ x d e = some x' := by
  rcases x' with ⟨l, P, Q⟩
  simp only at hl hP hQ
  subst hl
  rw [Function.iterate_succ_apply'] at hP hQ
  obtain ⟨i, hi, d, hd, rfl⟩ := exists_imgStart_add s _ hP
  obtain ⟨j, hj, e, he, rfl⟩ := exists_imgStart_add s _ hQ
  exact ⟨⟨n, i, j⟩, d, e, rfl, absStep_of hi hj hd he⟩

/-- **The reading at a block of the reduction of the iterates.**  For a balanced root, an
absolute pair whose two positions lie in the `j`-th block of `red (σⁿ T₀.1) (σⁿ T₀.2)` is read
by that block at its start offset, with any birth record; the block is irreducible and both
local positions lie inside it. -/
theorem anchor_of_red {s : α → List α} {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2)
    {x : AbsOcc} {j : ℕ}
    (hj : j < (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)).length)
    (h1 : blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j ≤ x.top)
    (h2 : x.top < blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j +
      (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].1.length)
    (h3 : blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j ≤ x.bot)
    (h4 : x.bot < blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j +
      (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].1.length)
    (b : Option (Birth α)) :
    Anchor s T₀ x ⟨(red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j],
        x.top - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j,
        x.bot - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j, b⟩
        (blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j) ∧
      IsBlock (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j] ∧
      x.top - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j <
        (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].1.length ∧
      x.bot - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j <
        (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].2.length := by
  have hW := equiv1_iterate_subst s x.level hT
  have hB : IsBlock (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j] :=
    red_isBlock hW _ (List.getElem_mem hj)
  have hg := getElem_red hW j hj
  have hl2 : (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].2.length =
      (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].1.length :=
    hB.2.1.length_eq.symm
  refine ⟨⟨hB.2.1, equiv1_take_blockStart hW j, (congrArg Prod.fst hg).symm, ?_, ?_, ?_⟩, hB,
    by omega, by rw [hl2]; omega⟩
  · show (((subst s)^[x.level] T₀.2).drop _).take
      (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].2.length = _
    rw [hl2]
    exact (congrArg Prod.snd hg).symm
  · show x.top = _ + (x.top - _)
    omega
  · show x.bot = _ + (x.bot - _)
    omega

/-- **Parent closure** (with `anchor_unique`): if the absolute child `x'` of `x` along `(d, e)`
has an irreducible reading containing both positions, then `x` has an irreducible reading
containing both positions (the block of `red (σⁿ T₀.1) (σⁿ T₀.2)` covering `x.top`, read with no
birth record), and the reading of `x'` is its literal child along the same digits, with the
birth record of that parent block. -/
theorem anchor_parent_inside {s : α → List α} {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2)
    {x x' : AbsOcc} {d e : ℕ} (hx : absStep s T₀ x d e = some x') {y' : Occ α} {off' : ℕ}
    (hy' : IsBlock y'.block) (hP : y'.top < y'.block.1.length) (hQ : y'.bot < y'.block.2.length)
    (ha' : Anchor s T₀ x' y' off') :
    ∃ (y : Occ α) (off k : ℕ), IsBlock y.block ∧ Anchor s T₀ x y off ∧
      y.top < y.block.1.length ∧ y.bot < y.block.2.length ∧ y.birth = none ∧
      occStep s y d e = some (.child ⟨y'.block, y'.top, y'.bot, some ⟨y.block, k⟩⟩) := by
  have hW := equiv1_iterate_subst s x.level hT
  obtain ⟨hPx, hQx, hd, he, -⟩ := absStep_some hx
  have hsum : ((red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)).map
      fun T => T.1.length).sum = ((subst s)^[x.level] T₀.1).length := by
    have := congrArg List.length (red_top hW.length_eq)
    rw [List.length_flatten, List.map_map] at this
    exact this
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (blockAt_isSome _ _ (hsum ▸ hPx :
    x.top < ((red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)).map
      fun T => T.1.length).sum))
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.1 (blockAt_isSome _ _
    ((hsum.trans hW.length_eq) ▸ hQx :
    x.bot < ((red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)).map
      fun T => T.1.length).sum))
  obtain ⟨hjl, hj1, hj2⟩ := (blockAt_spec _ _ _).1 hj
  obtain ⟨hjl', hj1', hj2'⟩ := (blockAt_spec _ _ _).1 hj'
  -- both positions lie in one block, else the child is separated
  have hjj : j = j' := by
    by_contra hne
    have hsep : Separated s T₀ x := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · refine ⟨_, equiv1_take_blockStart hW (j + 1), Or.inl ⟨?_, ?_⟩⟩
        · rw [blockStart_succ _ hjl]
          omega
        · exact le_trans (blockStart_mono _ (by omega)) hj1'
      · refine ⟨_, equiv1_take_blockStart hW (j' + 1), Or.inr ⟨?_, ?_⟩⟩
        · rw [blockStart_succ _ hjl']
          omega
        · exact le_trans (blockStart_mono _ (by omega)) hj1
    exact (hsep.step hx).not_anchor ha' hy' hP hQ
  subst hjj
  obtain ⟨ha, hB, hyP, hyQ⟩ := anchor_of_red hT hjl hj1 hj2 hj1' hj2' none
  set y : Occ α := ⟨(red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j],
    x.top - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j,
    x.bot - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j, none⟩
  change y.top < y.block.1.length at hyP
  change y.bot < y.block.2.length at hyQ
  change IsBlock y.block at hB
  obtain ⟨hlt, hlb⟩ := ha.letters hyP hyQ
  rw [List.getElem?_eq_getElem hPx, List.getElem?_eq_getElem hyP] at hlt
  rw [List.getElem?_eq_getElem hQx, List.getElem?_eq_getElem hyQ] at hlb
  have hd' : d < (s y.block.1[y.top]).length := Option.some.inj hlt ▸ hd
  have he' : e < (s y.block.2[y.bot]).length := Option.some.inj hlb ▸ he
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (occStep_isSome (s := s) hB.2.1 hyP hyQ hd' he')
  cases o with
  | split k k' =>
    obtain ⟨x'', hx'', hno⟩ := anchor_split ha ho
    rw [hx] at hx''
    obtain rfl := Option.some.inj hx''
    exact (hno ⟨y', off', hy', hP, hQ, ha'⟩).elim
  | child y'' =>
    obtain ⟨x'', off'', hx'', ha''⟩ := anchor_step ha ho
    rw [hx] at hx''
    obtain rfl := Option.some.inj hx''
    obtain ⟨hB'', hP'', -⟩ := occStep_child_isBlock hB.2.1 ho
    obtain ⟨-, hbl, htp, hbt⟩ := anchor_unique ha'' ha' hB'' hy' hP'' hP
    obtain ⟨-, -, k, _, -, -, -, -, -, -, hy''⟩ := occStep_child_iff.1 ho
    have hbirth : y''.birth = some ⟨y.block, k⟩ := by rw [hy'']
    refine ⟨y, _, k, hB, ha, hyP, hyQ, rfl, ?_⟩
    rw [ho]
    rcases y'' with ⟨b, t, q, br⟩
    simp only at hbl htp hbt hbirth
    rw [hbl, htp, hbt, hbirth]

/-- **Parent closure** (`anchor_parent_inside` without the position bounds and the empty birth
record of the parent reading): if the absolute child `x'` of `x` along `(d, e)` has an
irreducible reading containing both positions, then `x` has an irreducible reading whose
literal child along `(d, e)` is that reading, born of the parent block. -/
theorem anchor_parent {s : α → List α} {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2)
    {x x' : AbsOcc} {d e : ℕ} (hx : absStep s T₀ x d e = some x') {y' : Occ α} {off' : ℕ}
    (hy' : IsBlock y'.block) (hP : y'.top < y'.block.1.length) (hQ : y'.bot < y'.block.2.length)
    (ha' : Anchor s T₀ x' y' off') :
    ∃ (y : Occ α) (off k : ℕ), IsBlock y.block ∧ Anchor s T₀ x y off ∧
      occStep s y d e = some (.child ⟨y'.block, y'.top, y'.bot, some ⟨y.block, k⟩⟩) :=
  let ⟨y, off, k, hB, ha, _, _, _, h⟩ := anchor_parent_inside hT hx hy' hP hQ ha'
  ⟨y, off, k, hB, ha, h⟩

/-! ### The declared occurrence universe -/

/-- **The declared occurrence universe** of a root pair `T₀`: the anchored pairs reached by
retained edges from a level-0 position pair of `T₀` read as `T₀` itself with no birth. -/
def Universe (s : α → List α) (T₀ : List α × List α) : Set (Anchored s T₀) :=
  {a | ∃ b : Anchored s T₀, b.1.1.level = 0 ∧ b.1.2 = ⟨T₀, b.1.1.top, b.1.1.bot, none⟩ ∧
    b.1.1.top < T₀.1.length ∧ b.1.1.bot < T₀.2.length ∧ (anchoredGraph s T₀).Reach b a}

/-- The universe is closed under retained edges. -/
theorem universe_closed (s : α → List α) (T₀ : List α × List α) :
    (anchoredGraph s T₀).Closed (Universe s T₀) :=
  fun _ _ ⟨b, h0, h1, h2, h3, hb⟩ hab => ⟨b, h0, h1, h2, h3, hb.tail hab⟩

/-- The root reading of a position pair of a balanced root. -/
def rootAnchored (s : α → List α) {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2) (P Q : ℕ) :
    Anchored s T₀ :=
  ⟨(⟨0, P, Q⟩, ⟨T₀, P, Q, none⟩), 0, anchor_root s hT P Q⟩

/-- Every position pair of a balanced root is in the universe. -/
theorem rootAnchored_mem (s : α → List α) {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2)
    {P Q : ℕ} (hP : P < T₀.1.length) (hQ : Q < T₀.2.length) :
    rootAnchored s hT P Q ∈ Universe s T₀ :=
  ⟨_, rfl, rfl, hP, hQ, .refl⟩

/-- At level `0` the universe consists of the root readings. -/
theorem universe_level_zero {s : α → List α} {T₀ : List α × List α} {a : Anchored s T₀}
    (ha : a ∈ Universe s T₀) (hl : a.1.1.level = 0) :
    a.1.2 = ⟨T₀, a.1.1.top, a.1.1.bot, none⟩ ∧ a.1.1.top < T₀.1.length ∧
      a.1.1.bot < T₀.2.length := by
  obtain ⟨b, h0, h1, h2, h3, hb⟩ := ha
  rcases Relation.ReflTransGen.cases_tail hb with rfl | ⟨c, -, hc⟩
  · exact ⟨h1, h2, h3⟩
  · have := anchoredGraph_level hc
    omega

/-- Above level `0`, every element of the universe is the retained child of an element of the
universe. -/
theorem universe_succ {s : α → List α} {T₀ : List α × List α} {a : Anchored s T₀} {n : ℕ}
    (ha : a ∈ Universe s T₀) (hl : a.1.1.level = n + 1) :
    ∃ c ∈ Universe s T₀, (anchoredGraph s T₀).child c a := by
  obtain ⟨b, h0, h1, h2, h3, hb⟩ := ha
  rcases Relation.ReflTransGen.cases_tail hb with rfl | ⟨c, hbc, hc⟩
  · omega
  · exact ⟨c, ⟨b, h0, h1, h2, h3, hbc⟩, hc⟩

/-- **On the universe the reading is a function of the absolute pair**: two elements of the
universe over the same absolute pair are equal, birth record included (that record is the
block of the reading of the element over the absolute parent, `universe_birth`).  Induction on
the level: `absStep` is injective in (source, digits)
(`absStep_inj`), so both elements are retained children of elements over one absolute parent
along one digit pair, equal by induction, and `occStep` is a function.  No hypothesis on `s`
or `T₀`. -/
theorem universe_reading_unique {s : α → List α} {T₀ : List α × List α} {a b : Anchored s T₀}
    (ha : a ∈ Universe s T₀) (hb : b ∈ Universe s T₀) (h : a.1.1 = b.1.1) : a = b := by
  suffices H : ∀ (n : ℕ) (a b : Anchored s T₀), a ∈ Universe s T₀ → b ∈ Universe s T₀ →
      a.1.1 = b.1.1 → a.1.1.level = n → a = b from H _ a b ha hb h rfl
  intro n
  induction n with
  | zero =>
    intro a b ha hb h hl
    have h1 := (universe_level_zero ha hl).1
    have h2 := (universe_level_zero hb (h ▸ hl)).1
    apply Subtype.ext
    apply Prod.ext h
    rw [h1, h2, h]
  | succ n ih =>
    intro a b ha hb h hl
    obtain ⟨c, hc, -, d, e, hx, hy⟩ := universe_succ ha hl
    obtain ⟨c', hc', -, d', e', hx', hy'⟩ := universe_succ hb (h ▸ hl)
    rw [← h] at hx'
    obtain ⟨hxx, rfl, rfl⟩ := absStep_inj hx hx'
    have hcl : c.1.1.level = n := by
      have := absStep_level hx
      omega
    obtain rfl := ih c c' hc hc' hxx hcl
    rw [hy] at hy'
    apply Subtype.ext
    apply Prod.ext h
    simpa using hy'

/-- **The birth record on the universe is the reading of the absolute parent.**  Above level
`0`, an element `a` of the universe is the retained child of an element `c` of the universe
whose absolute pair steps to that of `a`, and the birth record of the reading of `a` is the
block of the reading of `c`, at some ordinal `k`.  The absolute parent `c.1.1` is the only
absolute pair with an absolute step to `a.1.1` (`absStep_inj`), and `c` is the only element of
the universe over it (`universe_reading_unique`).  No hypothesis on `s` or `T₀`. -/
theorem universe_birth {s : α → List α} {T₀ : List α × List α} {a : Anchored s T₀} {n : ℕ}
    (ha : a ∈ Universe s T₀) (hl : a.1.1.level = n + 1) :
    ∃ c ∈ Universe s T₀, ∃ d e k, (anchoredGraph s T₀).child c a ∧
      absStep s T₀ c.1.1 d e = some a.1.1 ∧
      (reading s T₀ a).birth = some ⟨(reading s T₀ c).block, k⟩ := by
  obtain ⟨c, hc, hca⟩ := universe_succ ha hl
  obtain ⟨hne, d, e, hx, hy⟩ := hca
  obtain ⟨_, _, k, _, _, _, _, _, _, _, hyeq⟩ := occStep_child_iff.1 hy
  refine ⟨c, hc, d, e, k, ⟨hne, d, e, hx, hy⟩, hx, ?_⟩
  show a.1.2.birth = _
  rw [hyeq]
  rfl

/-! ### ρ on the declared universe -/

/-- **The actual graph on the declared universe**: the retained edges of `anchoredGraph s T₀`
between elements of `Universe s T₀`, targets the coincidence blocks. -/
def universeGraph (s : α → List α) (T₀ : List α × List α) : ChildGraph (Universe s T₀) where
  child a b := (anchoredGraph s T₀).child a.1 b.1
  target a := (anchoredGraph s T₀).target a.1

/-- **The top square on the declared universe**: the reading is a refinement of the actual
graph induced on the universe onto `occGraph s` (soundness from every source of the universe:
the lift of `reading_soundEvery` stays in the universe, `universe_closed`), and the absolute pair
is injective on the universe (`universe_reading_unique`).  No hypothesis on `s` or `T₀`. -/
theorem universe_refines (s : α → List α) (T₀ : List α × List α) :
    Refines (universeGraph s T₀) (occGraph s) (fun a => reading s T₀ a.1) ∧
      Function.Injective (fun a : Universe s T₀ => a.1.1.1) := by
  refine ⟨⟨fun _ _ h => reading_complete s T₀ h, fun a y' h => ?_, fun _ h => h, fun _ h => h⟩,
    fun a b h => Subtype.ext (universe_reading_unique a.2 b.2 h)⟩
  obtain ⟨b, hb, rfl⟩ := reading_soundEvery s T₀ a.1 h
  exact ⟨⟨b, universe_closed s T₀ a.2 hb⟩, hb, rfl⟩

/-- The readings (E), (AE), (A), (A⁺) agree between an element of the universe (in the actual
graph induced on the universe) and its reading, and (AE°) pulls back from the reading. -/
theorem universe_readings (s : α → List α) (T₀ : List α × List α) (a : Universe s T₀) :
    ((universeGraph s T₀).Productive a ↔ (occGraph s).Productive (reading s T₀ a.1)) ∧
      ((universeGraph s T₀).HereditarilyProductive a ↔
        (occGraph s).HereditarilyProductive (reading s T₀ a.1)) ∧
      ((universeGraph s T₀).Inevitable a ↔ (occGraph s).Inevitable (reading s T₀ a.1)) ∧
      ((universeGraph s T₀).InevMax a ↔ (occGraph s).InevMax (reading s T₀ a.1)) ∧
      ((occGraph s).CyclicProductive (reading s T₀ a.1) →
        (universeGraph s T₀).CyclicProductive a) :=
  let h := (universe_refines s T₀).1
  ⟨h.productive_iff, h.hereditarilyProductive_iff, h.inevitable_iff, h.inevMax_iff,
    h.cyclicProductive_of_quotient⟩

/-- The actual graph on the declared universe for a packet target letter: the edges of
`universeGraph s T₀`, targets the packet successes `Occ.SuccessFor target` of the reading. -/
def universeGraphFor (s : α → List α) (T₀ : List α × List α) (target : Option α) :
    ChildGraph (Universe s T₀) where
  child := (universeGraph s T₀).child
  target a := a.1.1.2.SuccessFor target

/-- **The top square on the declared universe, success target**: the reading is a refinement of
`universeGraphFor s T₀ target` onto `occGraphFor s target`.  No hypothesis on `s`, `T₀` or
`target`. -/
theorem universe_refines_for (s : α → List α) (T₀ : List α × List α) (target : Option α) :
    Refines (universeGraphFor s T₀ target) (occGraphFor s target) (fun a => reading s T₀ a.1) :=
  let h := (universe_refines s T₀).1
  ⟨h.complete, h.soundEvery, fun _ h => h, fun _ h => h⟩

/-- For an irreducible root, every reading in the universe is a literal occurrence pair
(`Occ.Valid`: an irreducible block, both positions inside it, and, above level `0`, born as the
recorded ordinal child of the recorded noncoincident irreducible parent block).  That the
recorded parent block is the block of the reading of the element of the universe over the
absolute parent is `universe_birth`. -/
theorem universe_valid {s : α → List α} {T₀ : List α × List α} (hT : IsBlock T₀)
    {a : Anchored s T₀} (ha : a ∈ Universe s T₀) : (reading s T₀ a).Valid s := by
  obtain ⟨b, -, h1, h2, h3, hb⟩ := ha
  induction hb with
  | refl =>
    show b.1.2.Valid s
    rw [h1]
    exact ⟨hT, h2, h3, trivial⟩
  | tail _ hc ih =>
    obtain ⟨hne, d, e, -, hy⟩ := hc
    exact occChild.valid ih ⟨hne, d, e, hy⟩

/-- **Completeness relative to the declared universe, at the absolute level** (universe form).
For an irreducible root `T₀`: every absolute pair that has an irreducible noncoincident reading
containing both positions is the absolute pair of an element of the universe whose reading has
the same block and local positions (above level `0` its birth record is the block of the
reading of the element of the universe over its absolute parent, `universe_birth`); that
element is unique (`universe_reading_unique`).  Induction on the level with
`exists_absStep_parent`, `anchor_parent_inside` and `anchor_unique`; the parent block is
noncoincident because the children of a coincidence block are coincidence blocks
(`child_coincident`).  The noncoincidence hypothesis `hnc` cannot be dropped: at a coincidence
block the universe holds only the retained children of noncoincident pairs
(`anchored_cover_needs_hnc`). -/
theorem anchored_cover_universe {s : α → List α} {T₀ : List α × List α} (hT : IsBlock T₀)
    {x : AbsOcc} {y : Occ α} {off : ℕ} (ha : Anchor s T₀ x y off) (hy : IsBlock y.block)
    (hnc : y.block.1 ≠ y.block.2) (hP : y.top < y.block.1.length)
    (hQ : y.bot < y.block.2.length) :
    ∃ (y' : Occ α) (h' : ∃ off', Anchor s T₀ x y' off'), y'.block = y.block ∧
      y'.top = y.top ∧ y'.bot = y.bot ∧ (⟨(x, y'), h'⟩ : Anchored s T₀) ∈ Universe s T₀ := by
  suffices H : ∀ (n : ℕ) (x : AbsOcc) (y : Occ α) (off : ℕ), x.level = n →
      Anchor s T₀ x y off → IsBlock y.block → y.block.1 ≠ y.block.2 →
      y.top < y.block.1.length → y.bot < y.block.2.length →
      ∃ (y' : Occ α) (h' : ∃ off', Anchor s T₀ x y' off'), y'.block = y.block ∧
        y'.top = y.top ∧ y'.bot = y.bot ∧ (⟨(x, y'), h'⟩ : Anchored s T₀) ∈ Universe s T₀ from
    H _ x y off rfl ha hy hnc hP hQ
  intro n
  induction n with
  | zero =>
    intro x y off hl ha hy _ hP hQ
    rcases x with ⟨l, P, Q⟩
    simp only at hl
    subst hl
    obtain ⟨hlt, hlb⟩ := ha.letters hP hQ
    have hP0 : P < T₀.1.length := by
      have : ((subst s)^[0] T₀.1)[P]?.isSome := by
        rw [hlt, List.getElem?_eq_getElem hP]
        rfl
      simpa using this
    have hQ0 : Q < T₀.2.length := by
      have : ((subst s)^[0] T₀.2)[Q]?.isSome := by
        rw [hlb, List.getElem?_eq_getElem hQ]
        rfl
      simpa using this
    have hr := anchor_root s hT.2.1 P Q
    obtain ⟨-, hb, ht, hq⟩ := anchor_unique ha hr hy hT hP hP0
    exact ⟨⟨T₀, P, Q, none⟩, ⟨0, hr⟩, hb.symm, ht.symm, hq.symm,
      rootAnchored_mem s hT.2.1 hP0 hQ0⟩
  | succ n ih =>
    intro x y off hl ha hy hnc hP hQ
    obtain ⟨hlt, hlb⟩ := ha.letters hP hQ
    have hPx : x.top < ((subst s)^[x.level] T₀.1).length := by
      have : ((subst s)^[x.level] T₀.1)[x.top]?.isSome := by
        rw [hlt, List.getElem?_eq_getElem hP]
        rfl
      simpa using this
    have hQx : x.bot < ((subst s)^[x.level] T₀.2).length := by
      have : ((subst s)^[x.level] T₀.2)[x.bot]?.isSome := by
        rw [hlb, List.getElem?_eq_getElem hQ]
        rfl
      simpa using this
    obtain ⟨xp, d, e, hlp, hx⟩ := exists_absStep_parent hl hPx hQx
    obtain ⟨yp, offp, k, hBp, hap, hPp, hQp, -, hstep⟩ :=
      anchor_parent_inside hT.2.1 hx hy hP hQ ha
    have hncp : yp.block.1 ≠ yp.block.2 := by
      intro hc
      obtain ⟨-, -, k', hk', -, -, -, -, -, -, heq⟩ := occStep_child_iff.1 hstep
      have hmem : Child s yp.block y.block := by
        have := congrArg Occ.block heq
        simp only at this
        rw [Child, this]
        exact List.getElem_mem hk'
      exact hnc (child_coincident hc hmem)
    obtain ⟨yp', hp', hbl, htp, hbt, hmemU⟩ := ih xp yp offp hlp hap hBp hncp hPp hQp
    have h'' : ∃ off', Anchor s T₀ x ⟨y.block, y.top, y.bot, some ⟨yp.block, k⟩⟩ off' :=
      ⟨off, ha.congr rfl rfl rfl⟩
    have hedge : (anchoredGraph s T₀).child ⟨(xp, yp'), hp'⟩
        ⟨(x, ⟨y.block, y.top, y.bot, some ⟨yp.block, k⟩⟩), h''⟩ :=
      ⟨by rw [hbl]; exact hncp, d, e, hx, by rw [occStep_congr hbl htp hbt]; exact hstep⟩
    exact ⟨_, h'', rfl, rfl, rfl, universe_closed s T₀ hmemU hedge⟩

/-- **Completeness relative to the declared universe, at the absolute level** (the weaker
reachability form): for an irreducible root, an absolute pair inside one noncoincident
irreducible block of the iterates is reached from level `0`, from a reading with no birth
record, by retained edges; its reading along that path has the same block and local positions
and carries the literal birth record.  `anchored_cover_universe` is the stronger form (the
source is a root reading of `T₀`).  `hnc` cannot be dropped (`anchored_cover_needs_hnc`). -/
theorem anchored_cover {s : α → List α} {T₀ : List α × List α} (hT : IsBlock T₀)
    {x : AbsOcc} {y : Occ α} {off : ℕ} (ha : Anchor s T₀ x y off) (hy : IsBlock y.block)
    (hnc : y.block.1 ≠ y.block.2) (hP : y.top < y.block.1.length)
    (hQ : y.bot < y.block.2.length) :
    ∃ (y' : Occ α) (a₀ : Anchored s T₀), y'.block = y.block ∧ y'.top = y.top ∧
      y'.bot = y.bot ∧ a₀.1.1.level = 0 ∧ a₀.1.2.birth = none ∧
      ∃ h' : ∃ off', Anchor s T₀ x y' off',
        (anchoredGraph s T₀).Reach a₀ ⟨(x, y'), h'⟩ := by
  obtain ⟨y', h', hb, ht, hq, b, h0, h1, -, -, hreach⟩ :=
    anchored_cover_universe hT ha hy hnc hP hQ
  exact ⟨y', b, hb, ht, hq, h0, by rw [h1], h', hreach⟩

/-- **The universe, read at the reduction of the iterates.**  For an irreducible root `T₀`,
every absolute pair whose two positions lie in one noncoincident block of
`red (σⁿ T₀.1) (σⁿ T₀.2)` is the absolute pair of an element of the universe, read at that
block (`anchor_of_red`, `anchored_cover_universe`); that element is unique
(`universe_reading_unique`).  Conversely the reading of every element of the universe is a
block of that reduction (`universe_block_mem_red`).  At a coincidence block of that reduction
the statement fails (`fib_lvl2_not_universe`). -/
theorem anchored_cover_red {s : α → List α} {T₀ : List α × List α} (hT : IsBlock T₀)
    {x : AbsOcc} {j : ℕ}
    (hj : j < (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)).length)
    (h1 : blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j ≤ x.top)
    (h2 : x.top < blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j +
      (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].1.length)
    (h3 : blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j ≤ x.bot)
    (h4 : x.bot < blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j +
      (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].1.length)
    (hnc : (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].1 ≠
      (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j].2) :
    ∃ a ∈ Universe s T₀, a.1.1 = x ∧
      (reading s T₀ a).block = (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2))[j] ∧
      (reading s T₀ a).top =
        x.top - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j ∧
      (reading s T₀ a).bot =
        x.bot - blockStart (red ((subst s)^[x.level] T₀.1) ((subst s)^[x.level] T₀.2)) j := by
  obtain ⟨ha, hB, hP, hQ⟩ := anchor_of_red hT.2.1 hj h1 h2 h3 h4 none
  obtain ⟨y', h', hb, ht, hq, hU⟩ := anchored_cover_universe hT ha hB hnc hP hQ
  exact ⟨_, hU, rfl, hb, ht, hq⟩

/-- For an irreducible root, the block of every reading in the universe is a block of the
reduction of the iterates at its level. -/
theorem universe_block_mem_red {s : α → List α} {T₀ : List α × List α} (hT : IsBlock T₀)
    {a : Anchored s T₀} (ha : a ∈ Universe s T₀) :
    (reading s T₀ a).block ∈ red ((subst s)^[a.1.1.level] T₀.1) ((subst s)^[a.1.1.level] T₀.2) :=
  let ⟨_, h⟩ := a.2
  h.mem_red hT.2.1 (universe_valid hT ha).1

/-- **The actual edges out of the universe.**  For an irreducible root, every absolute child of
an element `a` of the universe whose block is noncoincident is either the absolute pair of a
retained child of `a` (an element of the universe), or separated, and then no absolute
descendant of it, along any digits at any depth, has an irreducible reading containing both
positions.  (Out of a coincidence block no edge is retained, by definition of
`anchoredGraph`.) -/
theorem universe_absStep {s : α → List α} {T₀ : List α × List α} (hT : IsBlock T₀)
    {a : Anchored s T₀} (ha : a ∈ Universe s T₀)
    (hnc : (reading s T₀ a).block.1 ≠ (reading s T₀ a).block.2) {d e : ℕ} {x' : AbsOcc}
    (hx : absStep s T₀ a.1.1 d e = some x') :
    (∃ b ∈ Universe s T₀, b.1.1 = x' ∧ (anchoredGraph s T₀).child a b) ∨
      (Separated s T₀ x' ∧ ∀ (ds : ℕ → ℕ × ℕ) (n : ℕ) {z : AbsOcc},
        absLineage s T₀ x' ds n = some z →
        ¬ ∃ (y' : Occ α) (off' : ℕ), IsBlock y'.block ∧ y'.top < y'.block.1.length ∧
          y'.bot < y'.block.2.length ∧ Anchor s T₀ z y' off') := by
  obtain ⟨off, hA⟩ := a.2
  obtain ⟨-, hP, hQ, -⟩ := universe_valid hT ha
  change a.1.2.top < a.1.2.block.1.length at hP
  change a.1.2.bot < a.1.2.block.2.length at hQ
  obtain ⟨hPx, hQx, hd, he, -⟩ := absStep_some hx
  obtain ⟨hlt, hlb⟩ := hA.letters hP hQ
  rw [List.getElem?_eq_getElem hPx, List.getElem?_eq_getElem hP] at hlt
  rw [List.getElem?_eq_getElem hQx, List.getElem?_eq_getElem hQ] at hlb
  have hd' : d < (s a.1.2.block.1[a.1.2.top]).length := Option.some.inj hlt ▸ hd
  have he' : e < (s a.1.2.block.2[a.1.2.bot]).length := Option.some.inj hlb ▸ he
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (occStep_isSome (s := s) hA.balanced hP hQ hd' he')
  cases o with
  | child y' =>
    obtain ⟨x'', off'', hx'', hA''⟩ := anchor_step hA ho
    rw [hx] at hx''
    obtain rfl := Option.some.inj hx''
    have hedge : (anchoredGraph s T₀).child a ⟨(x', y'), off'', hA''⟩ := ⟨hnc, d, e, hx, ho⟩
    exact Or.inl ⟨_, universe_closed s T₀ ha hedge, rfl, hedge⟩
  | split k k' =>
    obtain ⟨x'', hx'', hsep⟩ := hA.split_separated ho
    rw [hx] at hx''
    obtain rfl := Option.some.inj hx''
    refine Or.inr ⟨hsep, fun ds n z hz => ?_⟩
    rintro ⟨y', off', hB, hP', hQ', ha'⟩
    exact (hsep.lineage ds n hz).not_anchor ha' hB hP' hQ'

/-- **What the universe reads as.**  For a balanced root, the readings of the universe are
exactly the literal occurrence pairs reachable in `occGraph s` from the root pairs
`⟨T₀, P, Q, none⟩`: `⊆` by completeness of the reading along the reaching path, `⊇` by soundness
from every source (`SoundEvery.reach_lift`) from the root reading. -/
theorem reading_image_universe {s : α → List α} {T₀ : List α × List α} (hT : Equiv1 T₀.1 T₀.2) :
    reading s T₀ '' Universe s T₀ = {y | ∃ P Q, P < T₀.1.length ∧ Q < T₀.2.length ∧
      (occGraph s).Reach ⟨T₀, P, Q, none⟩ y} := by
  ext y
  constructor
  · rintro ⟨a, ⟨b, -, h1, h2, h3, hb⟩, rfl⟩
    refine ⟨_, _, h2, h3, ?_⟩
    have := (reading_complete s T₀).reach hb
    rwa [show reading s T₀ b = _ from h1] at this
  · rintro ⟨P, Q, hP, hQ, hreach⟩
    obtain ⟨a, ha, rfl⟩ := (reading_soundEvery s T₀).reach_lift
      (x := rootAnchored s hT P Q) hreach
    obtain ⟨b, h0, h1, h2, h3, hb⟩ := rootAnchored_mem s hT hP hQ
    exact ⟨a, ⟨b, h0, h1, h2, h3, hb.trans ha⟩, rfl⟩

/-- **The universe is covered by every child-closed set of literal occurrence pairs that holds
the root pairs**: the generic step of `universe_covered` (stated in the packet-square module,
not here), with the set of decoded packet rows in place of `S`. -/
theorem universe_reading_mem_of_closed {s : α → List α} {T₀ : List α × List α}
    {S : Set (Occ α)} (hroot : ∀ P Q, P < T₀.1.length → Q < T₀.2.length → ⟨T₀, P, Q, none⟩ ∈ S)
    (hS : (occGraph s).Closed S) {a : Anchored s T₀} (ha : a ∈ Universe s T₀) :
    reading s T₀ a ∈ S := by
  obtain ⟨b, -, h1, h2, h3, hb⟩ := ha
  induction hb with
  | refl =>
    show b.1.2 ∈ S
    rw [h1]
    exact hroot _ _ h2 h3
  | tail _ hc ih => exact hS ih (reading_complete s T₀ hc)

/-! ### Frame change at the absolute level -/

/-- Side swap of an absolute pair. -/
def AbsOcc.swap (x : AbsOcc) : AbsOcc := ⟨x.level, x.bot, x.top⟩

/-- The side swap of an absolute pair is an involution. -/
theorem AbsOcc.swap_swap (x : AbsOcc) : x.swap.swap = x := rfl

/-- Swapping the root swaps both positions and the reading. -/
theorem Anchor.swap {s : α → List α} {T₀ : List α × List α} {x : AbsOcc} {y : Occ α} {off : ℕ}
    (ha : Anchor s T₀ x y off) : Anchor s T₀.swap x.swap y.swap off where
  balanced := fun c => (ha.balanced c).symm
  zero := fun c => (ha.zero c).symm
  top_factor := ha.bot_factor
  bot_factor := ha.top_factor
  top_pos := ha.bot_pos
  bot_pos := ha.top_pos

omit [DecidableEq α] in
/-- **Orientation equivariance of the absolute step**: in the frame of `T₀.swap`, the swapped
pair steps along the swapped digits to the swapped child. -/
theorem absStep_swap (s : α → List α) (T₀ : List α × List α) (x : AbsOcc) (d e : ℕ) :
    absStep s T₀.swap x.swap e d = (absStep s T₀ x d e).map AbsOcc.swap := by
  rcases x with ⟨n, P, Q⟩
  simp only [absStep, AbsOcc.swap, Prod.fst_swap, Prod.snd_swap]
  cases ((subst s)^[n] T₀.1)[P]? with
  | none => cases ((subst s)^[n] T₀.2)[Q]? <;> rfl
  | some a =>
    cases ((subst s)^[n] T₀.2)[Q]? with
    | none => rfl
    | some b =>
      simp only
      by_cases hde : d < (s a).length ∧ e < (s b).length
      · rw [ite_eq_left ⟨hde.2, hde.1⟩, ite_eq_left hde]
        rfl
      · rw [ite_eq_right (fun h => hde ⟨h.2, h.1⟩), ite_eq_right hde]
        rfl

/-- Side swap of an anchored pair: an anchored pair of the frame `T₀.swap`. -/
def Anchored.swap {s : α → List α} {T₀ : List α × List α} (a : Anchored s T₀) :
    Anchored s T₀.swap :=
  ⟨(a.1.1.swap, a.1.2.swap), let ⟨off, h⟩ := a.2; ⟨off, h.swap⟩⟩

/-- The reading of a swapped anchored pair is the swapped reading (definitional). -/
theorem reading_swap {s : α → List α} {T₀ : List α × List α} (a : Anchored s T₀) :
    reading s T₀.swap a.swap = (reading s T₀ a).swap := rfl

/-- A retained edge, swapped, is a retained edge of the swapped frame. -/
theorem anchoredGraph_child_swap {s : α → List α} {T₀ : List α × List α} {a b : Anchored s T₀}
    (h : (anchoredGraph s T₀).child a b) : (anchoredGraph s T₀.swap).child a.swap b.swap := by
  obtain ⟨hne, d, e, hx, hy⟩ := h
  obtain ⟨off, ha⟩ := a.2
  refine ⟨fun h' => hne h'.symm, e, d, ?_, ?_⟩
  · show absStep s T₀.swap a.1.1.swap e d = some b.1.1.swap
    rw [absStep_swap, hx]
    rfl
  · show occStep s a.1.2.swap e d = some (.child b.1.2.swap)
    rw [occStep_swap ha.balanced, hy]
    rfl

/-- **Frame change of the universe**: the swap of an element of the universe of `T₀` is an
element of the universe of `T₀.swap` (so a lineage in the frame of a normalised seed is, with
top and bottom exchanged, a lineage in the frame of the mirrored seed). -/
theorem universe_swap {s : α → List α} {T₀ : List α × List α} {a : Anchored s T₀}
    (ha : a ∈ Universe s T₀) : a.swap ∈ Universe s T₀.swap := by
  obtain ⟨b, h0, h1, h2, h3, hb⟩ := ha
  refine ⟨b.swap, h0, ?_, h3, h2, ?_⟩
  · show b.1.2.swap = _
    rw [h1]
    rfl
  · induction hb with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail (anchoredGraph_child_swap h)

/-- **Frame change of the universe, both directions**: an anchored pair of the frame `T₀.swap`
is in its universe exactly when its swap (an anchored pair of the frame `T₀`, by `Prod` eta) is
in the universe of `T₀`. -/
theorem universe_swap_iff {s : α → List α} {T₀ : List α × List α} (a : Anchored s T₀.swap) :
    a.swap ∈ Universe s T₀ ↔ a ∈ Universe s T₀.swap := by
  constructor
  · intro h
    have h2 := universe_swap h
    have e : a.swap.swap = a := Subtype.ext (Prod.ext rfl (Occ.swap_swap _))
    rwa [e] at h2
  · exact universe_swap

/-! ### The block projection β -/

/-- **Completeness of the block projection** onto the balanced-pair automaton. -/
theorem block_complete (s : α → List α) : Complete (occGraph s) (bpaGraph s) Occ.block :=
  fun _ _ h => h.childNC

/-- The block projection preserves and reflects targets (both are the coincidence blocks). -/
theorem block_targets (s : α → List α) :
    TargetDown (occGraph s) (bpaGraph s) Occ.block ∧
      TargetUp (occGraph s) (bpaGraph s) Occ.block :=
  ⟨fun _ h => h, fun _ h => h⟩

/-- (E) projects along the block projection: a productive occurrence pair has a productive
block.  The converse fails (`fib_block_readings`). -/
theorem block_productive (s : α → List α) {x : Occ α} (h : (occGraph s).Productive x) :
    (bpaGraph s).Productive x.block :=
  (block_complete s).productive (block_targets s).1 h

/-- (A) pulls back along the block projection: an occurrence pair over an inevitable block is
inevitable.  The converse fails (`fib_block_readings`). -/
theorem block_inevitable (s : α → List α) {x : Occ α} (h : (bpaGraph s).Inevitable x.block) :
    (occGraph s).Inevitable x :=
  (block_complete s).inevitable (block_targets s).2 h

/-- **Soundness from some source** of the block projection, from irreducible sources: every
child edge `T → U` of the balanced-pair automaton out of an irreducible `T` is realised by the
root occurrence pair of `T` at the `cutAddr` addresses of the start of `U`, and the child is
`U` read at its start. -/
theorem block_soundSome_at {s : α → List α} {T U : List α × List α} (hT : IsBlock T)
    (hTU : ChildNC s T U) :
    ∃ x y : Occ α, x.block = T ∧ x.birth = none ∧ x.Valid s ∧ y.block = U ∧ y.AtStart ∧
      occChild s x y := by
  obtain ⟨hne, hmem⟩ := hTU
  have hE : Equiv1 (subst s T.1) (subst s T.2) := equiv1_subst s hT.2.1
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
  have hB : IsBlock (red (subst s T.1) (subst s T.2))[k] := red_isBlock hE _ (List.getElem_mem hk)
  have hpos : 0 < (red (subst s T.1) (subst s T.2))[k].1.length := List.length_pos_iff.2 hB.1
  have hend := blockStart_add_le hE.length_eq hk
  have hg1 : blockStart (red (subst s T.1) (subst s T.2)) k < (subst s T.1).length := by omega
  have hg2 : blockStart (red (subst s T.1) (subst s T.2)) k < (subst s T.2).length := by
    rw [← hE.length_eq]
    omega
  obtain ⟨i, hi, d, hd, hgi⟩ := exists_imgStart_add s T.1 hg1
  obtain ⟨j, hj, e, he, hgj⟩ := exists_imgStart_add s T.2 hg2
  refine ⟨⟨T, i, j, none⟩, ⟨(red (subst s T.1) (subst s T.2))[k], 0, 0, some ⟨T, k⟩⟩, rfl, rfl,
    ⟨hT, hi, hj, trivial⟩, rfl, ⟨rfl, rfl⟩, hne, d, e, ?_⟩
  rw [occStep_child_iff]
  dsimp only
  refine ⟨hi, hj, k, hk, hd, he, by omega, by omega, by omega, by omega, ?_⟩
  simp only [← hgi, ← hgj, Nat.sub_self]

/-- The Fibonacci occurrence pair `fibDead` (positions `(1, 0)` of the root `(01, 10)`) has no
literal child. -/
theorem fibDead_no_child (y : Occ (Fin 2)) : ¬ occChild fibSubst fibDead y := fun h => by
  have := mem_occChildren.2 h
  rw [fibDead_children] at this
  simp at this

/-- **The literal β-control** (Fibonacci `0 ↦ 01, 1 ↦ 0`, binary; inside the standing PIP class
as `Psc.QuantifierBinding.fib_lasso` records, outside the three-letter census corpus).  The
occurrence pair `fibDead` is valid; (AE) holds at its block `(01, 10)` in the balanced-pair
automaton while (E) fails at `fibDead`; (A) holds at `fibDead` (vacuously: it has no child, so
no infinite path leaves it) while (A) fails at its block; and the block projection is not sound
from every source. -/
theorem fib_block_readings :
    fibDead.Valid fibSubst ∧
      (bpaGraph fibSubst).HereditarilyProductive fibDead.block ∧
      ¬ (occGraph fibSubst).Productive fibDead ∧
      (occGraph fibSubst).Inevitable fibDead ∧ ¬ (bpaGraph fibSubst).Inevitable fibDead.block ∧
      ¬ SoundEvery (occGraph fibSubst) (bpaGraph fibSubst) Occ.block := by
  refine ⟨fibDead_valid, fib_lasso.2.1, ?_, ?_, fib_lasso.2.2.2, ?_⟩
  · rintro ⟨t, ht, htg⟩
    rcases Relation.ReflTransGen.cases_head ht with rfl | ⟨c, hc, -⟩
    · exact absurd htg (by decide : ¬ fibDead.Coincident)
    · exact fibDead_no_child c hc
  · intro p hp0 hp
    exact absurd (hp0 ▸ hp 0) (fibDead_no_child _)
  · intro hS
    obtain ⟨x', hx', -⟩ := hS fibDead (y' := ([0], [0])) fibDead_block_child
    exact fibDead_no_child x' hx'

/-! ### Calibration: the archived 2-cycle of `1/02/202` read off one absolute lineage

`rsSubst`, `rsState7`, `rsState8`, `x209`, `x429` and `rs_rows_edges` are those of
`Psc.OccurrenceGraph`.  The root is the seed `(01, 10)`. -/

/-- The seed `(01, 10)` of `1/02/202`. -/
def rsSeed : List (Fin 3) × List (Fin 3) := ([0, 1], [1, 0])

/-- The level-1 block `(102, 021)` of `σ(01, 10)`. -/
def rsState1 : List (Fin 3) × List (Fin 3) := ([1, 0, 2], [0, 2, 1])

/-- The reading at level `1` of the lineage below. -/
def rsY1 : Occ (Fin 3) := ⟨rsState1, 1, 1, some ⟨rsSeed, 0⟩⟩

/-- The reading at level `2` of the lineage below: archived state 7 at positions `(2, 1)` (the
positions of packet 429), born as the first child of `rsState1`. -/
def rsY2 : Occ (Fin 3) := ⟨rsState7, 2, 1, some ⟨rsState1, 0⟩⟩

/-- **The absolute lineage of the archived cycle** (its edge `(3,4,4) → (4,9,8)` was located by
hand): the absolute pairs
`(0,1,0) -(0,1)-> (1,1,1) -(0,0)-> (2,2,1) -(0,2)-> (3,4,4) -(0,0)-> (4,9,8) -(0,2)-> (5,20,20)`
of `σⁿ(01), σⁿ(10)`, by `absStep`, and the literal steps of their readings. -/
theorem rs_lineage_steps :
    absStep rsSubst rsSeed ⟨0, 1, 0⟩ 0 1 = some ⟨1, 1, 1⟩ ∧
      absStep rsSubst rsSeed ⟨1, 1, 1⟩ 0 0 = some ⟨2, 2, 1⟩ ∧
      absStep rsSubst rsSeed ⟨2, 2, 1⟩ 0 2 = some ⟨3, 4, 4⟩ ∧
      absStep rsSubst rsSeed ⟨3, 4, 4⟩ 0 0 = some ⟨4, 9, 8⟩ ∧
      absStep rsSubst rsSeed ⟨4, 9, 8⟩ 0 2 = some ⟨5, 20, 20⟩ ∧
      occStep rsSubst ⟨rsSeed, 1, 0, none⟩ 0 1 = some (.child rsY1) ∧
      occStep rsSubst rsY1 0 0 = some (.child rsY2) ∧
      occStep rsSubst rsY2 0 2 = some (.child x209) := by
  decide

/-- The seed `(01, 10)` is an irreducible block. -/
theorem rs_seed_isBlock : IsBlock rsSeed := by decide

/-- `rsY1` reads `(1, 1, 1)`: `σ(01, 10) = (102, 021)` is one block. -/
theorem rs_anchor1 : Anchor rsSubst rsSeed ⟨1, 1, 1⟩ rsY1 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `rsY2` reads `(2, 2, 1)`: the first block of `red (σ² 01) (σ² 10)` is `rsState7`. -/
theorem rs_anchor2 : Anchor rsSubst rsSeed ⟨2, 2, 1⟩ rsY2 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Packet 209 is the reading of `(3, 4, 4)`: the first block of `red (σ³ 01) (σ³ 10)` is
`rsState8.swap`. -/
theorem rs_anchor209 : Anchor rsSubst rsSeed ⟨3, 4, 4⟩ x209 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Packet 429 is the reading of `(4, 9, 8)`, at the third block (offset `7`) of
`red (σ⁴ 01) (σ⁴ 10)`. -/
theorem rs_anchor429 : Anchor rsSubst rsSeed ⟨4, 9, 8⟩ x429 7 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Packet 209 again, as the reading of `(5, 20, 20)`, at offset `16`. -/
theorem rs_anchor209' : Anchor rsSubst rsSeed ⟨5, 20, 20⟩ x209 16 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The anchored pair of the lineage at level `1`: `(1, 1, 1)` read as `rsY1`. -/
def rsA1 : Anchored rsSubst rsSeed := ⟨(⟨1, 1, 1⟩, rsY1), 0, rs_anchor1⟩
/-- The anchored pair of the lineage at level `2`: `(2, 2, 1)` read as `rsY2`. -/
def rsA2 : Anchored rsSubst rsSeed := ⟨(⟨2, 2, 1⟩, rsY2), 0, rs_anchor2⟩
/-- The anchored pair of the lineage at level `3`: `(3, 4, 4)` read as packet 209. -/
def rsA3 : Anchored rsSubst rsSeed := ⟨(⟨3, 4, 4⟩, x209), 0, rs_anchor209⟩
/-- The anchored pair of the lineage at level `4`: `(4, 9, 8)` read as packet 429. -/
def rsA4 : Anchored rsSubst rsSeed := ⟨(⟨4, 9, 8⟩, x429), 7, rs_anchor429⟩
/-- The anchored pair of the lineage at level `5`: `(5, 20, 20)` read as packet 209. -/
def rsA5 : Anchored rsSubst rsSeed := ⟨(⟨5, 20, 20⟩, x209), 16, rs_anchor209'⟩

/-- **Positive control for ρ.**  The archived packet cycle `209 -(0,0)-> 429 -(0,2)-> 209` is
read off the retained absolute lineage `(3,4,4) → (4,9,8) → (5,20,20)` of the seed `(01, 10)`,
which lies in the declared universe (reached from the root reading at positions `(1, 0)`);
every element of the universe over `(3,4,4)` reads as packet 209 and every element over
`(4,9,8)` as packet 429 (`universe_reading_unique`); the two readings of 209 sit at different
levels, and no actual cycle exists (`anchored_no_cycle`). -/
theorem rs_cycle_lineage :
    rsA3 ∈ Universe rsSubst rsSeed ∧ rsA4 ∈ Universe rsSubst rsSeed ∧
      rsA5 ∈ Universe rsSubst rsSeed ∧
      (anchoredGraph rsSubst rsSeed).child rsA3 rsA4 ∧
      (anchoredGraph rsSubst rsSeed).child rsA4 rsA5 ∧
      reading rsSubst rsSeed rsA3 = x209 ∧ reading rsSubst rsSeed rsA4 = x429 ∧
      reading rsSubst rsSeed rsA5 = x209 ∧ rsA3 ≠ rsA5 ∧
      (∀ a ∈ Universe rsSubst rsSeed, a.1.1 = ⟨3, 4, 4⟩ → reading rsSubst rsSeed a = x209) ∧
      (∀ a ∈ Universe rsSubst rsSeed, a.1.1 = ⟨4, 9, 8⟩ → reading rsSubst rsSeed a = x429) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := rs_lineage_steps
  have e1 : (anchoredGraph rsSubst rsSeed).child (rootAnchored rsSubst rs_seed_isBlock.2.1 1 0)
      rsA1 := ⟨by decide, 0, 1, h1, h6⟩
  have e2 : (anchoredGraph rsSubst rsSeed).child rsA1 rsA2 := ⟨by decide, 0, 0, h2, h7⟩
  have e3 : (anchoredGraph rsSubst rsSeed).child rsA2 rsA3 := ⟨by decide, 0, 2, h3, h8⟩
  have e4 : (anchoredGraph rsSubst rsSeed).child rsA3 rsA4 :=
    ⟨by decide, 0, 0, h4, rs_rows_edges.1⟩
  have e5 : (anchoredGraph rsSubst rsSeed).child rsA4 rsA5 :=
    ⟨by decide, 0, 2, h5, rs_rows_edges.2⟩
  have hU0 := rootAnchored_mem rsSubst rs_seed_isBlock.2.1 (P := 1) (Q := 0) (by decide)
    (by decide)
  have hU3 : rsA3 ∈ Universe rsSubst rsSeed :=
    universe_closed _ _ (universe_closed _ _ (universe_closed _ _ hU0 e1) e2) e3
  have hU4 : rsA4 ∈ Universe rsSubst rsSeed := universe_closed _ _ hU3 e4
  refine ⟨hU3, hU4, universe_closed _ _ hU4 e5, e4, e5, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun a : Anchored rsSubst rsSeed => a.1.1.level) h
    simp [rsA3, rsA5] at this
  · intro a ha hx
    rw [universe_reading_unique ha hU3 hx]
    rfl
  · intro a ha hx
    rw [universe_reading_unique ha hU4 hx]
    rfl

/-- The digit sequence of the archived cycle, `(0,0), (0,2), (0,0), …`. -/
def rsCycleDigits (n : ℕ) : ℕ × ℕ := if n % 2 = 0 then (0, 0) else (0, 2)

/-- The readings along the archived cycle, `209, 429, 209, …`. -/
def rsCycleReading (n : ℕ) : Occ (Fin 3) := if n % 2 = 0 then x209 else x429

/-- **The packet cycle lifts to an infinite absolute lineage, choice-free**: along the digits
of the cycle, the absolute lineage of `(3, 4, 4)` exists at every depth `n`, at level `3 + n`,
and reads as `209, 429, 209, …` (an instance of `absLineage_anchor`). -/
theorem rs_infinite_lineage (n : ℕ) :
    ∃ z off, absLineage rsSubst rsSeed ⟨3, 4, 4⟩ rsCycleDigits n = some z ∧ z.level = 3 + n ∧
      Anchor rsSubst rsSeed z (rsCycleReading n) off := by
  refine absLineage_anchor rsCycleReading rsCycleDigits rs_anchor209 ?_ n
  intro m
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h' : (m + 1) % 2 = 1 := by omega
    simp only [rsCycleReading, rsCycleDigits, h, h', ite_true]
    exact rs_rows_edges.1
  · have h' : (m + 1) % 2 = 0 := by omega
    simp only [rsCycleReading, rsCycleDigits, h, h']
    exact rs_rows_edges.2

/-! ### Negative control: the noncoincidence hypothesis of `anchored_cover` cannot be dropped

Fibonacci `0 ↦ 01, 1 ↦ 0` (`fibSubst`), root `(01, 10)` (`tmPair`).  The iterates at level `2`
are `01001`, `01010`, and the first block of their reduction is the irreducible coincidence
block `(0, 0)` at offset `0`, which holds the absolute pair `(2, 0, 0)`.  Its only absolute
parent is `(1, 0, 0)`, whose element of the universe reads as the coincidence block `(0, 0)`
of `σ(01, 10) = (010, 001)`; out of a coincidence block no edge is retained, so no element of
the universe lies over `(2, 0, 0)`. -/

/-- `(2, 0, 0)` is read by the coincidence block `(0, 0)` at offset `0`. -/
theorem fib_lvl2_anchor : Anchor fibSubst tmPair ⟨2, 0, 0⟩ ⟨([0], [0]), 0, 0, none⟩ 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The coincidence block `(0, 0)` is irreducible. -/
theorem fib_lvl2_block : IsBlock (([0], [0]) : List (Fin 2) × List (Fin 2)) := by decide

/-- The coincidence block `(0, 0)` is a block of the reduction of the level-`2` iterates. -/
theorem fib_lvl2_red : (([0], [0]) : List (Fin 2) × List (Fin 2)) ∈
    red ((subst fibSubst)^[2] tmPair.1) ((subst fibSubst)^[2] tmPair.2) := by decide

/-- The Fibonacci root `(01, 10)` is an irreducible block. -/
theorem fib_root_isBlock : IsBlock tmPair := by decide

/-- The element of the universe over `(1, 0, 0)`: the coincidence block `(0, 0)`, born as the
first child of the root. -/
def fibC1 : Anchored fibSubst tmPair :=
  ⟨(⟨1, 0, 0⟩, ⟨([0], [0]), 0, 0, some ⟨tmPair, 0⟩⟩), 0,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

/-- **No element of the universe lies over `(2, 0, 0)`.** -/
theorem fib_lvl2_not_universe (a : Anchored fibSubst tmPair) (hx : a.1.1 = ⟨2, 0, 0⟩) :
    a ∉ Universe fibSubst tmPair := by
  intro ha
  obtain ⟨c, hc, hne, d, e, hstep, -⟩ := universe_succ ha (n := 1) (by rw [hx])
  have h0 : absStep fibSubst tmPair ⟨1, 0, 0⟩ 0 0 = some ⟨2, 0, 0⟩ := by decide
  rw [hx] at hstep
  obtain ⟨hcx, -, -⟩ := absStep_inj hstep h0
  have hroot := rootAnchored_mem fibSubst fib_root_isBlock.2.1 (P := 0) (Q := 0) (by decide)
    (by decide)
  have e1 : (anchoredGraph fibSubst tmPair).child
      (rootAnchored fibSubst fib_root_isBlock.2.1 0 0) fibC1 :=
    ⟨by decide, 0, 0, by decide, by decide⟩
  have hc1 := universe_closed _ _ hroot e1
  obtain rfl := universe_reading_unique hc hc1 hcx
  exact hne rfl

/-- **`anchored_cover` without its noncoincidence hypothesis is false**: for Fibonacci and the
root `(01, 10)`, the absolute pair `(2, 0, 0)` has an irreducible reading containing both
positions (by a coincidence block of the reduction of the iterates, `fib_lvl2_red`), and no
reading of it is in the universe. -/
theorem anchored_cover_needs_hnc : ¬ ∀ (x : AbsOcc) (y : Occ (Fin 2)) (off : ℕ),
    Anchor fibSubst tmPair x y off → IsBlock y.block → y.top < y.block.1.length →
    y.bot < y.block.2.length →
    ∃ (y' : Occ (Fin 2)) (h' : ∃ off', Anchor fibSubst tmPair x y' off'),
      (⟨(x, y'), h'⟩ : Anchored fibSubst tmPair) ∈ Universe fibSubst tmPair := by
  intro H
  obtain ⟨y', h', hU⟩ := H _ _ _ fib_lvl2_anchor fib_lvl2_block (by decide) (by decide)
  exact fib_lvl2_not_universe _ rfl hU

end Psc.OccurrenceRealisation
