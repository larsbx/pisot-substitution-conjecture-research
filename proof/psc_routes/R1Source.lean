import Mathlib
import Lean.Util.CollectAxioms

/-!
# R1 source-prefix bridge: genuine, literal one-step cuts.

No balanced-pair state or strictness is assumed. The module proves that a
source-addressed prefix in an actually substituted word decomposes into
a full substituted source prefix and a *proper within-letter prefix*.

This is stronger than an arbitrary affine digit word, but not a theorem
that a periodic correction sequence is realizable as a strict SCC.
-/

namespace PscRoutes.R1Source

variable {A V : Type*} [AddCommGroup V]

/-- The actual prefix ending at within-image offset `r` after
the source word `pre` and the source letter `a`. -/
def cutPrefix (subst : A → List A) (pre : List A) (a : A) (r : ℕ) :
    List A :=
  pre.flatMap subst ++ (subst a).take r

def cutSuffix (subst : A → List A) (post : List A) (a : A) (r : ℕ) :
    List A :=
  (subst a).drop r ++ post.flatMap subst

/-- The cut divides a **literal** substituted source word, with no
rounding, numerical tile lengths, or allowance for invented source
prefix fragments. -/
theorem cutPrefix_append_cutSuffix (subst : A → List A)
    (pre post : List A) (a : A) (r : ℕ) :
    cutPrefix subst pre a r ++ cutSuffix subst post a r =
      (pre ++ a :: post).flatMap subst := by
  simp only [cutPrefix, cutSuffix, List.flatMap_append]
  simp [List.append_assoc, List.take_append_drop]

/-- Our actual cutPrefix is a prefix of the whole inflated word.
This is a structural source-occurrence fact, not just Parikh algebra. -/
theorem cutPrefix_isPrefix (subst : A → List A)
    (pre post : List A) (a : A) (r : ℕ) :
    (cutPrefix subst pre a r).IsPrefix
      ((pre ++ a :: post).flatMap subst) := by
  refine ⟨cutSuffix subst post a r, ?_⟩
  exact (cutPrefix_append_cutSuffix subst pre post a r).symm

/-- Source-word mass, including the Parikh basis specialization. -/
def wordMass (label : A → V) : List A → V
  | [] => 0
  | a :: tail => label a + wordMass label tail

theorem wordMass_append (label : A → V) (u v : List A) :
    wordMass label (u ++ v) =
      wordMass label u + wordMass label v := by
  induction u with
  | nil => simp [wordMass]
  | cons a u ih =>
      simp only [List.cons_append, wordMass, ih]
      abel

/-- Per-letter incidence is the **only** bridge assumption. -/
theorem wordMass_substitution (label : A → V)
    (subst : A → List A) (M : V →+ V)
    (hcols : ∀ a, M (label a) = wordMass label (subst a))
    (u : List A) :
    M (wordMass label u) = wordMass label (u.flatMap subst) := by
  induction u with
  | nil => simp [wordMass]
  | cons a tail ih =>
      change M (label a + wordMass label tail) =
        wordMass label (subst a ++ tail.flatMap subst)
      rw [map_add, hcols a, ih, wordMass_append]

/-- Canonical one-step asynchronous source-cut identity, now with
`local` fragments explicitly set to actual `take` prefixes of the
source images rather than supplied arbitrary lists. -/
theorem actualCut_prefix_mass_transport
    (label : A → V) (subst : A → List A) (M : V →+ V)
    (hcols : ∀ a, M (label a) = wordMass label (subst a))
    (topPre bottomPre : List A) (topLetter bottomLetter : A)
    (topOffset bottomOffset : ℕ) :
    wordMass label (cutPrefix subst topPre topLetter topOffset) -
      wordMass label (cutPrefix subst bottomPre bottomLetter bottomOffset) =
    M (wordMass label topPre - wordMass label bottomPre) +
      (wordMass label ((subst topLetter).take topOffset) -
       wordMass label ((subst bottomLetter).take bottomOffset)) := by
  simp only [cutPrefix, wordMass_append]
  rw [← wordMass_substitution label subst M hcols topPre,
      ← wordMass_substitution label subst M hcols bottomPre]
  rw [map_sub]
  abel


/-- A *literal interior balanced return* is specified by two equal-length
nonempty prefix words of equal Parikh mass, leaving nonempty suffixes
on both tracks. This avoids mistaking an asynchronous common letter
for an aligned coincidence. -/
def HasAlignedInteriorReturn (label : A → V)
    (topWord bottomWord : List A) : Prop :=
  ∃ topPre bottomPre topPost bottomPost : List A,
    topWord = topPre ++ topPost ∧
    bottomWord = bottomPre ++ bottomPost ∧
    topPre.length = bottomPre.length ∧
    0 < topPre.length ∧
    topPost ≠ [] ∧ bottomPost ≠ [] ∧
    wordMass label topPre = wordMass label bottomPre

/-- If the source prefix defect is exactly the mass of the NEXT
bottom letter and the top index is one larger, advancing the bottom
prefix by that letter makes an exact equal-length balanced cut.
A nonempty top suffix and equal parent lengths make it interior
on both tracks. This is a *source-ordered* obstruction that the
coarse affine correction alphabet does not capture. -/
theorem unit_source_defect_forces_aligned_interior_return
    (label : A → V)
    (topPre bottomPre topRest bottomRest : List A)
    (topNext bottomNext : A)
    (hlen : topPre.length = bottomPre.length + 1)
    (hdef : wordMass label topPre - wordMass label bottomPre =
      label bottomNext)
    (hparentLen :
      (topPre ++ topNext :: topRest).length =
      (bottomPre ++ bottomNext :: bottomRest).length) :
    HasAlignedInteriorReturn label
      (topPre ++ topNext :: topRest)
      (bottomPre ++ bottomNext :: bottomRest) := by
  have hbottomRest : bottomRest ≠ [] := by
    intro hempty
    subst bottomRest
    simp only [List.length_append, List.length_cons, List.length_nil] at hparentLen
    omega
  refine ⟨topPre, bottomPre ++ [bottomNext],
    topNext :: topRest, bottomRest, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.append_assoc]
  · simp [List.length_append, hlen]
  · omega
  · simp
  · exact hbottomRest
  · calc
      wordMass label topPre =
          wordMass label topPre - wordMass label bottomPre +
            wordMass label bottomPre := by abel
      _ = label bottomNext + wordMass label bottomPre := by rw [hdef]
      _ = wordMass label (bottomPre ++ [bottomNext]) := by
        rw [wordMass_append]
        simp [wordMass]
        abel

/-- Consequently no irreducible equal-length parent can contain
this source-germ configuration at a *proper* source cut.
This does NOT eliminate its recurrence across multiple irreducible
children at deeper inflated levels, which is the missing PSC bridge. -/
theorem irreducible_parent_excludes_unit_source_germ
    (label : A → V)
    (topPre bottomPre topRest bottomRest : List A)
    (topNext bottomNext : A)
    (hlen : topPre.length = bottomPre.length + 1)
    (hdef : wordMass label topPre - wordMass label bottomPre =
      label bottomNext)
    (hparentLen :
      (topPre ++ topNext :: topRest).length =
      (bottomPre ++ bottomNext :: bottomRest).length)
    (hirred : ¬ HasAlignedInteriorReturn label
      (topPre ++ topNext :: topRest)
      (bottomPre ++ bottomNext :: bottomRest)) : False := by
  exact hirred (unit_source_defect_forces_aligned_interior_return
    label topPre bottomPre topRest bottomRest topNext bottomNext
    hlen hdef hparentLen)


/-! ### Exact source-language calibration for the three-letter control.

These are finite, literal word statements. They do not assert
recognizability or legality for *all* words in a hypothetical strict SCC.
-/
def trImage (a : ℕ) : List ℕ :=
  if a = 0 then [0, 1]
  else if a = 1 then [0, 2]
  else [0]

def trInflate (word : List ℕ) : List ℕ :=
  word.flatMap trImage

def trFourth : List ℕ :=
  trInflate (trInflate (trInflate (trInflate [0])))

/-- Actual fourth Tribonacci image, with no external oracle. -/
theorem tribonacci_fourth_literal :
    trFourth = [0,1,0,2,0,1,0,0,1,0,2,0,1] := by decide

/-- The two contrasting balanced-pair controls have *legal source
word factors* in the same fixed Tribonacci iterate. -/
theorem tribonacci_source_controls_are_legal_factors :
    (∃ pre post : List ℕ,
       trFourth = pre ++ [0,0,1] ++ post) ∧
    (∃ pre post : List ℕ,
       trFourth = pre ++ [0,1,0] ++ post) ∧
    (∃ pre post : List ℕ,
       trFourth = pre ++ [1,0,0] ++ post) := by
  refine ⟨⟨[0,1,0,2,0,1], [0,2,0,1], ?_⟩,
    ⟨[], [2,0,1,0,0,1,0,2,0,1], ?_⟩,
    ⟨[0,1,0,2,0], [1,0,2,0,1], ?_⟩⟩
  all_goals decide

/-- The Parikh basis is the integer indicator for each literal label. -/
def trLabel (a : ℕ) : Fin 3 → ℤ :=
  fun i => if i.val = a then 1 else 0

/-- All three control words have identical Parikh masses.
This is checked symbolically coordinate by coordinate. -/
theorem tribonacci_source_controls_balanced :
    wordMass trLabel [0,0,1] = wordMass trLabel [0,1,0] ∧
    wordMass trLabel [0,0,1] = wordMass trLabel [1,0,0] := by
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [wordMass, trLabel]

/-- The source germ of 001/010 at top index one and bottom index
zero forces an interior balanced return, as the general theorem
predicts; neither a numerical simulation nor a geometric argument
supplies this fact. -/
theorem tribonacci_matching_source_control_has_interior_return :
    HasAlignedInteriorReturn trLabel [0,0,1] [0,1,0] := by
  apply unit_source_defect_forces_aligned_interior_return
    trLabel [0] [] [1] [1,0] 0 0
  · decide
  · simp [wordMass]
  · decide


/-- Standard aligned-prefix irreducibility, expressed directly with
literal `take` operations. Balancedness of the full words is a
separate (already proved) requirement. -/
def NoAlignedInteriorReturn (label : A → V)
    (topWord bottomWord : List A) : Prop :=
  ∀ k, 0 < k → k < topWord.length →
    wordMass label (topWord.take k) ≠
      wordMass label (bottomWord.take k)

/-- The matching-word negative control is *not* irreducible: its
index-one prefixes agree and both word lengths are three. -/
theorem tribonacci_matching_control_is_reducible :
    ¬ NoAlignedInteriorReturn trLabel [0,0,1] [0,1,0] := by
  intro h
  have h1 := h 1 (by decide) (by decide)
  apply h1
  norm_num [wordMass, trLabel]

/-- The nonmatching, but still fully Parikh-balanced, literal source
control 001/100 has no aligned zero return at any interior index.
Both possible indices (1 and 2) are rejected by exact coordinate-0
word counts. Unlike the generic germ recurrence, this is a fully
word-level irreducibility check, at precisely its declared scope. -/
theorem tribonacci_nonmatching_control_is_irreducible :
    NoAlignedInteriorReturn trLabel [0,0,1] [1,0,0] := by
  intro k hk hlt heq
  have hk_cases : k = 1 ∨ k = 2 := by
    simp only [List.length_cons, List.length_nil] at hlt
    omega
  rcases hk_cases with hk1 | hk2
  · subst k
    have h0 := congrFun heq (0 : Fin 3)
    norm_num [wordMass, trLabel] at h0
  · subst k
    have h0 := congrFun heq (0 : Fin 3)
    norm_num [wordMass, trLabel] at h0


/-! ### Multi-child boundary localization interface

A strict child factorization is a concatenation of *balanced*
irreducible children. Any aligned balanced return strictly inside
one child remains an interior balanced return after preceding balanced
children. The new theorem explains why source-germ return witnesses
must be checked against actual child boundaries, not merely against
one guessed parent pair. -/

/-- Balance of all completed children propagates to their concatenation. -/
theorem balanced_child_list_mass
    (label : A → V) (children : List (List A × List A))
    (hchildren : ∀ pair ∈ children,
      wordMass label pair.1 = wordMass label pair.2) :
    wordMass label (children.flatMap Prod.fst) =
      wordMass label (children.flatMap Prod.snd) := by
  induction children with
  | nil => simp [wordMass]
  | cons child rest ih =>
      have hhead : wordMass label child.1 = wordMass label child.2 :=
        hchildren child (by simp)
      have hrest : ∀ pair ∈ rest,
          wordMass label pair.1 = wordMass label pair.2 := by
        intro pair hp
        exact hchildren pair (by simp [hp])
      have htail := ih hrest
      simp only [List.flatMap_cons, wordMass_append]
      rw [hhead, htail]

/-- If the completed previous children are balanced, an aligned return
at equal relative offset `k` in the next child is possible only if
that child itself has a balanced return at `k`. -/
theorem balanced_child_prefix_cancel
    (label : A → V)
    (completedTop completedBottom childTop childBottom : List A)
    (k : ℕ)
    (hcompleted :
      wordMass label completedTop = wordMass label completedBottom)
    (hreturn :
      wordMass label (completedTop ++ childTop.take k) =
        wordMass label (completedBottom ++ childBottom.take k)) :
    wordMass label (childTop.take k) =
      wordMass label (childBottom.take k) := by
  simp only [wordMass_append] at hreturn
  rw [hcompleted] at hreturn
  exact add_left_cancel hreturn

/-- A complete balanced previous prefix does not hide an interior
return inside an irreducible next child. The *only remaining*
candidate cuts in a complete strict factorization are its
balanced child boundaries (or events crossing unmatched child
addresses, which require a separate source-refinement theorem). -/
theorem irreducible_child_rules_out_internal_aligned_return
    (label : A → V)
    (completedTop completedBottom childTop childBottom : List A)
    (k : ℕ)
    (hcompleted :
      wordMass label completedTop = wordMass label completedBottom)
    (hirred : NoAlignedInteriorReturn label childTop childBottom)
    (hkpositive : 0 < k) (hkproper : k < childTop.length) :
    wordMass label (completedTop ++ childTop.take k) ≠
      wordMass label (completedBottom ++ childBottom.take k) := by
  intro hreturn
  apply hirred k hkpositive hkproper
  exact balanced_child_prefix_cancel label
    completedTop completedBottom childTop childBottom
    k hcompleted hreturn


/-- Balanced children must also have **equal physical word lengths**:
Parikh mass equality for an arbitrary label map alone does not
supply an aligned cut index. The full length theorem is a separate
Lean obligation, rather than an unstated assumption in the
multi-child localization argument. -/
theorem equal_length_child_list
    (children : List (List A × List A))
    (hchildren : ∀ pair ∈ children,
      pair.1.length = pair.2.length) :
    (children.flatMap Prod.fst).length =
      (children.flatMap Prod.snd).length := by
  induction children with
  | nil => simp
  | cons child rest ih =>
      have hhead : child.1.length = child.2.length :=
        hchildren child (by simp)
      have hrest : ∀ pair ∈ rest,
          pair.1.length = pair.2.length := by
        intro pair hp
        exact hchildren pair (by simp [hp])
      have htail := ih hrest
      simp only [List.flatMap_cons, List.length_append]
      omega

/-- Both canonical cut invariants survive an arbitrary completed
list of literal balanced equal-length child pairs. No replacement
of physical lengths by Perron lengths or numerical coordinates. -/
theorem balanced_children_canonical_boundary
    (label : A → V)
    (children : List (List A × List A))
    (hbalanced : ∀ pair ∈ children,
      wordMass label pair.1 = wordMass label pair.2)
    (hlength : ∀ pair ∈ children,
      pair.1.length = pair.2.length) :
    (children.flatMap Prod.fst).length =
      (children.flatMap Prod.snd).length ∧
    wordMass label (children.flatMap Prod.fst) =
      wordMass label (children.flatMap Prod.snd) := by
  exact ⟨equal_length_child_list children hlength,
    balanced_child_list_mass label children hbalanced⟩


/-- In the actual ordered derived factorization a normalized
irreducible balanced child may occur with raw sides swapped.
An equal-length irreducible pair remains irreducible after that
side swap. This is the explicit sign-cocycle compatibility needed
to apply boundary localization to *raw oriented* occurrences. -/
theorem noAlignedInteriorReturn_swap
    (label : A → V) (top bottom : List A)
    (hlength : top.length = bottom.length)
    (hirred : NoAlignedInteriorReturn label top bottom) :
    NoAlignedInteriorReturn label bottom top := by
  intro k hpos hproper hreturn
  have htop : k < top.length := by
    rw [hlength]
    exact hproper
  exact (hirred k hpos htop) hreturn.symm

end PscRoutes.R1Source

#print axioms PscRoutes.R1Source.cutPrefix_append_cutSuffix
#print axioms PscRoutes.R1Source.cutPrefix_isPrefix
#print axioms PscRoutes.R1Source.wordMass_append
#print axioms PscRoutes.R1Source.wordMass_substitution
#print axioms PscRoutes.R1Source.actualCut_prefix_mass_transport
#print axioms PscRoutes.R1Source.unit_source_defect_forces_aligned_interior_return
#print axioms PscRoutes.R1Source.irreducible_parent_excludes_unit_source_germ
#print axioms PscRoutes.R1Source.tribonacci_fourth_literal
#print axioms PscRoutes.R1Source.tribonacci_source_controls_are_legal_factors
#print axioms PscRoutes.R1Source.tribonacci_source_controls_balanced
#print axioms PscRoutes.R1Source.tribonacci_matching_source_control_has_interior_return
#print axioms PscRoutes.R1Source.tribonacci_matching_control_is_reducible
#print axioms PscRoutes.R1Source.tribonacci_nonmatching_control_is_irreducible
#print axioms PscRoutes.R1Source.balanced_child_list_mass
#print axioms PscRoutes.R1Source.balanced_child_prefix_cancel
#print axioms PscRoutes.R1Source.irreducible_child_rules_out_internal_aligned_return
#print axioms PscRoutes.R1Source.equal_length_child_list
#print axioms PscRoutes.R1Source.balanced_children_canonical_boundary
#print axioms PscRoutes.R1Source.noAlignedInteriorReturn_swap

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1Source.cutPrefix_append_cutSuffix,
      `PscRoutes.R1Source.cutPrefix_isPrefix,
      `PscRoutes.R1Source.wordMass_append,
      `PscRoutes.R1Source.wordMass_substitution,
      `PscRoutes.R1Source.actualCut_prefix_mass_transport,
      `PscRoutes.R1Source.unit_source_defect_forces_aligned_interior_return,
      `PscRoutes.R1Source.irreducible_parent_excludes_unit_source_germ,
      `PscRoutes.R1Source.tribonacci_fourth_literal,
      `PscRoutes.R1Source.tribonacci_source_controls_are_legal_factors,
      `PscRoutes.R1Source.tribonacci_source_controls_balanced,
      `PscRoutes.R1Source.tribonacci_matching_source_control_has_interior_return,
      `PscRoutes.R1Source.tribonacci_matching_control_is_reducible,
      `PscRoutes.R1Source.tribonacci_nonmatching_control_is_irreducible,
      `PscRoutes.R1Source.balanced_child_list_mass,
      `PscRoutes.R1Source.balanced_child_prefix_cancel,
      `PscRoutes.R1Source.irreducible_child_rules_out_internal_aligned_return,
      `PscRoutes.R1Source.equal_length_child_list,
      `PscRoutes.R1Source.balanced_children_canonical_boundary,
      `PscRoutes.R1Source.noAlignedInteriorReturn_swap] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_R1SOURCE_AXIOMS_OK\t{name}"
