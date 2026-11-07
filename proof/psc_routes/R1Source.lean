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

end PscRoutes.R1Source

#print axioms PscRoutes.R1Source.cutPrefix_append_cutSuffix
#print axioms PscRoutes.R1Source.cutPrefix_isPrefix
#print axioms PscRoutes.R1Source.wordMass_append
#print axioms PscRoutes.R1Source.wordMass_substitution
#print axioms PscRoutes.R1Source.actualCut_prefix_mass_transport
#print axioms PscRoutes.R1Source.unit_source_defect_forces_aligned_interior_return
#print axioms PscRoutes.R1Source.irreducible_parent_excludes_unit_source_germ

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1Source.cutPrefix_append_cutSuffix,
      `PscRoutes.R1Source.cutPrefix_isPrefix,
      `PscRoutes.R1Source.wordMass_append,
      `PscRoutes.R1Source.wordMass_substitution,
      `PscRoutes.R1Source.actualCut_prefix_mass_transport,
      `PscRoutes.R1Source.unit_source_defect_forces_aligned_interior_return,
      `PscRoutes.R1Source.irreducible_parent_excludes_unit_source_germ] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_R1SOURCE_AXIOMS_OK\t{name}"
