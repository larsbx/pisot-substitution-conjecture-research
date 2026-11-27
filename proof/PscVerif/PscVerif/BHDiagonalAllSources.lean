import PscVerif.BHDiagonalTermination
import PscVerif.BHThirdLevelEntry

/-!
# Every strict original packet exits in the three high-determinant bands

The actual third-level marks provide entry into the central run window.
The diagonal uses the full residual/outer termination theorem; the two
adjacent bands use their existing central descent. All paths preserve
original digit occurrences, full integral displacement and terminal labels.

The source is any strict integral typed packet, not a bounded census or a
preselected finite carrier. The statement remains specific to the literal
family `(1, 0 1^k 2, 0^r 1)` with `r ≥ 12` and `r ≤ k ≤ r+2`.
-/

namespace Psc.BHDiagonalAllSources

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral
open Psc.ClassAMinusPrefixAssembly

theorem diagonal_entry_bounds {r β} (h : BHDiagonalLiteral.Family r β) :
    12 < β ∧ 3*β/4 < (r : ℝ)-1 := by
  have hr : (12 : ℝ) ≤ r := by exact_mod_cast h.large
  constructor <;> linarith [h.lower, h.upper]

theorem near_diagonal_entry_bounds {r k β} (h : Family r k β) :
    12 < β ∧ (r : ℝ) < β ∧ 3*β/4 < (k : ℝ)-1 := by
  have hr : (12 : ℝ) ≤ r := by exact_mod_cast h.large
  have hk : (r : ℝ)+1 ≤ k := by exact_mod_cast h.above
  constructor
  · linarith [h.lower]
  constructor <;> linarith [h.lower, h.upper]

/-- Uniform actual all-source labelled exit for the diagonal band. -/
theorem all_source_exit {r β} (h : BHDiagonalLiteral.Family r β)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    BHDiagonalProgress.LabelledExit r β p := by
  obtain ⟨q, hentry, hc⟩ := BHThirdLevelEntry.run_family_entry h.toRunFamily
    (diagonal_entry_bounds h).1 h.lower (diagonal_entry_bounds h).2 p hp
  obtain ⟨q', hexit, hlabel, hzero⟩ :=
    BHDiagonalTermination.central_hits_labelled_zero h hc
  exact ⟨q', hentry.trans hexit, hlabel, hzero⟩

/-- The same all-source conclusion is retained as a transcript of the
actual original top and bottom occurrence ordinals at every level. -/
theorem all_source_exit_ordered {r β} (h : BHDiagonalLiteral.Family r β)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ (q : Packet) (xs : List (ℕ × ℕ)),
      OrderedInteriorPath (sigma r r) (lengths r β) p xs q ∧
      q.top = q.bottom ∧ q.delta = 0 := by
  obtain ⟨q, hpath, hlabel, hzero⟩ := all_source_exit h p hp
  obtain ⟨xs, hordered⟩ := BHThirdLevelEntry.interior_path_ordered
    (sigma r r) (lengths r β) hp hpath
  exact ⟨q, xs, hordered, hlabel, hzero⟩

/-- This endpoint assumes only the integer parameter bound and strictness
of the source; it constructs the root and supplies every source exit. -/
theorem exists_root_all_source_exit (r : ℕ) (hr : 12 ≤ r) :
    ∃ β : ℝ, BHDiagonalLiteral.Family r β ∧
      ∀ p : Packet, p.Interior (lengths r β) →
        BHDiagonalProgress.LabelledExit r β p := by
  obtain ⟨β, h⟩ := BHDiagonalParameters.family_root_exists r hr
  exact ⟨β, h, all_source_exit h⟩

/-- The same literal entry closes the all-source assembly for both
previously proved off-diagonal central-descent bands. -/
theorem near_diagonal_all_source_exit {r k β} (h : Family r k β)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β))
      p (runPacket 0 0 0) := by
  obtain ⟨q, hentry, hc⟩ := BHThirdLevelEntry.run_family_entry h.toRunFamily
    (near_diagonal_entry_bounds h).1 (near_diagonal_entry_bounds h).2.1
    (near_diagonal_entry_bounds h).2.2 p hp
  exact hentry.trans (central_hits_zero h hc)

theorem exists_root_near_diagonal_all_source_exit (r k : ℕ)
    (hr : 12 ≤ r) (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) :
    ∃ β : ℝ, Family r k β ∧
      ∀ p : Packet, p.Interior (lengths r β) →
        Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β))
          p (runPacket 0 0 0) := by
  obtain ⟨β, h⟩ := BHDiagonalParameters.near_diagonal_root_exists r k hr hklo hkhi
  exact ⟨β, h, near_diagonal_all_source_exit h⟩

/-- One parameter-only endpoint covers all three high-determinant bands. -/
theorem three_band_all_source_exit (r k : ℕ) (hr : 12 ≤ r)
    (hklo : r ≤ k) (hkhi : k ≤ r+2) :
    ∃ β : ℝ, (k : ℝ) < β ∧ β < (k : ℝ)+1 ∧
      β^3 = (k : ℝ)*β^2+2*β+r ∧
      ∀ p : Packet, p.Interior (lengths r β) →
        ∃ q : Packet,
          Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p q ∧
          q.top = q.bottom ∧ q.delta = 0 := by
  by_cases hk : k = r
  · subst k
    obtain ⟨β, h, hexit⟩ := exists_root_all_source_exit r hr
    exact ⟨β, h.lower, h.upper, h.cubic, hexit⟩
  · obtain ⟨β, h, hexit⟩ := exists_root_near_diagonal_all_source_exit r k hr
      (by omega) hkhi
    refine ⟨β, h.lower, h.upper, h.cubic, fun p hp =>
      ⟨runPacket 0 0 0, hexit p hp, rfl, ?_⟩⟩
    funext i
    fin_cases i <;> rfl

end Psc.BHDiagonalAllSources
