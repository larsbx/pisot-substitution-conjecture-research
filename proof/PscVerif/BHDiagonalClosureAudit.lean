import PscVerif.BHThreeBandClosure
import PscVerif.BHThreeBandBPA
import PscVerif.BHHigherDeterminantPisot
import PscVerif.BHDiagonalCertificate
import PscVerif.BHDiagonalClassification
import Lean.Util.CollectAxioms

set_option autoImplicit false

/-!
# Unconditional signature and recursive-axiom audit

The explicit examples below are conditionality checks: their hypotheses
are exactly the displayed parameter bounds, family equations, or source
strictness. In particular, no entry, residual classification, progress,
coincidence, root-existence, finite carrier, or spectral premise is supplied
to an all-parameter endpoint. The final capstone example expands every field
on one and the same root rather than merely checking a theorem name.
-/

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.BHNearDiagonalLiteral Psc.BHNearDiagonalDescent
open Psc.ClassAMinusPrefixAssembly Matrix Polynomial

example (r : ℕ) (hr : 12 ≤ r) :
    ∃ β : ℝ, Psc.BHDiagonalLiteral.Family r β :=
  Psc.BHDiagonalParameters.family_root_exists r hr

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β)
    (z y : ℤ) (hdisk : (z : ℝ)^2+(y : ℝ)^2 < (r : ℝ)^2) :
    (∃ t : ℤ, |(t : ℝ)+((β-r)*y+(r/β)*z)| ≤ ((r : ℝ)-1)/β ∧
      energy (β-r) (r/β) y t < energy (β-r) (r/β) z y) ∨
    y = 0 ∨ ∃ N : ℕ, r = 3*N ∧
      ((z = (N : ℤ)-1 ∧ y = N) ∨ (z = (N : ℤ)+2 ∧ y = -(N : ℤ)) ∨
       (z = 1-(N : ℤ) ∧ y = -(N : ℤ)) ∨ (z = -(N : ℤ)-2 ∧ y = N)) :=
  Psc.BHDiagonalClassificationFull.residual_classification h z y hdisk

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β)
    {p : Packet} (hp : Central r r β p) :
    ∃ q : Packet,
      Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β)) p q ∧
      q.top = q.bottom ∧ q.delta = 0 :=
  Psc.BHDiagonalTermination.central_hits_labelled_zero h hp

example {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hβ : 12 < β) (hrβ : (r : ℝ) < β) (hwindow : 3*β/4 < (k : ℝ)-1)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ q : Packet,
      Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p q ∧
      Central r k β q :=
  Psc.BHThirdLevelEntry.run_family_entry h hβ hrβ hwindow p hp

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ q : Packet,
      Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β)) p q ∧
      q.top = q.bottom ∧ q.delta = 0 :=
  Psc.BHDiagonalAllSources.all_source_exit h p hp

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ (q : Packet) (xs : List (ℕ × ℕ)),
      OrderedInteriorPath (sigma r r) (lengths r β) p xs q ∧
      q.top = q.bottom ∧ q.delta = 0 :=
  Psc.BHDiagonalAllSources.all_source_exit_ordered h p hp

example (r k : ℕ) (hr : 12 ≤ r) (hklo : r ≤ k) (hkhi : k ≤ r+2) :
    ∃ β : ℝ, (k : ℝ) < β ∧ β < (k : ℝ)+1 ∧
      β^3 = (k : ℝ)*β^2+2*β+r ∧
      ∀ p : Packet, p.Interior (lengths r β) →
        ∃ q : Packet,
          Relation.ReflTransGen (InteriorStep (sigma r k) (lengths r β)) p q ∧
          q.top = q.bottom ∧ q.delta = 0 :=
  Psc.BHDiagonalAllSources.three_band_all_source_exit r k hr hklo hkhi

example (r : ℕ) (hr : 12 ≤ r) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r r)^n) a c) ∧
    Irreducible (Psc.BHDiagonalPisot.incidenceQ r).charpoly ∧
    ∃ β : ℝ, Psc.BHDiagonalLiteral.Family r β ∧ 1 < β ∧
      aeval (β : ℂ) (Psc.BHDiagonalPisot.incidenceQ r).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (Psc.BHDiagonalPisot.incidenceQ r).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1) ∧
      ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
        w ᵥ* (inc (sigma r r)).map (Nat.cast : ℕ → ℝ) = β • w :=
  Psc.BHDiagonalPisot.primitive_irreducible_pisot r hr

example (r k : ℕ) (hr : 12 ≤ r) (hklo : r+1 ≤ k) (hkhi : k ≤ r+2) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r k)^n) a c) ∧
    Irreducible (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly ∧
    ∃ β : ℝ, Family r k β ∧ 1 < β ∧
      aeval (β : ℂ) (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1) ∧
      ∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
        w ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) = β • w :=
  Psc.BHNearDiagonalPisot.primitive_irreducible_pisot r k hr hklo hkhi

/-- The larger parameter range certifies actual arithmetic and eigenlengths;
it does not silently strengthen the three-band geometric conclusion. -/
example (r k : ℕ) (hr : 4 ≤ r) (hk : r ≤ k) :
    (∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r k)^n) a c) ∧
    Irreducible (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly ∧
    ∃ β : ℝ, Psc.BHHigherDeterminantPisot.Family r k β ∧ 1 < β ∧
      aeval (β : ℂ) (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1) ∧
      (∀ a, 0 < lengths r β a) ∧
      lengths r β ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) =
        β • lengths r β ∧
      (∀ a, physicalLength (lengths r β) (sigma r k a) = β * lengths r β a) :=
  Psc.BHHigherDeterminantPisot.primitive_irreducible_pisot r k hr hk

example (r k : ℕ) : (Psc.BHNearDiagonalPisot.incidenceQ r k).det = r :=
  Psc.BHNearDiagonalPisot.determinant r k

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) (a b : Fin 3) :
    ∃ (n : ℕ) (top : Mark (image (sigma r r) n a))
      (bottom : Mark (image (sigma r r) n b)),
      top.letter = bottom.letter ∧ parikhZ top.before = parikhZ bottom.before :=
  Psc.BHDiagonalConsequences.all_pairs_equal_prefix_marks h a b

example (r k : ℕ) (hr : 12 ≤ r) (hklo : r ≤ k) (hkhi : k ≤ r+2)
    (a b : Fin 3) :
    ∃ (n : ℕ) (P Q P' Q' : Word) (x : Fin 3),
      (subst (sigma r k))^[n] [a] = P ++ x :: Q ∧
      (subst (sigma r k))^[n] [b] = P' ++ x :: Q' ∧ Equiv1 P P' :=
  Psc.BHDiagonalConsequences.three_band_strong_coincidence r k hr hklo hkhi a b

example (r k : ℕ) (hr : 12 ≤ r) (hklo : r ≤ k) (hkhi : k ≤ r+2)
    (C : Finset WordPair) : ¬ Psc.StrictSystem.StrictSystem (sigma r k) C :=
  Psc.BHDiagonalConsequences.three_band_no_strict_system r k hr hklo hkhi C

/-- Expanded capstone contract: every conclusion is on the same actual
substitution, actual incidence, and constructed root. -/
example (r k : ℕ) (hr : 12 ≤ r) (hklo : r ≤ k) (hkhi : k ≤ r+2) :
    ∃ β : ℝ, (k : ℝ) < β ∧ β < (k : ℝ)+1 ∧
      β^3 = (k : ℝ)*β^2+2*β+r ∧
      (∃ n ≥ 1, ∀ a c, 0 < (inc (sigma r k)^n) a c) ∧
      (Psc.BHNearDiagonalPisot.incidenceQ r k).det = r ∧
      Irreducible (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly ∧
      1 < β ∧ aeval (β : ℂ) (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 ∧
      (∀ z : ℂ, aeval z (Psc.BHNearDiagonalPisot.incidenceQ r k).charpoly = 0 →
        z ≠ (β : ℂ) → ‖z‖ < 1) ∧
      (∀ a, 0 < lengths r β a) ∧
      (∀ a, physicalLength (lengths r β) (sigma r k a) = β*lengths r β a) ∧
      (∃ w : Fin 3 → ℝ, (∀ a, 0 < w a) ∧
        w ᵥ* (inc (sigma r k)).map (Nat.cast : ℕ → ℝ) = β • w) ∧
      (∀ p : Packet, p.Interior (lengths r β) →
        ∃ (q : Packet) (xs : List (ℕ × ℕ)),
          OrderedInteriorPath (sigma r k) (lengths r β) p xs q ∧
          q.top = q.bottom ∧ q.delta = 0) ∧
      (∀ a b, Psc.StrictSystem.StrongCoincidenceWitness (sigma r k) a b) ∧
      ∀ C : Finset WordPair, ¬ Psc.StrictSystem.StrictSystem (sigma r k) C := by
  obtain ⟨β, h⟩ := Psc.BHThreeBandClosure.family_closure r k hr hklo hkhi
  exact ⟨β, h.lower, h.upper, h.cubic, h.primitive, h.determinant,
    h.irreducible, h.expanding, h.root, h.contracting, h.positive_lengths,
    h.lengths_scale, h.positive_left_eigenvector, h.all_source,
    h.strong_coincidence, h.no_strict_system⟩

/-- The extracted generic contraction result retains its original spectral
hypotheses and constructs its proper contracting data. -/
example {α : Type*} [DecidableEq α] [Fintype α] (s : α → List α)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    {β : ℝ} {ℓ : α → ℝ} (hℓ : ∀ a, 0 < ℓ a)
    (hℓM : ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ)
    (hpisot : ∀ z : ℂ, ((inc s).map (Nat.cast : ℕ → ℂ)).charpoly.eval z = 0 →
      z ≠ β → ‖z‖ < 1) :
    ∃ (ν : (α → ℤ) → ℝ) (ρ : ℝ),
      Psc.GeometricF.ContractionData s (Psc.GeometricF.lenHom ℓ) ν ρ :=
  Psc.GeometricFPisot.exists_contractionData_of_pisot s hirr hℓ hℓM hpisot

/-- Finite carrier construction requires actual Pisot incidence data, but
does not take a carrier, exit, coincidence, or seed-balance premise. -/
example (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ (β : ℂ) → ‖z‖ < 1) (T : WordPair) :
    ∃ C : Finset Packet, Psc.OccurrenceAncestry.CoversWords ℓ T (↑C : Set Packet) ∧
      (∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) ∧
      (∀ p ∈ C, p.Interior ℓ) :=
  Psc.BHPisotFiniteBPA.finite_closed_packet_cover_of_pisot s ℓ β hpos hscale hirr hpisot T

example (r k : ℕ) (hr : 12 ≤ r) (hklo : r ≤ k) (hkhi : k ≤ r+2)
    (T : WordPair) (hT : IsBlock T) :
    Psc.StrictSystem.TerminatesWithCoincidence (sigma r k) T :=
  Psc.BHThreeBandBPA.all_blocks_terminate r k hr hklo hkhi T hT

/-- Expanded full-iterate condition: finitely many actual reduced factors,
and an actual singleton coincidence in an iterate of every reached factor.
Only the natural parameter bounds and the irreducible balanced seed occur
as hypotheses. -/
example (r k : ℕ) (hr : 12 ≤ r) (hklo : r ≤ k) (hkhi : k ≤ r+2)
    (T : WordPair) (hT : IsBlock T) :
    {U | ∃ n, U ∈ red ((subst (sigma r k))^[n] T.1)
      ((subst (sigma r k))^[n] T.2)}.Finite ∧
    ∀ U, (∃ n, U ∈ red ((subst (sigma r k))^[n] T.1)
      ((subst (sigma r k))^[n] T.2)) →
      ∃ m a, ([a], [a]) ∈ red ((subst (sigma r k))^[m] U.1)
        ((subst (sigma r k))^[m] U.2) :=
  Psc.BHThreeBandBPA.all_blocks_full_factor_coincidence r k hr hklo hkhi T hT

example (r k : ℕ) (hr : 12 ≤ r) (hklo : r ≤ k) (hkhi : k ≤ r+2)
    (a b : Fin 3) (hab : a ≠ b) :
    Psc.StrictSystem.TerminatesWithCoincidence (sigma r k) ([a,b], [b,a]) :=
  Psc.BHThreeBandBPA.all_swap_seeds_terminate r k hr hklo hkhi a b hab

/-! Inherited refusal controls remain independently compiled. -/

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) :
    ¬ Psc.BHNearDiagonalDescent.Window (β-r) (r/β) (((r : ℝ)-1)/β) :=
  Psc.BHDiagonalLiteral.not_near_diagonal_window h

example (r : ℕ) (β : ℝ) : ¬ Central r r β (runPacket r 0 0) :=
  Psc.BHDiagonalLiteral.saturation_not_central r β

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) :
    (runPacket r 0 0).delta ≠ 0 := Psc.BHDiagonalLiteral.saturation_not_zero h

example : Psc.BHDiagonalLiteral.zero12.top ≠ Psc.BHDiagonalLiteral.zero12.bottom :=
  Psc.BHDiagonalLiteral.zero12_not_labelled

example : (runPacket 1 0 0).delta 2 = 0 ∧ (runPacket 1 0 0).delta 1 = 0 ∧
    (runPacket 1 0 0).delta ≠ 0 :=
  Psc.BHDiagonalCertificate.projected_zero_is_not_full_zero

example : ∃ s u c k z y q : ℝ,
    4 < s ∧ 0 < u ∧ u < 1/12 ∧ 0 ≤ c ∧ c < 1/3 ∧
    (s+1/3)*u < 3/8 ∧ y = s+(q-c)/3 ∧ s-3/2 < y ∧
    0 ≤ k ∧ k < s+1 ∧ k = z+1+y*u-q*s ∧
    0 ≤ Psc.BHDiagonalClassification.change k 1 z y ∧ 0 < q ∧ q < 1 :=
  Psc.BHDiagonalClassification.nonintegral_congruence_control

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let endpoints := #[
      `Psc.BHDiagonalParameters.family_root_exists,
      `Psc.BHDiagonalParameters.near_diagonal_root_exists,
      `Psc.BHDiagonalOuter.truncate_decreases,
      `Psc.BHDiagonalOuter.choose_rounding,
      `Psc.BHDiagonalOuter.cutoff_implies_disk,
      `Psc.BHDiagonalClassificationFull.residual_classification,
      `Psc.BHDiagonalProgress.residual_progress,
      `Psc.BHDiagonalTermination.finite_energy_sublevel,
      `Psc.BHDiagonalTermination.central_hits_labelled_zero,
      `Psc.BHDiagonalTermination.run_window_exit_for_all_parameters,
      `Psc.BHThirdLevelGeometry.exists_clean_window,
      `Psc.BHThirdLevelTransport.assembled_has_ordered_interior_path,
      `Psc.BHThirdLevelTransport.positioned_run_marks,
      `Psc.BHThirdLevelTransport.half_mass_common_interval,
      `Psc.BHThirdLevelEntry.run_family_entry,
      `Psc.BHThirdLevelEntry.run_family_entry_ordered,
      `Psc.BHDiagonalAllSources.all_source_exit,
      `Psc.BHDiagonalAllSources.all_source_exit_ordered,
      `Psc.BHDiagonalAllSources.three_band_all_source_exit,
      `Psc.BHDiagonalPisot.primitive_irreducible_pisot,
      `Psc.BHNearDiagonalPisot.primitive_irreducible_pisot,
      `Psc.BHHigherDeterminantPisot.primitive_irreducible_pisot,
      `Psc.BHNearDiagonalPisot.determinant,
      `Psc.BHDiagonalConsequences.all_pairs_equal_prefix_marks,
      `Psc.BHDiagonalConsequences.all_pairs_strong_coincidence_for_all_parameters,
      `Psc.BHDiagonalConsequences.three_band_strong_coincidence,
      `Psc.BHDiagonalConsequences.three_band_no_strict_system,
      `Psc.BHThreeBandClosure.family_closure,
      `Psc.GeometricF.lengthData_of_left_eigen,
      `Psc.GeometricFPisot.exists_contractionData_of_pisot,
      `Psc.GeometricFPisot.aeval_charpoly,
      `Psc.BHPisotFiniteBPA.packet_reach_finite,
      `Psc.BHPisotFiniteBPA.finite_closed_packet_cover_of_pisot,
      `Psc.BHPisotFiniteBPA.terminates_of_pisot_all_source_exit,
      `Psc.BHThreeBandBPA.all_blocks_terminate,
      `Psc.BHThreeBandBPA.all_blocks_full_factor_coincidence,
      `Psc.BHThreeBandBPA.all_swap_seeds_terminate,
      `Psc.BHBoundedFactors.expanding_zero_cover_without_coincidence,
      `Psc.BHDiagonalLiteral.not_near_diagonal_window,
      `Psc.BHDiagonalLiteral.saturation_not_central,
      `Psc.BHDiagonalLiteral.saturation_not_zero,
      `Psc.BHDiagonalLiteral.zero12_not_labelled,
      `Psc.BHDiagonalCertificate.projected_zero_is_not_full_zero,
      `Psc.BHDiagonalClassification.nonintegral_congruence_control]
    let modules := #[
      `PscVerif.BHDiagonalAllSources,
      `PscVerif.BHDiagonalClassificationFull,
      `PscVerif.BHDiagonalConsequences,
      `PscVerif.BHDiagonalOuter,
      `PscVerif.BHDiagonalParameters,
      `PscVerif.BHDiagonalPisot,
      `PscVerif.BHDiagonalProgress,
      `PscVerif.BHDiagonalTermination,
      `PscVerif.BHNearDiagonalPisot,
      `PscVerif.BHThirdLevelEntry,
      `PscVerif.BHThirdLevelGeometry,
      `PscVerif.BHThirdLevelTransport,
      `PscVerif.BHThreeBandClosure,
      `PscVerif.BHPisotFiniteBPA,
      `PscVerif.BHThreeBandBPA,
      `PscVerif.BHHigherDeterminantPisot,
      `PscVerif.GeometricFLength,
      `PscVerif.GeometricFPisotCore]
    for name in endpoints do
      let some info := env.find? name | throwError "Missing endpoint {name}"
      unless info.isTheorem do throwError "Not a theorem: {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom in {name}: {ax}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_BH_DIAGONAL_CLOSURE_ENDPOINT\t{name}"
    for mod in modules do
      let some index := env.getModuleIdx? mod | throwError "Missing module {mod}"
      let mut declarations := 0
      let mut theorems := 0
      for info in env.header.moduleData[index.toNat]!.constants do
        unless env.getModuleIdxFor? info.name == some index do continue
        if info.isAxiom then throwError "Local axiom {info.name}"
        for ax in ← collectAxioms info.name do
          unless allowed.contains ax do throwError "Unexpected axiom in {info.name}: {ax}"
        declarations := declarations + 1
        if info.isTheorem then theorems := theorems + 1
      if theorems == 0 then throwError "Empty compiled module {mod}"
      Lean.Core.liftIOCore <| IO.println
        s!"PSC_BH_DIAGONAL_CLOSURE_MODULE\t{mod}\t{declarations}\t{theorems}"
    Lean.Core.liftIOCore <| IO.println
      s!"PSC_BH_DIAGONAL_CLOSURE_AUDIT_COMPLETE\t{endpoints.size}\t{modules.size}"
