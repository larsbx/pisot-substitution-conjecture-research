import PscVerif.GeometricFPisotCore
import PscVerif.ZeroFibreOverlap
import PscVerif.BHBoundedFactors

/-!
# Actual finite balanced-pair termination from Pisot enclosure and labelled exits

Full typed packets use top-minus-bottom displacement. The existing finite
strict-overlap graph uses the opposite sign; the adapters below retain
both labels, the entire integer vector and the same original word marks.

Pisot contraction makes the complete all-child forward orbit of each
strict packet finite. The union over the actual strict seed marks supplies
a finite closed carrier. Actual all-source labelled exits then discharge
both finiteness and productivity of the terminal balanced-pair algorithm.
No property (F), inverse incidence, unimodularity or finite seed-orbit
premise is assumed.

Source decisions: `docs/bh-diagonal-arithmetic-stop-go-2026-11-27.md`
and `docs/bh-three-band-spectral-transfer-2026-11-27.md`, extending the
reviewed finite-enclosure mechanism without a new universal invariant.
-/

namespace Psc.BHPisotFiniteBPA

open Psc.Binomial Psc.Incidence Psc.Reduction Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.OccurrenceSuccessor Psc.OccurrenceAncestry Psc.OccurrenceFinite
open Matrix Polynomial

theorem lenHom_offset (ℓ : Fin 3 → ℝ) (v : Fin 3 → ℤ) :
    GeometricF.lenHom ℓ v = offset ℓ v := rfl

theorem pvec_parikh (w : Word) : GeometricF.pvec w = parikhZ w := rfl

theorem incZ_incidence (s : Fin 3 → Word) :
    GeometricF.incZ s = incidenceZ s := rfl

/-- Change only the displacement convention, retaining the original labels. -/
def packetOverlap (p : Packet) : GeometricF.OverlapCoordinates (Fin 3) :=
  ⟨p.top, p.bottom, -p.delta⟩

def overlapPacket (u : GeometricF.OverlapCoordinates (Fin 3)) : Packet :=
  ⟨u.top, u.bottom, -u.shift⟩

@[simp] theorem overlapPacket_packetOverlap (p : Packet) :
    overlapPacket (packetOverlap p) = p := by
  cases p
  simp [overlapPacket, packetOverlap]

@[simp] theorem packetOverlap_overlapPacket (u : GeometricF.OverlapCoordinates (Fin 3)) :
    packetOverlap (overlapPacket u) = u := by
  cases u
  simp [overlapPacket, packetOverlap]

/-- The two strict-interior predicates agree after reversing the shift. -/
theorem packetOverlap_interior_iff (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (p : Packet) :
    (packetOverlap p).Interior (GeometricF.lenHom ℓ) ↔ p.Interior ℓ := by
  rw [Packet.interior_iff_bounds ℓ hpos]
  simp only [GeometricF.OverlapCoordinates.Interior, packetOverlap,
    GeometricF.lenHom_single, map_neg, lenHom_offset]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

def strictPacketOverlap (ℓ : Fin 3 → ℝ) (hpos : ∀ a, 0 < ℓ a)
    (p : Packet) (hp : p.Interior ℓ) : GeometricF.StrictOverlap (GeometricF.lenHom ℓ) :=
  ⟨packetOverlap p, (packetOverlap_interior_iff ℓ hpos p).mpr hp⟩

/-- A literal packet child gives the literal overlap child using exactly
the same two original occurrences and the full negated affine equation. -/
theorem digitStep_overlap {s : Fin 3 → Word} {p q : Packet} (h : DigitStep s p q) :
    GeometricF.LiteralOverlapChild s (packetOverlap p) (packetOverlap q) := by
  obtain ⟨dt, db, rfl⟩ := h
  refine ⟨dt.before, dt.after, db.before, db.after, dt.split, db.split, ?_⟩
  change -(incidenceZ s *ᵥ p.delta + OccurrenceTransport.residual dt.before db.before) =
    GeometricF.incZ s *ᵥ (-p.delta) + GeometricF.pvec db.before - GeometricF.pvec dt.before
  rw [incZ_incidence, pvec_parikh, pvec_parikh, Matrix.mulVec_neg]
  unfold OccurrenceTransport.residual
  abel

theorem interior_path_target {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ} {p q : Packet}
    (hp : p.Interior ℓ) (hpath : Relation.ReflTransGen (InteriorStep s ℓ) p q) :
    q.Interior ℓ := by
  induction hpath with
  | refl => exact hp
  | tail _ he _ => exact he.2

/-- The complete strict packet path embeds in the complete overlap graph;
the relation includes all actual literal children, not a chosen policy. -/
theorem interior_path_overlap (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {p q : Packet} (hp : p.Interior ℓ) (hq : q.Interior ℓ)
    (hpath : Relation.ReflTransGen (InteriorStep s ℓ) p q) :
    GeometricF.OverlapReach s (GeometricF.lenHom ℓ)
      (strictPacketOverlap ℓ hpos p hp) (strictPacketOverlap ℓ hpos q hq) := by
  revert hq
  induction hpath with
  | refl => intro _; exact .refl
  | @tail b c hprev he ih =>
    intro _
    exact (ih (interior_path_target hp hprev)).tail (digitStep_overlap he.1)

/-- Every full strict packet has a finite all-child forward reachable set
under the existing proper Pisot contraction data. -/
theorem packet_reach_finite (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {ν : (Fin 3 → ℤ) → ℝ} {ρ : ℝ}
    (hc : GeometricF.ContractionData s (GeometricF.lenHom ℓ) ν ρ)
    (p : Packet) (hp : p.Interior ℓ) :
    {q | Relation.ReflTransGen (InteriorStep s ℓ) p q}.Finite := by
  have hf := GeometricF.overlap_reach_finite hc (strictPacketOverlap ℓ hpos p hp)
  apply (hf.image (fun v => overlapPacket v.val)).subset
  intro q hq
  have hqi := interior_path_target hp hq
  refine ⟨strictPacketOverlap ℓ hpos q hqi, interior_path_overlap s ℓ hpos hp hqi hq, ?_⟩
  exact overlapPacket_packetOverlap q

/-- The actual seed marks generate a finite carrier closed under every
literal interior edge. Every carrier member remains a strict full packet. -/
theorem finite_closed_packet_cover_of_contraction (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (hpos : ∀ a, 0 < ℓ a) {ν : (Fin 3 → ℤ) → ℝ} {ρ : ℝ}
    (hc : GeometricF.ContractionData s (GeometricF.lenHom ℓ) ν ρ) (T : WordPair) :
    ∃ C : Finset Packet, CoversWords ℓ T (↑C : Set Packet) ∧
      (∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) ∧
      (∀ p ∈ C, p.Interior ℓ) := by
  classical
  let seeds := (packetSupport {T}).filter (fun p => p.Interior ℓ)
  let C : Set Packet := ⋃ p ∈ (↑seeds : Set Packet),
    {q | Relation.ReflTransGen (InteriorStep s ℓ) p q}
  have hfin : C.Finite := seeds.finite_toSet.biUnion (fun p hp =>
    packet_reach_finite s ℓ hpos hc p (Finset.mem_filter.mp hp).2)
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro top bot hover
    apply hfin.mem_toFinset.mpr
    let m : MarkedPair := ⟨T, top, bot⟩
    have hseed : m.packet ∈ seeds := Finset.mem_filter.mpr
      ⟨mem_packetSupport.mpr ⟨m, by simp [m], rfl⟩,
        (MarkedPair.overlaps_iff ℓ m).mp hover⟩
    exact Set.mem_iUnion.mpr ⟨m.packet, Set.mem_iUnion.mpr ⟨hseed, .refl⟩⟩
  · intro p hp q he
    apply hfin.mem_toFinset.mpr
    obtain ⟨seed, hseed, hpath⟩ := Set.mem_iUnion₂.mp (hfin.mem_toFinset.mp hp)
    exact Set.mem_iUnion₂.mpr ⟨seed, hseed, hpath.tail he⟩
  · intro p hp
    obtain ⟨seed, hseed, hpath⟩ := Set.mem_iUnion₂.mp (hfin.mem_toFinset.mp hp)
    exact interior_path_target (Finset.mem_filter.mp hseed).2 hpath

/-- Exact physical image scaling is precisely the left-eigenrow equation
for the original image-letter incidence counts. -/
theorem left_eigen_of_scaling (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a) :
    ℓ ᵥ* (inc s).map (Nat.cast : ℕ → ℝ) = β • ℓ := by
  ext c
  simpa [Matrix.vecMul, dotProduct, Matrix.map_apply, physicalLength, inc_apply]
    using hscale c

/-- The actual irreducible Pisot characteristic polynomial and exact
positive length scaling supply the already proved proper contraction. -/
theorem contraction_of_pisot (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ (β : ℂ) → ‖z‖ < 1) :
    ∃ (ν : (Fin 3 → ℤ) → ℝ) (ρ : ℝ),
      GeometricF.ContractionData s (GeometricF.lenHom ℓ) ν ρ := by
  apply GeometricFPisot.exists_contractionData_of_pisot s hirr hpos
    (left_eigen_of_scaling s ℓ β hscale)
  intro z hz hne
  apply hpisot z _ hne
  rw [Psc.GeometricFPisot.aeval_charpoly]
  exact hz

/-- Arithmetic alone supplies a finite all-child carrier for every
finite seed's strict marks. Its productivity is a separate input below. -/
theorem finite_closed_packet_cover_of_pisot (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ (β : ℂ) → ‖z‖ < 1) (T : WordPair) :
    ∃ C : Finset Packet, CoversWords ℓ T (↑C : Set Packet) ∧
      (∀ p ∈ C, ∀ q, InteriorStep s ℓ p q → q ∈ C) ∧
      (∀ p ∈ C, p.Interior ℓ) := by
  obtain ⟨ν, ρ, hc⟩ := contraction_of_pisot s ℓ β hpos hscale hirr hpisot
  exact finite_closed_packet_cover_of_contraction s ℓ hpos hc T

/-- Every irreducible balanced seed terminates with coincidence when the
actual irreducible Pisot incidence has strict all-source labelled exits.
The finite full carrier is constructed, not assumed, and closure includes
all literal interior edges. -/
theorem terminates_of_pisot_all_source_exit (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ) (β : ℝ)
    (hpos : ∀ a, 0 < ℓ a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength ℓ (s a) = β * ℓ a)
    (hirr : Irreducible ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly)
    (hpisot : ∀ z : ℂ, aeval z ((inc s).map (Nat.cast : ℕ → ℚ)).charpoly = 0 →
      z ≠ (β : ℂ) → ‖z‖ < 1)
    (hexit : ∀ p : Packet, p.Interior ℓ → ∃ q : Packet,
      Relation.ReflTransGen (InteriorStep s ℓ) p q ∧ q.top = q.bottom ∧ q.delta = 0)
    (T : WordPair) (hT : IsBlock T) :
    Psc.StrictSystem.TerminatesWithCoincidence s T := by
  obtain ⟨C, hseed, hclosed, hstrict⟩ :=
    finite_closed_packet_cover_of_pisot s ℓ β hpos hscale hirr hpisot T
  apply BHBoundedFactors.terminates_of_closed_diagonal_cover s ℓ β hpos hβ hscale
    T hT C hseed hclosed
  intro p hp
  obtain ⟨q, hpath, hlabels, hzero⟩ := hexit p (hstrict p hp)
  exact ⟨q, hpath, hlabels, hzero⟩

end Psc.BHPisotFiniteBPA
