import PscVerif.PeriodicPartnerRealization
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Normalized Haar measure for the full compatible-history solenoid. -/

namespace Psc.PeriodicPartnerSolenoidHaar

open Function MeasureTheory Set
open Psc.PeriodicPartnerHull Psc.PeriodicPartnerRealization

variable {α : Type*} [Fintype α] [DecidableEq α] (S : LengthSubst α)

scoped instance solenoidMeasurableSpace : MeasurableSpace (Solenoid S) := borel _

scoped instance solenoidBorelSpace : BorelSpace (Solenoid S) := ⟨rfl⟩

scoped instance solenoidCompact : CompactSpace (Solenoid S) := solenoid_compactSpace S

scoped instance solenoidT2 : T2Space (Solenoid S) := solenoid_t2Space S

/-- Normalize additive Haar measure on the whole compact solenoid. -/
noncomputable def haar : Measure (Solenoid S) :=
  Measure.addHaarMeasure ⟨⟨univ, isCompact_univ⟩, by simp⟩

instance haar_isAddHaarMeasure : (haar S).IsAddHaarMeasure := by
  unfold haar
  infer_instance

instance haar_isProbabilityMeasure : IsProbabilityMeasure (haar S) :=
  ⟨Measure.addHaarMeasure_self⟩

/-- The literal coordinatewise shift, as an additive homomorphism. -/
def shiftAddHom : Solenoid S →+ Solenoid S where
  toFun := shiftS S
  map_zero' := shiftS_zero S
  map_add' z w := Subtype.ext (funext fun n => (torusMap S).map_add (z.1 n) (w.1 n))

/-- Full-history inflation preserves normalized Haar probability. -/
theorem measurePreserving_shiftS : MeasurePreserving (shiftS S) (haar S) (haar S) :=
  AddMonoidHom.measurePreserving (f := shiftAddHom S) (shiftHomeomorph S).continuous
    (shiftS_bijective S).2 rfl

end Psc.PeriodicPartnerSolenoidHaar
