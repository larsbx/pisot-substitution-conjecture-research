import PscVerif.ClassARunDescent
import Lean.Util.CollectAxioms

namespace Psc.ClassARunDescentAudit

open Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.ClassARunDescent Matrix

private def runSize (k t : ℕ) (a : Fin 3) : ℕ :=
  if a = 0 then (k+t+3)+(k+2*t+5) else if a = 1 then k+t+3 else (k+t+3)-1

private def literalSigma (k t : ℕ) (a : Fin 3) : Word :=
  [if a = 1 then 1 else 0] ++ List.replicate (runSize k t a) 2 ++
    [if a = 2 then 1 else 0]

private def literalLengths (α h : ℝ) : Fin 3 → ℝ := ![2+α-h, 1+h, 1]

private def literalGap (L : Fin 3 → ℝ) (β : ℝ) (source : Packet) : ℝ :=
  -(β * offset L source.delta) + L (if source.bottom = 1 then 1 else 0) -
    L (if source.top = 1 then 1 else 0)

/-- Pin the public statement to the literal ordered substitution, normalized
physical lengths, both oriented run sizes and the typed terminal. -/
example (k t : ℕ) (hk : 4 ≤ k) (α h β : ℝ)
    (hpos : ∀ a, 0 < literalLengths α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (literalLengths α h) (literalSigma k t a) =
      β * literalLengths α h a) (source : Packet)
    (hlo : 1 - (runSize k t source.bottom : ℝ) ≤ literalGap (literalLengths α h) β source)
    (hhi : literalGap (literalLengths α h) β source ≤ (runSize k t source.top : ℝ)-1) :
    Relation.ReflTransGen (InteriorStep (literalSigma k t) (literalLengths α h))
      source ⟨2, 2, ![0, 0, 0]⟩ :=
  minus_class_a_run_gap_path k t hk α h β hpos hβ hscale source hlo hhi

/-- A genuine strict RUN/RUN two-cycle with constant positive radius.
This checks that the radius is for selected edges, rather than all edges. -/
theorem alternating_cycle (α h β : ℝ) (hpos : ∀ a, 0 < lengths α h a)
    (hβ : 0 < β) (hβn : β = 9+α) (hβh : β*h = 1) (hβa : β*α = 3-2*h)
    (hα : 0 ≤ α) (hh : 0 < h) (hK : (1-α-2*h)*(β+1) = 5) :
    InteriorStep (ClassAZeroDefectEscape.sigma 7 9) (lengths α h)
      (yyPacket 1 (-1) 3) (yyPacket (-1) 1 (-3)) ∧
    InteriorStep (ClassAZeroDefectEscape.sigma 7 9) (lengths α h)
      (yyPacket (-1) 1 (-3)) (yyPacket 1 (-1) 3) ∧
    radius 1 (-1) = 1 ∧ radius (-1) 1 = 1 := by
  have hγ : 0 < 1-α-2*h := by
    by_contra! hb
    linarith [mul_nonpos_of_nonpos_of_nonneg hb (show 0 ≤ β+1 by linarith)]
  have hγ1 : 1-α-2*h < 1 := by linarith
  have hmul : β*(1-α-2*h) ≤ 5 := by nlinarith only [hγ, hK]
  have h1 : shift α h 1 (-1) 3 = -(1-α-2*h) := by norm_num [shift]; ring
  have h2 : shift α h (-1) 1 (-3) = 1-α-2*h := by norm_num [shift]; ring
  have hs1 : |β*shift α h 1 (-1) 3| ≤ (7 : ℝ)-2 := by
    rw [h1, abs_mul, abs_of_pos hβ, abs_neg, abs_of_pos hγ]
    exact (show β*(1-α-2*h) ≤ 7-2 by linarith)
  have hs2 : |β*shift α h (-1) 1 (-3)| ≤ (7 : ℝ)-2 := by
    rw [h2, abs_mul, abs_of_pos hβ, abs_of_pos hγ]
    exact (show β*(1-α-2*h) ≤ 7-2 by linarith)
  have ht1 : |shift α h (-1) 1 ((-1 : ℤ)-2*1)| < 1 := by
    norm_num [shift, abs_lt]
    constructor <;> linarith
  have ht2 : |shift α h 1 (-1) ((1 : ℤ)-2*(-1))| < 1 := by
    norm_num [shift, abs_lt]
    constructor <;> linarith
  obtain ⟨_, _, _, _, _, _, e1⟩ := run_to 7 9 (by decide) α h β hpos
    (by norm_num; exact hβn) hβh (by norm_num; exact hβa) 1 (-1) 3 1 hs1 ht1
  obtain ⟨_, _, _, _, _, _, e2⟩ := run_to 7 9 (by decide) α h β hpos
    (by norm_num; exact hβn) hβh (by norm_num; exact hβa) (-1) 1 (-3) (-1) hs2 ht2
  exact ⟨e1.interiorStep, e2.interiorStep, by decide, by decide⟩

/-- Outside the closed run gap, even a strict parent shift can exceed
all genuine RUN/RUN ordinal differences. The model case is q = n. -/
example (n : ℕ) (β : ℝ) (hβ : (n : ℝ) < β) :
    (n : ℝ)/β < 1 ∧ ∀ i j : ℕ, 1 ≤ i → i < n → 1 ≤ j → j < n →
      ¬ |(n : ℝ)+(j : ℝ)-i| < 1 := by
  have hpos : 0 < β := lt_of_le_of_lt (Nat.cast_nonneg _) hβ
  refine ⟨(div_lt_iff₀ hpos).mpr (by simpa), ?_⟩
  intro i j _ hi hj _ habs
  have hi' : (i : ℝ) < n := by exact_mod_cast hi
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  linarith [(abs_lt.mp habs).2]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mod := `PscVerif.ClassARunDescent
  let some index := env.getModuleIdx? mod | throwError "Missing Class-A run descent module"
  let mut declarations : Nat := 0
  for info in env.header.moduleData[index.toNat]!.constants do
    if env.getModuleIdxFor? info.name != some index then continue
    if info.isAxiom then throwError "Local axiom {info.name}"
    for ax in ← Lean.collectAxioms info.name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {info.name}"
    declarations := declarations + 1
  if declarations == 0 then throwError "Empty Class-A run descent module"
  for name in #[``run_to, ``shrinks_new_slot, ``reaches_small_radius, ``parameter_residual_bound,
      ``enters_central_run, ``minus_class_a_run_gap_path, ``alternating_cycle] do
    logInfo m!"Class-A run endpoint {name}: {(← Lean.collectAxioms name).toList}"
  logInfo m!"Class-A run descent audit checked {declarations} owned declarations."

end Psc.ClassARunDescentAudit
