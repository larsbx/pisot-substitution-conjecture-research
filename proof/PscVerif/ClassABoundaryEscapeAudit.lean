import PscVerif.ClassABoundaryEscape
import Lean.Util.CollectAxioms

namespace Psc.ClassABoundaryEscapeAudit

open Psc.Reduction Psc.Descendants Psc.OccurrenceNewborn Psc.OccurrenceTransport Psc.OccurrenceMass
  Psc.ClassAZeroDefectEscape Psc.ClassARunDescent Psc.ClassABoundaryEscape Matrix

private def literalSigma (k t : ℕ) (a : Fin 3) : Word :=
  [if a = 1 then 1 else 0] ++
    List.replicate (if a = 0 then (k+t+3)+(k+2*t+5) else
      if a = 1 then k+t+3 else (k+t+3)-1) 2 ++ [if a = 2 then 1 else 0]

/-- Independently bind the unconditional endpoint to the literal ordered
words, irreducible balanced blocks and the terminal ChildNC relation. -/
example (k t : ℕ) (hk : 4 ≤ k) (T : WordPair) (hT : IsBlock T) :
    ∃ U : WordPair, Relation.ReflTransGen (ChildNC (literalSigma k t)) T U ∧ U.1 = U.2 :=
  minus_class_a_all_blocks k t hk T hT

private def L (α h : ℝ) : Fin 3 → ℝ := ![2+α-h,1+h,1]

/-- The packet endpoint covers every strictly overlapping integral packet,
with only positive exact normalized scaling as input. -/
example (k t : ℕ) (hk : 4 ≤ k) (α h β : ℝ) (hpos : ∀ a, 0 < L α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (L α h) (literalSigma k t a) = β * L α h a)
    (p : Packet) (hp : p.Interior (L α h)) :
    Relation.ReflTransGen (InteriorStep (literalSigma k t) (L α h))
      p ⟨2,2,![0,0,0]⟩ :=
  minus_class_a_strict_path k t hk α h β hpos hβ hscale p hp

/-- Pin the smaller-parameter result to the same original packets and to
explicit integer coordinates, including the third-slot bound. -/
example (k t : ℕ) (hn : 7 ≤ k+t+3) (α h β : ℝ) (hpos : ∀ a, 0 < L α h a) (hβ : 0 < β)
    (hscale : ∀ a, physicalLength (L α h) (literalSigma k t a) = β * L α h a)
    (p : Packet) (hp : p.Interior (L α h)) :
    ∃ u v w : ℤ, (k+1)*max u.natAbs v.natAbs ≤ 5 ∧
      (2 ≤ k → (k+1)*max u.natAbs v.natAbs ≤ 4) ∧ w.natAbs ≤ 15 ∧
      |β*((v : ℝ)+(α-h)*u+h*w)| ≤ ((k+t+3 : ℕ) : ℝ)-2 ∧
      Relation.ReflTransGen (InteriorStep (literalSigma k t) (L α h))
        p ⟨2,2,![-u,-w,-(v-2*u-w)]⟩ :=
  minus_class_a_strict_reaches_residual k t hn α h β hpos hβ hscale p hp

private def doubled (a : Fin 3) : Word := [a,a]
private noncomputable def rationalLengths : Fin 3 → ℝ := ![1,5/4,1]
private def halfShift : Packet := ⟨0,0,![1,-1,0]⟩

/-- Literal words with an inflated width of 3/2 have exactly three positive
children of width 1/2 in this example. A strict improvement of the generic
half-tile threshold at that total width would be false. -/
theorem sharp_half_mass :
    (2 : ℝ) * packetMass rationalLengths halfShift = 3/2 ∧
    ∀ i : Fin (doubled halfShift.top).length, ∀ j : Fin (doubled halfShift.bottom).length,
      packetMass rationalLengths (digitPacket doubled halfShift i j) =
        if i.val = 0 ∧ j.val = 1 then 0 else 1/2 := by
  have hscale : ∀ a, physicalLength rationalLengths (doubled a) = 2*rationalLengths a := by
    intro a
    simp [doubled, two_mul]
  have hδ : offset rationalLengths halfShift.delta = -(1/4) := by
    norm_num [offset, dotProduct, Fin.sum_univ_three, rationalLengths, halfShift]
  constructor
  · unfold packetMass
    rw [hδ]
    norm_num [intervalMass, rationalLengths, halfShift]
  · intro i j
    rw [digitPacket_mass _ _ _ hscale, hδ]
    fin_cases i <;> fin_cases j <;>
      norm_num [doubled, halfShift, rationalLengths, intervalMass]

/-- Wide boundary control in the first proved chamber. This `x/x` packet
is outside the run gap, yet a literal edge captures a full unit. -/
theorem wide_boundary_example :
    ∃ α h β : ℝ, ∀ p : Packet, p = packet 0 0 1 (-5) 5 →
      (runLength 7 9 p.top : ℝ)-1 < runOriginShift (lengths α h) β p ∧
      1/2 ≤ packetMass (lengths α h) p ∧
      ∃ q, InteriorStep (sigma 7 9) (lengths α h) p q ∧ 1 ≤ packetMass (lengths α h) q := by
  obtain ⟨α,h,β,hβ,hpos,hscale⟩ := minus_class_a_lengths_exist 4 0
  obtain ⟨hh, ha0, ha1, hβn, hβh, hβa, _⟩ :=
    minus_class_a_length_arithmetic 4 0 α h β hpos hβ hscale
  norm_num at hβn hβa
  have hβ9 : 9 ≤ β := by linarith
  have hh9 : h ≤ 1/9 := by
    nlinarith [mul_le_mul_of_nonneg_right hβ9 hh.le]
  have hαh : h < α := by
    apply (mul_lt_mul_iff_right₀ hβ).mp
    linarith
  have hx2 : 2 ≤ lengths α h 0 := by change 2 ≤ 2+α-h; linarith
  have hx3 : lengths α h 0 < 3 := by change 2+α-h < 3; linarith
  have hcx : lengths α h 1 ≤ lengths α h 0 := by change 1+h ≤ 2+α-h; linarith
  have hhw : 1/2 ≤ 5*h := by
    have h10 : β < 10 := by linarith
    nlinarith [mul_lt_mul_of_pos_right h10 hh]
  let p := packet 0 0 1 (-5) 5
  have hδ : offset (lengths α h) p.delta = -(2+α-6*h) := by
    norm_num [offset, dotProduct, Fin.sum_univ_three, p, packet, lengths]
    ring
  have hshift : 0 ≤ 2+α-6*h := by linarith
  have hmass : packetMass (lengths α h) p = 5*h := by
    unfold packetMass intervalMass
    rw [hδ]
    change max 0 (min (2+α-h) (2+α-h - (-(2+α-6*h))) - max 0 (-(-(2+α-6*h)))) = 5*h
    rw [neg_neg, max_eq_right hshift, min_eq_left (by linarith)]
    rw [max_eq_right (by linarith)]
    ring
  have hu : (runLength 7 9 p.top : ℝ)-1 < runOriginShift (lengths α h) β p := by
    unfold runOriginShift
    rw [hδ]
    simp [runLength, p, packet]
    nlinarith only [hβn, hβh, hβa, hαh]
  have hwide : 1/2 ≤ packetMass (lengths α h) p := hmass ▸ hhw
  refine ⟨α,h,β,?_⟩
  intro s hs
  subst s
  exact ⟨hu,hwide,upper_boundary_full_child 7 9 (by decide) α h β hβ hβ9
    (by norm_num; exact hβn) ha1 hx2 hx3 hcx hscale p hwide hu⟩

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`PscVerif.OccurrenceWidth, `PscVerif.ClassARunDescent,
      `PscVerif.ClassABoundaryEscape] do
    let some index := env.getModuleIdx? mod | throwError "Missing {mod}"
    let mut count : Nat := 0
    for info in env.header.moduleData[index.toNat]!.constants do
      if env.getModuleIdxFor? info.name != some index then continue
      if info.isAxiom then throwError "Local axiom {info.name}"
      for ax in ← Lean.collectAxioms info.name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {info.name}"
      count := count+1
    if count == 0 then throwError "Empty module {mod}"
    logInfo m!"{mod}: checked {count} declarations"
  for name in #[``OccurrenceWidth.child_mass_at_least, ``OccurrenceWidth.reaches_half_mass,
      ``minus_class_a_strict_enters_run_gap, ``minus_class_a_strict_reaches_residual,
      ``minus_class_a_strict_path, ``minus_class_a_lengths_exist, ``minus_class_a_all_blocks,
      ``sharp_half_mass, ``wide_boundary_example] do
    let axs ← Lean.collectAxioms name
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Class-A boundary endpoint {name}: {axs.toList}"

end Psc.ClassABoundaryEscapeAudit
