import PscVerif.BHDiagonalCertificate
import PscVerif.BHDiagonalDescent
import PscVerif.BHDiagonalAxis
import PscVerif.BHDiagonalClassification
import Lean.Util.CollectAxioms

open Psc.OccurrenceTransport Psc.BHNearDiagonalLiteral Psc.BHNearDiagonalDescent

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β)
    (cert : Psc.BHDiagonalCertificate.RankedRegion r β) (x y z : ℤ)
    (hm : (z,y) ∈ cert.carrier) (hc : Central r r β (runPacket x y z)) :
    ∃ q : Packet,
      Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
        (runPacket x y z) q ∧
      Central r r β q ∧ Psc.BHDiagonalCertificate.Small r (q.delta 2, q.delta 1) :=
  Psc.BHDiagonalCertificate.ranked_region_reaches_small h cert x y z hm hc

example {r : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family r β) (x z : ℤ)
    (hc : Central r r β (runPacket x 0 z)) (hz : 1 ≤ z) (hzr : z < (r : ℤ)) :
    Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
      (runPacket x 0 z) Psc.BHDiagonalLiteral.zero00 ∨
    ∃ q : Packet,
      Relation.ReflTransGen (InteriorStep (sigma r r) (lengths r β))
        (runPacket x 0 z) q ∧ Central r r β q ∧
      energy (β-r) (r/β) (q.delta 2) (q.delta 1) < energy (β-r) (r/β) z 0 :=
  Psc.BHDiagonalAxis.positive_axis_progress h x z hc hz hzr

example {q : ℕ} {β : ℝ} (h : Psc.BHDiagonalLiteral.Family (3*q) β) (x : ℤ)
    (hc : Central (3*q) (3*q) β (runPacket x q ((q : ℤ)-1))) :
    Relation.ReflTransGen (InteriorStep (sigma (3*q) (3*q)) (lengths (3*q) β))
      (runPacket x q ((q : ℤ)-1))
      (runPacket (-(q : ℤ)+(3*q : ℕ)*(q : ℤ)) (1-(q : ℤ)) (-(q : ℤ))) ∧
      Central (3*q) (3*q) β
        (runPacket (-(q : ℤ)+(3*q : ℕ)*(q : ℤ)) (1-(q : ℤ)) (-(q : ℤ))) :=
  Psc.BHDiagonalDescent.first_pair_literal_path h x hc

example {s u c k z y : ℝ} (q : ℤ)
    (hs : 4 ≤ s) (hu : 0 < u) (hu' : u < 1/12)
    (hc : 0 ≤ c) (hc' : c < 1/3) (hratio : (s+1/3)*u < 3/8)
    (hy : y = s+((q : ℝ)-c)/3) (hylo : s-3/2 < y)
    (hk0 : 0 ≤ k) (hkhi : k < s+1) (hk : k = z+1+y*u-(q : ℝ)*s)
    (hnondec : 0 ≤ Psc.BHDiagonalClassification.change k 1 z y) : q = 0 :=
  Psc.BHDiagonalClassification.congruence_zero_of_nondec q hs hu hu' hc hc'
    hratio hy hylo hk0 hkhi hk hnondec

open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let allowed := #[`propext, `Classical.choice, `Quot.sound]
    let endpoints := #[
      `Psc.BHNearDiagonalLiteral.literal_rounding_step_of_runFamily,
      `Psc.BHNearDiagonalLiteral.central_hits_zero,
      `Psc.BHDiagonalLiteral.literal_rounding_step,
      `Psc.BHDiagonalLiteral.unit_injection_hits_labelled_zero,
      `Psc.BHDiagonalLiteral.central_zero_pair_step,
      `Psc.BHDiagonalLiteral.not_near_diagonal_window,
      `Psc.BHDiagonalLiteral.saturation_not_central,
      `Psc.BHDiagonalLiteral.zero12_not_labelled,
      `Psc.BHDiagonalCertificate.ranked_region_reaches_small,
      `Psc.BHDiagonalCertificate.projected_zero_is_not_full_zero,
      `Psc.BHDiagonalDescent.family_block_parameters,
      `Psc.BHDiagonalDescent.first_pair_literal_path,
      `Psc.BHDiagonalDescent.first_pair_decreases,
      `Psc.BHDiagonalDescent.second_pair_literal_path,
      `Psc.BHDiagonalDescent.second_pair_decreases,
      `Psc.BHDiagonalAxis.positive_axis_progress,
      `Psc.BHDiagonalClassification.congruence_zero_of_nondec,
      `Psc.BHDiagonalClassification.nonintegral_congruence_control]
    for name in endpoints do
      let some info := env.find? name | throwError "Missing endpoint {name}"
      unless info.isTheorem do throwError "Not a theorem: {name}"
      for ax in ← collectAxioms name do
        unless allowed.contains ax do throwError "Unexpected axiom in {name}: {ax}"
      Lean.Core.liftIOCore <| IO.println s!"PSC_BH_DIAGONAL_ENDPOINT\t{name}"
    for mod in #[`PscVerif.BHNearDiagonalLiteral, `PscVerif.BHDiagonalLiteral,
      `PscVerif.BHDiagonalCertificate, `PscVerif.BHDiagonalDescent,
      `PscVerif.BHDiagonalAxis, `PscVerif.BHDiagonalClassification] do
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
      Lean.Core.liftIOCore <| IO.println s!"PSC_BH_DIAGONAL_MODULE\t{mod}\t{declarations}\t{theorems}"
    Lean.Core.liftIOCore <| IO.println "PSC_BH_DIAGONAL_AUDIT_COMPLETE\t18\t6"
