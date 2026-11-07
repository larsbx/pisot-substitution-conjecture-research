// R2 adversarial control: mean-zero bounded displacement need
// not have a zero return. The alternating +/- 1 orbit never hits 0.
module PscR2OrientedAverage {
  var displacement: int
  var cumulative: int
  var samples: int
  var zeroSeen: bool
  var orientation: bool
  var orientedTotal: int

  action init = all {
    displacement' = 1,
    cumulative' = 0,
    samples' = 0,
    zeroSeen' = false,
    orientation' = true,
    orientedTotal' = 0,
  }

  action alternate = all {
    samples < 12,
    displacement' = -displacement,
    cumulative' = cumulative + displacement,
    samples' = samples + 1,
    zeroSeen' = if (displacement == 0) true else zeroSeen,
    orientation' = if (orientation) false else true,
    orientedTotal' = orientedTotal + (if (orientation) displacement else -displacement),
  }

  action step = alternate

  val boundedDisplacement = displacement >= -1 and displacement <= 1
  val boundedCumulative = cumulative >= -1 and cumulative <= 1
  val noZeroWitness = not(zeroSeen)
  val boundedOrientedTotal = orientedTotal >= 0 and orientedTotal <= 12


  // Exact witness: 12 alternating nonzero defects give ordinary sum 0,
  // while their deck-indexed positive scores add to 12. No zero return.
  // This refutes transporting B-prime averaging to a gauge-dependent
  // score without a separately certified coboundary/frequency bridge.
  run meanZeroWithoutReturnTest =
    init.then(12.reps(_ => alternate))
      .expect(cumulative == 0 and orientedTotal == 12 and samples == 12 and (zeroSeen == false))
}
