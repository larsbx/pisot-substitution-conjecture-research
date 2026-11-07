// R2 adversarial control: mean-zero bounded displacement need
// not have a zero return. The alternating +/- 1 orbit never hits 0.
module PscR2OrientedAverage {
  var displacement: int
  var cumulative: int
  var samples: int
  var zeroSeen: bool

  action init = all {
    displacement' = 1,
    cumulative' = 0,
    samples' = 0,
    zeroSeen' = false,
  }

  action alternate = all {
    samples < 12,
    displacement' = -displacement,
    cumulative' = cumulative + displacement,
    samples' = samples + 1,
    zeroSeen' = if (displacement == 0) true else zeroSeen,
  }

  action step = alternate

  val boundedDisplacement = displacement >= -1 and displacement <= 1
  val boundedCumulative = cumulative >= -1 and cumulative <= 1
  val noZeroWitness = not(zeroSeen)


  // Exact witness: 12 alternating nonzero defects give cumulative sum 0,
  // yet no individual defect is zero.
  run meanZeroWithoutReturnTest =
    init.then(12.reps(_ => alternate))
      .expect(cumulative == 0 and samples == 12 and (zeroSeen == false))
}
