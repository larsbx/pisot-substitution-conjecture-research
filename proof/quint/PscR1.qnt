// R1 adversarial control: finite ancestry can sustain a NONZERO cycle
// through forcing. It must not be confused with a correction-free run.
module PscR1Ancestry {
  var defect: int
  var correction: int

  action init = all {
    defect' = 1,
    correction' = 0,
  }

  action correctionFree = all {
    defect' = 2 * defect,
    correction' = 0,
    defect >= -1,
    defect <= 1,
  }

  // Exact negative control: x = 1 --c=-1--> x = 1
  action forcedCycle = all {
    defect' = 2 * defect - 1,
    correction' = -1,
    defect == 1,
  }

  action step = any { correctionFree, forcedCycle }

  val finiteAncestryBox = defect >= -2 and defect <= 2


  // Deterministic negative witness: forced nonzero ancestry repeats.
  run forcedNonzeroCycleTest =
    init.then(forcedCycle).then(forcedCycle).then(forcedCycle)
      .expect(defect == 1 and correction == -1 and finiteAncestryBox)
}
