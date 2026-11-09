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


// Separate exact three-coordinate Tribonacci arithmetic control.
// Transition correction vectors (0,0,0), (-1,0,0), (+1,0,0)
// are independently pinned in tests/test_prefix_ancestry.py.
// This does NOT model full legal, ordered descendant paths.
module PscR1TribonacciArithmetic {
  var phase: int
  var x0: int
  var x1: int
  var x2: int

  action init = all {
    phase' = 0,
    x0' = 1,
    x1' = -1,
    x2' = 0,
  }

  // M = [[1,1,1], [1,0,0], [0,1,0]]
  action step0 = all {
    phase == 0,
    x0' = x0 + x1 + x2,
    x1' = x0,
    x2' = x1,
    phase' = 1,
  }

  action step1 = all {
    phase == 1,
    x0' = x0 + x1 + x2 - 1,
    x1' = x0,
    x2' = x1,
    phase' = 2,
  }

  action step2 = all {
    phase == 2,
    x0' = x0 + x1 + x2 + 1,
    x1' = x0,
    x2' = x1,
    phase' = 0,
  }

  action step = any { step0, step1, step2 }

  val coordinateBox = x0 >= -1 and x0 <= 1 and
    x1 >= -1 and x1 <= 1 and x2 >= -1 and x2 <= 1

  run threeStepActualMatrixCycleTest =
    init.then(step0).then(step1).then(step2)
      .expect(phase == 0 and x0 == 1 and x1 == -1 and x2 == 0)
}
