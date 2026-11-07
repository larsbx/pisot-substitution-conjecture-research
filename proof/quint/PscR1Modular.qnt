// R1F: finite-field toy, exhaustive explicit F2 residue enumeration.
// A = 0 and b = 1 mod 2: the equation A*x=b has no solution.
// This is NOT an actual Pisot strict-component correction cycle.
module PscR1Modular {
  var x: int

  action init = all { x' = 0 }
  action chooseZero = all { x' = 0 }
  action chooseOne = all { x' = 1 }
  action step = any { chooseZero, chooseOne }

  val residueBound = x == 0 or x == 1
  val noSolution = 0 * x != 1

  run zeroResidueRejectedTest =
    init.then(chooseZero).expect(x == 0 and noSolution)
  run oneResidueRejectedTest =
    init.then(chooseOne).expect(x == 1 and noSolution)
}


// Concrete mod-2 filter for the *actual* Tribonacci incidence matrix
// M = [[1,1,1],[1,0,0],[0,1,0]] and locally admissible proper-prefix
// correction e0. If x2=x1 (row 2 of (I-M)x=e0), then x1+x2 is
// either 0 or 2, never an odd residue. This rejects an integral
// period-one cycle with that digit but NOT all strict source cycles.
module PscR1TribonacciResidues {
  var x1: int
  var x2: int

  action init = all { x1' = 0, x2' = 0 }
  action choose00 = all { x1' = 0, x2' = 0 }
  action choose01 = all { x1' = 0, x2' = 1 }
  action choose10 = all { x1' = 1, x2' = 0 }
  action choose11 = all { x1' = 1, x2' = 1 }
  action step = any { choose00, choose01, choose10, choose11 }

  val residueBounds = (x1 == 0 or x1 == 1) and
    (x2 == 0 or x2 == 1)
  val noE0PeriodOne = x1 != x2 or x1 + x2 != 1

  run tribonacci00Test = init.then(choose00)
    .expect(x1 == 0 and x2 == 0 and noE0PeriodOne)
  run tribonacci01Test = init.then(choose01)
    .expect(x1 == 0 and x2 == 1 and noE0PeriodOne)
  run tribonacci10Test = init.then(choose10)
    .expect(x1 == 1 and x2 == 0 and noE0PeriodOne)
  run tribonacci11Test = init.then(choose11)
    .expect(x1 == 1 and x2 == 1 and noE0PeriodOne)
}


// Exact arithmetic of a locally admissible 3-step correction cycle:
// M e0 - e0 = e1, M e1 - e0 = e2, M e2 = e0.
// This is a **negative control** against claiming that the correction
// alphabet alone prohibits all cycles; it has not been bound to an
// actual strict ordered child occurrence cycle.
module PscR1TribonacciPeriodThree {
  var phase: int
  var x0: int
  var x1: int
  var x2: int

  action init = all {
    phase' = 0, x0' = 1, x1' = 0, x2' = 0,
  }

  action minusOneFirst = all {
    phase == 0,
    phase' = 1,
    x0' = x0 + x1 + x2 - 1,
    x1' = x0,
    x2' = x1,
  }

  action minusOneSecond = all {
    phase == 1,
    phase' = 2,
    x0' = x0 + x1 + x2 - 1,
    x1' = x0,
    x2' = x1,
  }

  action zeroThird = all {
    phase == 2,
    phase' = 0,
    x0' = x0 + x1 + x2,
    x1' = x0,
    x2' = x1,
  }

  action step = any { minusOneFirst, minusOneSecond, zeroThird }

  val unitBasisState = (x0 == 1 and x1 == 0 and x2 == 0)
    or (x0 == 0 and x1 == 1 and x2 == 0)
    or (x0 == 0 and x1 == 0 and x2 == 1)

  run locallyAdmissiblePeriodThreeTest =
    init.then(minusOneFirst).then(minusOneSecond).then(zeroThird)
      .expect(phase == 0 and x0 == 1 and x1 == 0 and x2 == 0
        and unitBasisState)
}
