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


// Source-address refinement control: 0->01, 1->02, 2->0.
// A proper prefix of the image of 0 or 1 may have length 0 or 1;
// a proper prefix of image 2 (one letter) has length zero only.
// All nonempty proper prefixes contribute exactly one symbol 0.
// This model checks source-image *local* constraints, not full
// occurrence-compatible ancestry under repeated desubstitution.
module PscR1LiteralProperPrefixes {
  var topLetter: int
  var bottomLetter: int
  var topOffset: int
  var bottomOffset: int

  action init = all {
    topLetter' = 0, bottomLetter' = 0,
    topOffset' = 0, bottomOffset' = 0,
  }

  // Each of these is a literal valid proper-prefix pair.
  action negativeDigit = all {
    topLetter' = 2, bottomLetter' = 1,
    topOffset' = 0, bottomOffset' = 1,
  }
  action positiveDigit = all {
    topLetter' = 1, bottomLetter' = 2,
    topOffset' = 1, bottomOffset' = 0,
  }
  action zeroDigit = all {
    topLetter' = 2, bottomLetter' = 2,
    topOffset' = 0, bottomOffset' = 0,
  }

  // Deliberately wrong: image(2)=[0] has NO proper prefix of length 1.
  action invalidDigit = all {
    topLetter' = 2, bottomLetter' = 2,
    topOffset' = 1, bottomOffset' = 0,
  }

  action step = any { negativeDigit, positiveDigit, zeroDigit }

  val validLetterPair = topLetter >= 0 and topLetter <= 2
    and bottomLetter >= 0 and bottomLetter <= 2
  val validProperOffsets = topOffset >= 0 and bottomOffset >= 0
    and topOffset < (if (topLetter == 2) 1 else 2)
    and bottomOffset < (if (bottomLetter == 2) 1 else 2)
  val correctionOnE0 = topOffset - bottomOffset
  val correctionBound = correctionOnE0 >= -1 and correctionOnE0 <= 1

  run actualNegativePrefixTest =
    init.then(negativeDigit).expect(
      validLetterPair and validProperOffsets and correctionOnE0 == -1)
  run actualPositivePrefixTest =
    init.then(positiveDigit).expect(
      validLetterPair and validProperOffsets and correctionOnE0 == 1)
  run actualZeroPrefixTest =
    init.then(zeroDigit).expect(
      validLetterPair and validProperOffsets and correctionOnE0 == 0)
  run rejectNonproperPrefixTest =
    init.then(invalidDigit).expect(not(validProperOffsets))
}


// Stronger adversarial model: the period-three defect cycle also
// survives *literal next-letter* and *proper within-image offset*
// transitions at cut-germ level:
//
// g0=(e0, top 0, bottom 0) --offset (0,1)--> g1=(e1,0,1)
// g1=(e1,0,1) --offset (0,1)--> g2=(e2,0,2)
// g2=(e2,0,2) --offset (0,0)--> g0=(e0,0,0).
//
// The source images are 0->01, 1->02, 2->0.
// This still does NOT certify an entire balanced, strictly
// child-closed word pair or compatible multi-level word contexts.
module PscR1ProperCutGerm {
  var phase: int
  var x0: int
  var x1: int
  var x2: int
  var topLetter: int
  var bottomLetter: int
  var topOffset: int
  var bottomOffset: int

  action init = all {
    phase' = 0,
    x0' = 1, x1' = 0, x2' = 0,
    topLetter' = 0, bottomLetter' = 0,
    topOffset' = 0, bottomOffset' = 1,
  }

  action firstProper = all {
    phase == 0,
    topLetter == 0, bottomLetter == 0,
    x0 == 1, x1 == 0, x2 == 0,
    topOffset == 0, bottomOffset == 1,
    x0' = x0 + x1 + x2 - 1,
    x1' = x0,
    x2' = x1,
    topLetter' = 0, bottomLetter' = 1,
    topOffset' = 0, bottomOffset' = 1,
    phase' = 1,
  }

  action secondProper = all {
    phase == 1,
    topLetter == 0, bottomLetter == 1,
    x0 == 0, x1 == 1, x2 == 0,
    topOffset == 0, bottomOffset == 1,
    x0' = x0 + x1 + x2 - 1,
    x1' = x0,
    x2' = x1,
    topLetter' = 0, bottomLetter' = 2,
    topOffset' = 0, bottomOffset' = 0,
    phase' = 2,
  }

  action thirdProper = all {
    phase == 2,
    topLetter == 0, bottomLetter == 2,
    x0 == 0, x1 == 0, x2 == 1,
    topOffset == 0, bottomOffset == 0,
    x0' = x0 + x1 + x2,
    x1' = x0,
    x2' = x1,
    topLetter' = 0, bottomLetter' = 0,
    topOffset' = 0, bottomOffset' = 1,
    phase' = 0,
  }

  action step = any { firstProper, secondProper, thirdProper }

  val allOffsetsProper =
    topOffset >= 0 and bottomOffset >= 0 and
    topOffset < (if (topLetter == 2) 1 else 2) and
    bottomOffset < (if (bottomLetter == 2) 1 else 2)
  val sourceIndexDifferenceOne = x0 + x1 + x2 == 1
  val cutGermOrbit =
    (phase == 0 and x0 == 1 and x1 == 0 and x2 == 0
      and topLetter == 0 and bottomLetter == 0) or
    (phase == 1 and x0 == 0 and x1 == 1 and x2 == 0
      and topLetter == 0 and bottomLetter == 1) or
    (phase == 2 and x0 == 0 and x1 == 0 and x2 == 1
      and topLetter == 0 and bottomLetter == 2)

  run literalProperGermThreeCycleTest =
    init.then(firstProper).then(secondProper).then(thirdProper)
      .expect(phase == 0 and x0 == 1 and x1 == 0 and x2 == 0
        and topLetter == 0 and bottomLetter == 0
        and allOffsetsProper and sourceIndexDifferenceOne
        and cutGermOrbit)
}
