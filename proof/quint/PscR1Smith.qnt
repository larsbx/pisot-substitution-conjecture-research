// R1F exact scalar integer-membership negative control.
// 4x = 2 has no integer solution. Modulo 2 it is 0=0 (satisfiable),
// but modulo 4 it is 0=2 (unsatisfiable). Every residue is checked.
//
// This is a Smith/prime-power **test fixture**, not an actual
// substitution occurrence cycle or a proof of any PSC universal gate.
module PscR1SmithModFour {
  var residue: int

  action init = residue' = 0
  action choose0 = residue' = 0
  action choose1 = residue' = 1
  action choose2 = residue' = 2
  action choose3 = residue' = 3
  action step = any { choose0, choose1, choose2, choose3 }

  val canonicalF4 = residue >= 0 and residue < 4
  val modTwoSolvable = ((4 * residue) % 2) == (2 % 2)
  val modFourRefuses = ((4 * residue) % 4) != (2 % 4)
  val integerSmallRefuses = (4 * residue) != 2

  run residue0Test =
    init.then(choose0).expect(residue == 0 and modTwoSolvable and modFourRefuses)
  run residue1Test =
    init.then(choose1).expect(residue == 1 and modTwoSolvable and modFourRefuses)
  run residue2Test =
    init.then(choose2).expect(residue == 2 and modTwoSolvable and modFourRefuses)
  run residue3Test =
    init.then(choose3).expect(residue == 3 and modTwoSolvable and modFourRefuses)
}

// Odd prime example: x=2 solves 4x=2 modulo 3, but not over integers.
module PscR1SmithModThree {
  var residue: int

  action init = residue' = 2
  action stayAtTwo = residue' = 2
  action step = stayAtTwo

  val canonicalF3 = residue >= 0 and residue < 3
  val modThreeSolution = ((4 * residue) % 3) == (2 % 3)

  run oddPrimeHasSolutionTest =
    init.then(stayAtTwo).expect(residue == 2 and modThreeSolution)
}


// Independent arithmetic for a concrete integer Smith certificate of
// A=I-M, M=[[1,1,1],[1,0,0],[0,1,0]], U*A*V=diag(1,1,2).
// The Lean theorem must establish universal exact matrix equalities;
// these bounded Quint tests cover selected basis and sign controls.
module PscR1SmithTribonacciMatrix {
  var x0: int
  var x1: int
  var x2: int

  action init = all { x0' = 0, x1' = 0, x2' = 0 }
  action e0 = all { x0' = 1, x1' = 0, x2' = 0 }
  action e1 = all { x0' = 0, x1' = 1, x2' = 0 }
  action e2 = all { x0' = 0, x1' = 0, x2' = 1 }
  action negative = all { x0' = -1, x1' = 1, x2' = -1 }
  action step = any { e0, e1, e2, negative }

  // V*y
  val v0 = x0 + x1 - x2
  val v1 = x1 - x2
  val v2 = x2

  // A*(V*y)
  val a0 = -v1 - v2
  val a1 = -v0 + v1
  val a2 = -v1 + v2

  // U*A*V*y
  val uav0 = -a1
  val uav1 = -a0
  val uav2 = -a0 + a2

  val exactSmithDiagonal =
    uav0 == x0 and uav1 == x1 and uav2 == 2 * x2
  val finiteTestBox =
    x0 >= -1 and x0 <= 1 and
    x1 >= -1 and x1 <= 1 and
    x2 >= -1 and x2 <= 1

  run smithE0Test = init.then(e0)
    .expect(exactSmithDiagonal and x0 == 1)
  run smithE1Test = init.then(e1)
    .expect(exactSmithDiagonal and x1 == 1)
  run smithE2Test = init.then(e2)
    .expect(exactSmithDiagonal and x2 == 1)
  run smithSignedTest = init.then(negative)
    .expect(exactSmithDiagonal and x0 == -1 and x2 == -1)
}


// First actual substitution-specific integer-membership decision:
// proper source-image prefixes of 0->01,1->02,2->0 yield
// delta in {-1,0,1} on the first letter coordinate.
// The exact Smith transforms of I-M give U*(delta*e0)=(0,-delta,-delta),
// with diagonal (1,1,2), so integer membership holds iff 2 | delta.
//
// This tests only the local **period-one** candidate equation, not
// whether a full source-compatible strict occurrence cycle exists.
module PscR1SmithTribonacciParity {
  var delta: int

  action init = delta' = 0
  action negativeDigit = delta' = -1
  action zeroDigit = delta' = 0
  action positiveDigit = delta' = 1
  action step = any { negativeDigit, zeroDigit, positiveDigit }

  val allowedProperPrefixDigit = delta >= -1 and delta <= 1
  val transformed0 = 0
  val transformed1 = -delta
  val transformed2 = -delta
  val smithIntegral = transformed2 % 2 == 0
  val onlyZeroPasses = smithIntegral == (delta == 0)

  run negativeDigitRejectedTest = init.then(negativeDigit)
    .expect(delta == -1 and not(smithIntegral) and onlyZeroPasses)
  run zeroDigitAcceptedTest = init.then(zeroDigit)
    .expect(delta == 0 and smithIntegral and onlyZeroPasses)
  run positiveDigitRejectedTest = init.then(positiveDigit)
    .expect(delta == 1 and not(smithIntegral) and onlyZeroPasses)
}
