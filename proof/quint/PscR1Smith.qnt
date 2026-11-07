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
