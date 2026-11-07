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

  run zeroResidueRejected =
    init.then(chooseZero).expect(x == 0 and noSolution)
  run oneResidueRejected =
    init.then(chooseOne).expect(x == 1 and noSolution)
}
