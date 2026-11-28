// Independent finite models for the beta-numeration route.
// Elements of Z[sqrt D] are compared exactly through the integer sign of
// u + v*sqrt(D); no floating point or Lean expression is imported.
// Quantified tests enumerate their entire stated finite domains. They are
// finite-domain evidence for the stated boxes and parameters, not universal
// theorems; the universal statements are the Lean modules cited in
// docs/beta-numeration-quint-2026-11-28.md.
module BetaNumerationDefinitions {
  // Sign of u + v*sqrt(D) for D > 0.
  pure def sgn(u: int, v: int, d: int): int =
    if (u >= 0 and v >= 0) (if (u == 0 and v == 0) 0 else 1)
    else if (u <= 0 and v <= 0) -1
    else if (u > 0) (if (u * u > d * v * v) 1 else if (u * u == d * v * v) 0 else -1)
    else (if (u * u > d * v * v) -1 else if (u * u == d * v * v) 0 else 1)

  pure def pairs(lo: int, hi: int): Set[(int, int)] =
    lo.to(hi).fold(Set(), (acc, a) => acc.union(lo.to(hi).map(b => (a, b))))

  pure def closure(step: ((int, int)) => Set[(int, int)], seeds: Set[(int, int)], rounds: int):
      Set[(int, int)] =
    range(0, rounds).foldl(seeds, (known, _) =>
      known.union(known.fold(Set(), (acc, p) => acc.union(step(p)))))

  // ---- Golden base: y = a + b*phi, phi = (1 + sqrt 5)/2, 2y = (2a + b) + b*sqrt 5.
  pure def gNonneg(a: int, b: int): bool = sgn(2 * a + b, b, 5) >= 0
  // 0 <= y <= phi, with phi - y = -a + (1 - b)*phi.
  pure def gInRange(p: (int, int)): bool = gNonneg(p._1, p._2) and gNonneg(-p._1, 1 - p._2)
  // Conjugate c = a + b*(1 - phi) = (a + b) - b*phi; |c| <= phi^2 = 1 + phi.
  pure def gConjSmall(p: (int, int)): bool = all {
    gNonneg(1 - (p._1 + p._2), 1 + p._2),
    gNonneg(1 + p._1 + p._2, 1 - p._2),
  }
  pure val gBox: Set[(int, int)] = pairs(-4, 4)
  pure val gPoints: Set[(int, int)] = gBox.filter(p => gInRange(p))
  // Remainder step y -> phi*y - d in coordinates.
  pure def gStep(p: (int, int), d: int): (int, int) = (p._2 - d, p._1 + p._2)
  pure def gSucc(p: (int, int)): Set[(int, int)] =
    Set(0, 1).map(d => gStep(p, d)).filter(q => gInRange(q))
  pure def gSuccIn(p: (int, int)): Set[(int, int)] = gSucc(p).intersect(gPoints)
  pure def gReach(seeds: Set[(int, int)]): Set[(int, int)] = closure(gSuccIn, seeds, 81)
  pure def gOnCycle(p: (int, int)): bool = gSuccIn(p).exists(q => gReach(Set(q)).contains(p))
  pure val gZero: (int, int) = (0, 0)
  pure val gInv: (int, int) = (-1, 1)
  pure val gOne: (int, int) = (1, 0)
  pure val gPhi: (int, int) = (0, 1)
  pure val gTwoMinusPhi: (int, int) = (2, -1)
  pure val gT: Set[(int, int)] = Set(gZero, gInv, gOne, gPhi)
  pure def gPred(q: (int, int)): Set[(int, int)] = gPoints.filter(p => gSucc(p).contains(q))

  // ---- Metallic carry: beta = (m + sqrt D)/2, D = m^2 + 4, r = beta - m.
  // z = a + b*beta, 2z = (2a + b*m) + b*sqrt D, 2(1 + r) = (2 - m) + sqrt D.
  pure def cIn(m: int, p: (int, int)): bool = all {
    sgn((2 - m) - (2 * p._1 + p._2 * m), 1 - p._2, m * m + 4) >= 0,
    sgn((2 * p._1 + p._2 * m) + (2 - m), p._2 + 1, m * m + 4) >= 0,
  }
  pure def cBox(m: int): Set[(int, int)] = pairs(-(2 * m + 6), 2 * m + 6)
  pure def cStates(m: int): Set[(int, int)] = cBox(m).filter(p => cIn(m, p))
  pure def cStep(m: int, p: (int, int), d: int): (int, int) = (p._2 + d, p._1 + m * p._2)
  pure def digits(m: int): Set[int] = (-m).to(m)
  // Greatest subset in which every state has a successor (bounded rounds).
  pure def cLive(m: int): Set[(int, int)] = {
    val s = cStates(m)
    range(0, s.size()).foldl(s, (live, _) =>
      live.filter(p => digits(m).exists(d => live.contains(cStep(m, p, d)))))
  }
  pure def cReach(m: int): Set[(int, int)] = {
    val live = cLive(m)
    closure(p => digits(m).map(d => cStep(m, p, d)).intersect(live), Set((0, 0)), live.size())
  }
  pure def walk(m: int, ds: List[int]): List[(int, int)] =
    ds.foldl(List((0, 0)), (path, d) => path.append(cStep(m, path[path.length() - 1], d)))
  pure def staysIn(m: int, ds: List[int]): bool = { val s = cStates(m)
    walk(m, ds).foldl(true, (ok, p) => ok and s.contains(p)) }
  pure def sevenStates(m: int): Set[(int, int)] =
    Set((0, 0), (1, 0), (-1, 0), (-m, 1), (1 - m, 1), (m, -1), (m - 1, -1))
}

module GoldenOrbit {
  import BetaNumerationDefinitions.*
  var tick: int
  action init = tick' = 0

  run signCalibrationTest = init.expect(all {
    sgn(1, 0, 5) == 1, sgn(-3, 1, 5) == -1, sgn(-2, 1, 5) == 1,
    sgn(3, -1, 5) == 1, sgn(2, -1, 5) == -1, sgn(0, 0, 5) == 0, sgn(2, -1, 4) == 0,
    gInRange(gInv), gInRange(gPhi), not(gInRange((1, 1))), not(gInRange((-1, 0))),
  })
  run candidateStatesTest = init.expect(
    gPoints.filter(p => gConjSmall(p)) == Set(gZero, gOne, gInv, gPhi, gTwoMinusPhi))
  run cycleStatesTest = init.expect(gPoints.filter(p => gOnCycle(p)) == gT)
  run closedSetTest = init.expect(gT.forall(p => gSucc(p).subseteq(gT)))
  run exactTransitionsTest = init.expect(all {
    gSucc(gZero) == Set(gZero),
    gSucc(gInv) == Set(gOne, gZero),
    gSucc(gOne) == Set(gPhi, gInv),
    gSucc(gPhi) == Set(gPhi),
  })
  run entryTest = init.expect(all {
    gPred(gZero) == Set(gZero, gInv),
    gPred(gPhi) == Set(gOne, gPhi),
  })
  run twoMinusPhiTest = init.expect(all {
    gSucc(gTwoMinusPhi) == Set(gInv),
    not(gOnCycle(gTwoMinusPhi)),
  })
}

module MetallicCarry {
  import BetaNumerationDefinitions.*
  var tick: int
  action init = tick' = 0

  run carryStepCalibrationTest = init.expect(all {
    cStep(1, (0, 0), 1) == (1, 0), cStep(1, (1, 0), -1) == (-1, 1),
    cStep(2, (1, 1), 0) == (1, 3), cIn(1, (0, 0)), not(cIn(1, (2, 0))),
  })
  run everyBoundedStateContinuesTest = init.expect(
    1.to(6).forall(m => cLive(m) == cStates(m)))
  run sevenReachableStatesTest = init.expect(
    1.to(6).forall(m => cReach(m) == sevenStates(m)))
  run collision100Test = init.expect(all {
    staysIn(1, [1, -1, -1, 0, 0, 0]),
    walk(1, [1, -1, -1])[3] == (0, 0),
  })
  run metallicCollisionTest = init.expect(
    // a 0 c ~ (a-1) m (c+1): digit differences (1, -m, -1) return to 0.
    2.to(6).forall(m => staysIn(m, [1, -m, -1, 0, 0]) and walk(m, [1, -m, -1])[3] == (0, 0)))
}

module BetaAdversarial {
  import BetaNumerationDefinitions.*
  var tick: int
  action init = tick' = 0

  // 2 - phi meets the conjugate bound with equality; a stopping proof would admit it.
  run conjugateBoundIsSharpTest = init.expect(all {
    gConjSmall(gTwoMinusPhi),
    sgn(1 - (gTwoMinusPhi._1 + gTwoMinusPhi._2), 1 + gTwoMinusPhi._2, 5) == 0,
  })
  // 1 0^inf against 0^inf: the carry grows and leaves the state set.
  run unboundedCarryRejectedTest = init.expect(all {
    not(staysIn(1, [1, 0, 0, 0, 0, 0])),
    2.to(6).forall(m => not(staysIn(m, [1, 0, 0, 0]))),
  })
  // The greedy-forced digit at 2 - phi is 0; digit 1 leaves [0, phi].
  run forcedDigitTest = init.expect(not(gInRange(gStep(gTwoMinusPhi, 1))))
  // Equal reachable counts are not a vacuous consequence of an empty box.
  run nonVacuousStatesTest = init.expect(1.to(6).forall(m => cStates(m).size() > 7))
}
