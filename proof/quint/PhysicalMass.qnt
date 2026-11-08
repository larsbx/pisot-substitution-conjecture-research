// Independent finite model of the physical-mass implication.
// Row i, column j is the inverse occurrence multiplicity i -> j.
// These integer fixtures do not import Lean expressions or PR #515 data.
// Quantified tests enumerate their entire stated finite domains; they are
// not randomized samples and are not a universal theorem about real matrices.
module PhysicalMassDefinitions {
  pure def vertices(t) = 0.to(t.length() - 1)
  pure def mv(t, v) = range(0, t.length()).foldl(List(), (out, i) =>
    out.append(vertices(t).fold(0, (sum, j) => sum + t[i][j] * v[j])))
  pure def tmv(t, h) = range(0, t.length()).foldl(List(), (out, j) =>
    out.append(vertices(t).fold(0, (sum, i) => sum + t[i][j] * h[i])))
  pure def dot(u, v) = 0.to(u.length() - 1)
    .fold(0, (sum, i) => sum + u[i] * v[i])
  pure def nonnegative(v) = 0.to(v.length() - 1).forall(i => v[i] >= 0)
  pure def positive(v) = 0.to(v.length() - 1).forall(i => v[i] > 0)
  pure def allZero(v) = 0.to(v.length() - 1).forall(i => v[i] == 0)
  pure def matrixNonnegative(t) = vertices(t).forall(i => nonnegative(t[i]))
  pure def deficit(t, h, theta) = {
    val columns = tmv(t, h)
    range(0, t.length()).foldl(List(), (out, j) => out.append(theta * h[j] - columns[j]))
  }
  pure def slack(t, v, theta) = {
    val rows = mv(t, v)
    range(0, t.length()).foldl(List(), (out, i) => out.append(rows[i] - theta * v[i]))
  }
  pure def premises(t, h, v, theta) = all {
    matrixNonnegative(t), positive(h), nonnegative(v),
    nonnegative(slack(t, v, theta)), nonnegative(deficit(t, h, theta)),
  }

  // At most n-1 edges suffice for reachability in a graph on n vertices.
  // n rounds are used so the result is already stable (including n=1).
  pure def expand(t, known) = known.union(vertices(t).filter(j =>
    known.exists(i => t[i][j] > 0)))
  pure def closure(t, seeds) = range(0, t.length())
    .foldl(seeds, (known, _) => expand(t, known))
  pure def reaches(t, i, j) = closure(t, Set(i)).contains(j)
  pure def sameScc(t, i, j) = reaches(t, i, j) and reaches(t, j, i)
  // A source SCC has no predecessor outside itself, including transitive ones.
  pure def source(t, i) = vertices(t).forall(j =>
    not(reaches(t, j, i)) or reaches(t, i, j))
  pure def sink(t, i) = vertices(t).forall(j =>
    not(reaches(t, i, j)) or reaches(t, j, i))
  pure def losing(t, e) = vertices(t).filter(i => e[i] > 0)
  pure def sourceLoss(t, e) = vertices(t).forall(i =>
    not(source(t, i)) or vertices(t).exists(j => sameScc(t, i, j) and e[j] > 0))
  pure def sinkLoss(t, e) = vertices(t).forall(i =>
    not(sink(t, i)) or vertices(t).exists(j => sameScc(t, i, j) and e[j] > 0))
  pure def fullRootCoverage(t, roots) = vertices(t).forall(i =>
    closure(t, roots).contains(i))

  pure def consequence(t, h, v, theta) = {
    val e = deficit(t, h, theta)
    val s = slack(t, v, theta)
    all {
      // Conservation uses the transpose, not the row mass.
      dot(h, s) + dot(e, v) == 0,
      not(premises(t, h, v, theta)) or all {
        allZero(s),
        vertices(t).forall(i => e[i] <= 0 or v[i] == 0),
        vertices(t).forall(i => vertices(t).forall(j =>
          v[i] != 0 or t[i][j] <= 0 or v[j] == 0)),
        vertices(t).forall(i => vertices(t).forall(j =>
          v[i] != 0 or not(reaches(t, i, j)) or v[j] == 0)),
        not(sourceLoss(t, e)) or allZero(v),
      },
    }
  }

  pure def matrix2(code) = List(
    List(code % 3, (code / 3) % 3),
    List((code / 9) % 3, (code / 27) % 3))
  pure def vector2(code, base, offset) =
    List(offset + code % base, offset + (code / base) % base)
  pure def graph3(code) = List(
    List(code % 2, (code / 2) % 2, (code / 4) % 2),
    List((code / 8) % 2, (code / 16) % 2, (code / 32) % 2),
    List((code / 64) % 2, (code / 128) % 2, (code / 256) % 2))
  pure def loss3(code) = List(code % 2, (code / 2) % 2, (code / 4) % 2)
  pure def set3(code) = 0.to(2).filter(i => loss3(code)[i] > 0)

  // Independent short-path formula for the three-vertex reachability check.
  pure def shortPath3(t, i, j) = i == j or t[i][j] > 0 or
    0.to(2).exists(k => t[i][k] > 0 and t[k][j] > 0)

  // Literal occurrence IDs are retained. Comparing support alone would lose
  // the distinction between two positions with the same matrix endpoints.
  pure def occurrenceMatrix(occurrences) = range(0, 2).foldl(List(), (rows, i) =>
    rows.append(range(0, 2).foldl(List(), (row, j) =>
      row.append(occurrences.select(o => o._1 == i and o._2 == j).length()))))
  pure def occurrenceSupport(occurrences) = occurrences
    .foldl(Set(), (out, o) => out.union(Set((o._1, o._2))))
  pure def sameOccurrences(expected, supplied) = expected == supplied
}

module PhysicalMassFinite2 {
  import PhysicalMassDefinitions.*
  var active: bool
  action init = active' = true

  pure val matrices = 0.to(80)
  pure val masses = 0.to(3)
  pure val vectors = 0.to(8)
  pure val scales = 0.to(3)

  run directMatrixEntryCalibrationTest = init.expect(all {
    mv(List(List(2, 0), List(0, 0)), List(1, 0)) == List(2, 0),
    tmv(List(List(2, 0), List(0, 0)), List(1, 1)) == List(2, 0),
    deficit(List(List(2, 0), List(0, 0)), List(1, 1), 2) == List(0, 2),
    mv(List(List(0, 1), List(0, 2)), List(1, 1)) == List(1, 2),
    tmv(List(List(0, 1), List(0, 2)), List(1, 1)) == List(0, 3),
    deficit(List(List(0, 1), List(0, 2)), List(1, 1), 2) == List(2, -1),
  })

  run domainCountTest = init.expect(all {
    active, matrices.size() == 81, masses.size() == 4,
    vectors.size() == 9, scales.size() == 4,
    matrices.size() * masses.size() * vectors.size() * scales.size() == 11664,
    matrices.map(c => matrix2(c)).size() == 81,
    masses.map(c => vector2(c, 2, 1)).size() == 4,
    vectors.map(c => vector2(c, 3, 0)).size() == 9,
  })

  // Every one of the 11,664 tuples is checked, including theta=0.
  run exhaustiveNumericalImplicationTest = init.expect(matrices.forall(c =>
    masses.forall(h => vectors.forall(v => scales.forall(theta =>
      consequence(matrix2(c), vector2(h, 2, 1), vector2(v, 3, 0), theta))))))

  // Non-vacuity guards: both accepted source-loss data and a conservative
  // admissible nonzero vector occur in the enumerated domain.
  run acceptedAndConservativeInputsTest = init.expect(all {
    premises(List(List(0, 1), List(0, 0)), List(1, 1), List(0, 0), 2),
    sourceLoss(List(List(0, 1), List(0, 0)), List(2, 1)),
    premises(List(List(2, 1), List(0, 0)), List(1, 1), List(1, 0), 2),
    not(sourceLoss(List(List(2, 1), List(0, 0)), List(0, 1))),
  })
}

module PhysicalMassGraph3 {
  import PhysicalMassDefinitions.*
  var active: bool
  action init = active' = true
  pure val graphs = 0.to(511)
  pure val masks = 0.to(7)

  run graphDomainCountTest = init.expect(all {
    active, graphs.size() == 512, masks.size() == 8,
    graphs.map(c => graph3(c)).size() == 512,
    masks.map(c => set3(c)).size() == 8,
    graphs.size() * masks.size() == 4096,
    graphs.size() * masks.size() * masks.size() == 32768,
  })

  run exactReachabilityTest = init.expect(graphs.forall(c => {
    val t = graph3(c)
    0.to(2).forall(i => 0.to(2).forall(j =>
      reaches(t, i, j) == shortPath3(t, i, j)))
  }))

  run everyVertexHasSourceAncestorTest = init.expect(graphs.forall(c => {
    val t = graph3(c)
    0.to(2).forall(j => 0.to(2).exists(i => source(t, i) and reaches(t, i, j)))
  }))

  // All 512 directed three-vertex graphs (loops included), all eight loss sets.
  run exhaustiveSourceLossCoverageTest = init.expect(graphs.forall(c =>
    masks.forall(mask => {
      val t = graph3(c)
      val e = loss3(mask)
      sourceLoss(t, e) == (closure(t, losing(t, e)) == Set(0, 1, 2))
    })))

  // All graph/loss/known triples, restricted by the antecedent to reachable
  // zero-set overapproximations. A proper stable zero set cannot survive
  // source loss. This quantifies the transition terminal condition.
  run exhaustiveNoPrematureTerminalTest = init.expect(graphs.forall(c =>
    masks.forall(lossMask => masks.forall(knownMask => {
      val t = graph3(c)
      val known = set3(knownMask)
      not(all {
        sourceLoss(t, loss3(lossMask)), set3(lossMask).subseteq(known),
        expand(t, known) == known,
      }) or known == Set(0, 1, 2)
    }))))
}

module PhysicalMassPropagation {
  import PhysicalMassDefinitions.*
  // One losing vertex in the two-vertex source SCC, plus a conservative sink.
  pure val t = List(List(0, 2, 0), List(1, 0, 2), List(0, 0, 0))
  pure val h = List(1, 1, 1)
  pure val theta = 2
  var knownZero: Set[int]
  var steps: int
  action init = all { knownZero' = losing(t, deficit(t, h, theta)), steps' = 0 }
  pure def canPropagate(known, i, j) = known.contains(i) and t[i][j] > 0 and not(known.contains(j))
  action propagate(i, j) = all {
    canPropagate(knownZero, i, j), knownZero' = knownZero.union(Set(j)), steps' = steps + 1,
  }
  action done = all {
    knownZero == Set(0, 1, 2), knownZero' = knownZero, steps' = steps,
  }
  action step = {
    nondet i = 0.to(2).oneOf()
    nondet j = 0.to(2).oneOf()
    any { propagate(i, j), done }
  }
  val invariant = knownZero.subseteq(Set(0, 1, 2)) and knownZero.contains(0) and
    steps == knownZero.size() - 1 and steps <= 2

  run losingSourceInitializationTest = init.expect(all {
    deficit(t, h, theta) == List(1, 0, 0), knownZero == Set(0),
    sourceLoss(t, deficit(t, h, theta)), invariant,
  })
  run forwardZeroPropagationTest = init.then(propagate(0, 1))
    .expect(knownZero == Set(0, 1) and invariant)
    .then(propagate(1, 2)).expect(knownZero == Set(0, 1, 2) and invariant)
    .then(done).expect(steps == 2 and invariant)
  run reverseAndAbsentEdgesRefusedTest = init.expect(all {
    not(canPropagate(knownZero, 1, 0)), not(canPropagate(knownZero, 0, 2)),
    canPropagate(knownZero, 0, 1), invariant,
  })
}

module PhysicalMassAdversarial {
  import PhysicalMassDefinitions.*
  var active: bool
  action init = active' = true

  run conservativeSourceRefusedTest = init.expect({
    val t = List(List(2, 0), List(0, 0))
    val h = List(1, 1)
    val v = List(1, 0)
    all {
      active, premises(t, h, v, 2), deficit(t, h, 2) == List(0, 2),
      source(t, 0), source(t, 1), not(sourceLoss(t, deficit(t, h, 2))),
      not(allZero(v)),
    }
  })

  run losingSinkIsNotLosingSourceTest = init.expect({
    val t = List(List(2, 1), List(0, 0))
    val h = List(1, 1)
    val v = List(1, 0)
    val e = deficit(t, h, 2)
    all {
      premises(t, h, v, 2), e == List(0, 1),
      source(t, 0), not(source(t, 1)), sink(t, 1), sinkLoss(t, e),
      not(sourceLoss(t, e)), not(allZero(v)),
      closure(t, losing(t, e)) == Set(1),
    }
  })

  run omittedRepeatedOccurrenceRefusedTest = init.expect({
    val expected = List((0, 0, 0), (0, 0, 1))
    val supplied = List((0, 0, 0))
    val actual = occurrenceMatrix(expected)
    val fake = occurrenceMatrix(supplied)
    val h = List(1, 1)
    val v = List(1, 0)
    all {
      occurrenceSupport(expected) == occurrenceSupport(supplied),
      not(sameOccurrences(expected, supplied)),
      actual == List(List(2, 0), List(0, 0)),
      fake == List(List(1, 0), List(0, 0)),
      premises(actual, h, v, 2), not(sourceLoss(actual, deficit(actual, h, 2))),
      sourceLoss(fake, deficit(fake, h, 2)),
      not(premises(fake, h, v, 2)), not(allZero(v)),
    }
  })

  run incorrectTransposeRefusedTest = init.expect({
    val t = List(List(0, 1), List(0, 2))
    val h = List(1, 1)
    val v = List(1, 2)
    val wrongDeficit = List(2 * h[0] - mv(t, h)[0], 2 * h[1] - mv(t, h)[1])
    all {
      mv(t, v) == List(2, 4), wrongDeficit == List(1, 0),
      nonnegative(wrongDeficit), sourceLoss(t, wrongDeficit),
      tmv(t, h) == List(0, 3), deficit(t, h, 2) == List(2, -1),
      not(premises(t, h, v, 2)), not(allZero(v)),
    }
  })

  // With correct transpose budget, nonnegative h and source loss everywhere,
  // positivity propagates from losing sources. Thus zero h cannot preserve
  // every other hypothesis. This fixture refutes the intermediate inference
  // weighted-slack=0 => slack=0 when strict mass positivity is omitted.
  run zeroMassBreaksSaturationTest = init.expect({
    val t = List(List(2, 0), List(0, 0))
    val h = List(0, 1)
    val v = List(1, 0)
    val e = deficit(t, h, 1)
    val s = slack(t, v, 1)
    all {
      nonnegative(h), not(positive(h)), nonnegative(e), nonnegative(s),
      e == List(0, 1), s == List(1, 0), dot(h, s) + dot(e, v) == 0,
      not(allZero(s)), not(premises(t, h, v, 1)), not(sourceLoss(t, e)),
    }
  })

  run incompleteRootReachabilityRefusedTest = init.expect({
    val t = List(List(0, 0), List(0, 2))
    val h = List(1, 1)
    val v = List(0, 1)
    val roots = Set(0)
    all {
      premises(t, h, v, 2), deficit(t, h, 2) == List(2, 0),
      closure(t, roots) == Set(0), not(fullRootCoverage(t, roots)),
      roots.forall(i => v[i] == 0), not(allZero(v)),
      not(sourceLoss(t, deficit(t, h, 2))),
    }
  })

  run negativeMatrixEntryRefusedTest = init.expect({
    val t = List(List(0, 1, -1), List(0, 0, 1), List(0, 0, 1))
    val h = List(1, 1, 1)
    val v = List(0, 1, 1)
    val e = deficit(t, h, 1)
    all {
      positive(h), nonnegative(v), not(matrixNonnegative(t)),
      mv(t, v) == v, e == List(1, 0, 0), nonnegative(e), sourceLoss(t, e),
      t[0][1] > 0, v[0] == 0, v[1] > 0,
      not(premises(t, h, v, 1)), not(allZero(v)),
    }
  })

  run signedOverlapRefusedTest = init.expect({
    val t = List(List(0, 0), List(0, 0))
    val h = List(1, 1)
    val v = List(-1, 0)
    val e = deficit(t, h, 1)
    all {
      matrixNonnegative(t), positive(h), not(nonnegative(v)),
      nonnegative(slack(t, v, 1)), nonnegative(e), sourceLoss(t, e),
      not(premises(t, h, v, 1)), not(allZero(v)),
    }
  })
}
