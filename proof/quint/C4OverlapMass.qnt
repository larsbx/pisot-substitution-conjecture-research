// Independent bounded model of actual ordered overlap subdivision.
// Every finite forall is exhausted. Integer controls neither encode all real
// length rows nor identify formal packets with a compact realized overlap.
module C4OverlapMassDefinitions {
  pure def min2(a, b) = if (a < b) a else b
  pure def max2(a, b) = if (a > b) a else b
  pure def overlapLength(a, b, c, d) = {
    val left = max2(a, c)
    val right = min2(b, d)
    if (right > left) right - left else 0
  }
  pure def prefixMass(w, n, ls) = range(0, n).foldl(0, (out, i) => out + ls[w[i]])
  pure def countPrefix(w, n, a) = range(0, n)
    .foldl(0, (out, i) => out + (if (w[i] == a) 1 else 0))
  pure def prefixVector(w, n) = (countPrefix(w, n, 0), countPrefix(w, n, 1), countPrefix(w, n, 2))
  pure def sub3(x, y) = (x._1 - y._1, x._2 - y._2, x._3 - y._3)
  pure def add3(x, y) = (x._1 + y._1, x._2 + y._2, x._3 + y._3)
  pure def dot3(ls, r) = ls[0] * r._1 + ls[1] * r._2 + ls[2] * r._3
  pure def incidence(s, r) = (
    countPrefix(s[0], s[0].length(), 0) * r._1 + countPrefix(s[1], s[1].length(), 0) * r._2 + countPrefix(s[2], s[2].length(), 0) * r._3,
    countPrefix(s[0], s[0].length(), 1) * r._1 + countPrefix(s[1], s[1].length(), 1) * r._2 + countPrefix(s[2], s[2].length(), 1) * r._3,
    countPrefix(s[0], s[0].length(), 2) * r._1 + countPrefix(s[1], s[1].length(), 2) * r._2 + countPrefix(s[2], s[2].length(), 2) * r._3)
  pure def childResidual(s, a, b, r, i, j) =
    add3(incidence(s, r), sub3(prefixVector(s[a], i), prefixVector(s[b], j)))
  pure def packetMass(p, ls) = overlapLength(0, ls[p._1], -dot3(ls, p._3), ls[p._2] - dot3(ls, p._3))
  pure def children(s, p) = range(0, s[p._1].length()).foldl(List(), (out, i) =>
    range(0, s[p._2].length()).foldl(out, (row, j) =>
      row.append((s[p._1][i], s[p._2][j], childResidual(s, p._1, p._2, p._3, i, j)))))
  pure def sumMass(ps, ls) = ps.foldl(0, (out, p) => out + packetMass(p, ls))
  pure def scaledImages(s, ls, beta) = beta >= 0 and ls.indices().forall(a =>
    ls[a] >= 0 and prefixMass(s[a], s[a].length(), ls) == beta * ls[a])
  pure def partitionMass(u, v, ls, displacement) = range(0, u.length()).foldl(0, (out, i) =>
    range(0, v.length()).foldl(out, (row, j) => row + overlapLength(
      prefixMass(u, i, ls), prefixMass(u, i + 1, ls),
      prefixMass(v, j, ls) - displacement, prefixMass(v, j + 1, ls) - displacement)))
  pure def selected(mask, i) = (mask / (2^i)) % 2 == 1
  pure def retainedMass(ps, ls, mask) = ps.indices().filter(i => selected(mask, i))
    .fold(0, (out, i) => out + packetMass(ps[i], ls))
  pure def omittedMass(ps, ls, mask) = ps.indices().filter(i => not(selected(mask, i)))
    .fold(0, (out, i) => out + packetMass(ps[i], ls))

  pure val binaryParts = Set(0, 1).allListsUpTo(2)
  pure val binaryImages = binaryParts.filter(w => w.length() == 2)
  pure val shortLengths = Set(List(0, 0, 0), List(0, 1, 0), List(0, 2, 0),
    List(1, 0, 0), List(1, 1, 0), List(1, 2, 0),
    List(2, 0, 0), List(2, 1, 0), List(2, 2, 0))
  pure val offsets = Set(-2, -1, 0, 1, 2)
  pure val strictSigma = List(List(1), List(0, 1, 2), List(1))
  pure val strictLengths = List(1, 2, 1)
  pure val strictCarrier = List(
    (List(0, 1), List(1, 0)), (List(1, 0), List(0, 1)),
    (List(1, 2), List(2, 1)), (List(2, 1), List(1, 2)))
  pure def actualPackets(pair) = range(0, pair._1.length()).foldl(List(), (out, i) =>
    range(0, pair._2.length()).foldl(out, (row, j) => row.append(
      (pair._1[i], pair._2[j], sub3(prefixVector(pair._1, i), prefixVector(pair._2, j))))))
  pure val strictPackets = strictCarrier.foldl(List(), (out, pair) => out.concat(actualPackets(pair)))

  // Each edge retains a literal list position, even when endpoints repeat.
  pure def fiberSize(labels, i) = labels.select(j => j == i).length()
  pure def outgoing(edges, labels, x, j) = edges.select(e => e._1 == x and labels[e._2] == j).length()
  pure def incoming(edges, labels, x, j) = edges.select(e => e._2 == x and labels[e._1] == j).length()
  pure def forward(edges, labels, representatives) = range(0, representatives.length())
    .foldl(List(), (out, i) => out.append(range(0, representatives.length())
      .foldl(List(), (row, j) => row.append(outgoing(edges, labels, representatives[i], j)))))
  pure def inverse(edges, labels, representatives) = range(0, representatives.length())
    .foldl(List(), (out, i) => out.append(range(0, representatives.length())
      .foldl(List(), (row, j) => row.append(incoming(edges, labels, representatives[i], j)))))
  pure def uniformCounts(edges, labels, representatives) = labels.indices().forall(x => representatives.indices().forall(j =>
    outgoing(edges, labels, x, j) == outgoing(edges, labels, representatives[labels[x]], j) and
    incoming(edges, labels, x, j) == incoming(edges, labels, representatives[labels[x]], j)))
  pure def fiberWeights(labels, representatives) = range(0, representatives.length()).foldl(List(), (out, i) => out.append(fiberSize(labels, i)))
  pure def countCorrespondence(f, t, m) = m.indices().forall(i => m.indices().forall(j =>
    m[i] * t[i][j] == m[j] * f[j][i]))
  pure def rowAction(t, v) = range(0, t.length()).foldl(List(), (rows, i) =>
    rows.append(range(0, t.length()).foldl(0, (out, j) => out + t[i][j] * v[j])))
  pure def transposeAction(t, h) = range(0, t.length()).foldl(List(), (columns, j) =>
    columns.append(range(0, t.length()).foldl(0, (out, i) => out + t[i][j] * h[i])))
  pure def weighted(h, m) = range(0, h.length()).foldl(List(), (out, i) => out.append(m[i] * h[i]))
  pure def forwardDeficit(f, h, beta) = {
    val rows = rowAction(f, h)
    range(0, h.length()).foldl(List(), (out, i) => out.append(beta * h[i] - rows[i]))
  }
  pure def inverseDeficit(t, h, beta) = {
    val columns = transposeAction(t, h)
    range(0, h.length()).foldl(List(), (out, i) => out.append(beta * h[i] - columns[i]))
  }
  pure def graph3(code) = range(0, 3).foldl(List(), (out, i) =>
    range(0, 3).foldl(out, (row, j) =>
      if ((code / (2^(3*i+j))) % 2 == 1) row.append((i, j)) else row))
}

module C4OverlapMass {
  import C4OverlapMassDefinitions.*
  var active: bool
  action init = active' = true

  run domainCountTest = init.expect(all {
    active, binaryParts.size() == 7, binaryImages.size() == 4,
    shortLengths.size() == 9, offsets.size() == 5,
    7 * 7 * 9 * 5 == 2205,
    4 * 4 * 2 * 2 * 5 * 5 == 1600,
    0.to(511).map(c => graph3(c)).size() == 512,
  })

  // Empty words and zero length letters are allowed in this partition domain.
  run finiteIntervalPartitionTest = init.expect(binaryParts.forall(u => binaryParts.forall(v =>
    shortLengths.forall(ls => offsets.forall(d =>
      partitionMass(u, v, ls, d) == overlapLength(0, prefixMass(u, u.length(), ls),
        -d, prefixMass(v, v.length(), ls) - d))))))

  // All 1600 substitution, source-type and residual inputs are evaluated.
  run finiteScaledSubdivisionTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    val ls = List(1, 1, 1)
    scaledImages(s, ls, 2) and 0.to(1).forall(a => 0.to(1).forall(b =>
      offsets.forall(x => offsets.forall(y => {
        val p = (a, b, (x, y, 0))
        sumMass(children(s, p), ls) == 2 * packetMass(p, ls)
      }))))
  })))

  run affineTranslationTest = init.expect(all {
    childResidual(strictSigma, 0, 1, (1, -1, 0), 0, 1) == (-2, 0, -1),
    dot3(strictLengths, childResidual(strictSigma, 0, 1, (1, -1, 0), 0, 1)) == -3,
    2 * dot3(strictLengths, (1, -1, 0)) + prefixMass(strictSigma[0], 0, strictLengths)
      - prefixMass(strictSigma[1], 1, strictLengths) == -3,
  })

  run strictCompleteCarrierConservativeTest = init.expect({
    val support = strictPackets.select(p => packetMass(p, strictLengths) > 0)
      .foldl(Set(), (out, p) => out.union(Set(p)))
    all {
      scaledImages(strictSigma, strictLengths, 2), strictPackets.length() == 16, support.size() == 12,
      strictPackets.indices().forall(i => sumMass(children(strictSigma, strictPackets[i]), strictLengths)
        == 2 * packetMass(strictPackets[i], strictLengths)),
      support.forall(p => {
        val cs = children(strictSigma, p)
        cs.indices().forall(i => packetMass(cs[i], strictLengths) == 0 or support.contains(cs[i]))
      }),
    }
  })

  run occurrenceMultiplicityTest = init.expect({
    val s = List(List(0, 0), List(0, 0), List(0, 0))
    val ls = List(1, 1, 1)
    val p = (0, 1, (0, 0, 0))
    val cs = children(s, p)
    val distinct = cs.foldl(Set(), (out, c) => out.union(Set(c)))
    all {
      cs.length() == 4, cs[0] == cs[3], distinct.size() == 3,
      cs.foldl(List(), (out, c) => out.append(packetMass(c, ls))) == List(1, 0, 0, 1),
      sumMass(cs, ls) == 2,
      distinct.fold(0, (out, c) => out + packetMass(c, ls)) == 1,
      sumMass(cs, ls) == 2 * packetMass(p, ls),
    }
  })

  run boundaryAndDegenerateTest = init.expect({
    val empty = List(List(), List(), List())
    val zeroLength = List(List(0), List(0), List(0))
    all {
      overlapLength(0, 1, 1, 2) == 0, overlapLength(0, 1, 2, 3) == 0,
      overlapLength(0, 0, -1, 1) == 0,
      scaledImages(empty, List(1, 1, 1), 0),
      sumMass(children(empty, (0, 1, (0, 0, 0))), List(1, 1, 1)) == 0,
      scaledImages(zeroLength, List(0, 0, 0), 2),
      sumMass(children(zeroLength, (0, 1, (2, -1, 0))), List(0, 0, 0)) == 0,
    }
  })

  run positiveWrongRowTest = init.expect({
    val ls = List(2, 1, 1)
    val p = (0, 0, (0, -1, 0))
    all {
      ls.indices().forall(a => ls[a] > 0), not(scaledImages(strictSigma, ls, 2)),
      packetMass(p, ls) == 1, sumMass(children(strictSigma, p), ls) == 0,
      sumMass(children(strictSigma, p), ls) != 2 * packetMass(p, ls),
    }
  })

  run omittedOccurrenceBudgetTest = init.expect({
    val s = List(List(0, 0), List(0, 0), List(0, 0))
    val ls = List(1, 1, 1)
    val cs = children(s, (0, 1, (0, 0, 0)))
    all {
      0.to(15).forall(mask => 2 - retainedMass(cs, ls, mask) == omittedMass(cs, ls, mask)),
      retainedMass(cs, ls, 9) == 2, omittedMass(cs, ls, 9) == 0,
      retainedMass(cs, ls, 1) == 1, omittedMass(cs, ls, 1) == 1,
    }
  })

  run literalMixedOrbitCountsTest = init.expect({
    val labels = List(0, 0, 1)
    val representatives = List(0, 2)
    val es = List((0, 2), (1, 2), (2, 2))
    all {
      uniformCounts(es, labels, representatives), fiberWeights(labels, representatives) == List(2, 1),
      forward(es, labels, representatives) == List(List(0, 1), List(0, 1)),
      inverse(es, labels, representatives) == List(List(0, 0), List(2, 1)),
      countCorrespondence(forward(es, labels, representatives), inverse(es, labels, representatives), fiberWeights(labels, representatives)),
    }
  })

  run finiteQuotientCountsTest = init.expect(0.to(511).forall(code => {
    val es = graph3(code)
    val labels = List(0, 0, 1)
    val representatives = List(0, 2)
    not(uniformCounts(es, labels, representatives)) or
      countCorrespondence(forward(es, labels, representatives), inverse(es, labels, representatives), fiberWeights(labels, representatives))
  }))

  run uniformityIsNecessaryTest = init.expect({
    val es = List((0, 2))
    val labels = List(0, 0, 1)
    val representatives = List(0, 2)
    all {
      not(uniformCounts(es, labels, representatives)),
      not(countCorrespondence(forward(es, labels, representatives), inverse(es, labels, representatives), fiberWeights(labels, representatives))),
    }
  })

  run allFixedAndFreeOrbitsTest = init.expect({
    val fixedLabels = List(0, 1)
    val fixedReps = List(0, 1)
    val repeatedEdges = List((0, 1), (0, 1), (1, 1))
    val freeLabels = List(0, 0, 1, 1)
    val freeReps = List(0, 2)
    val freeEdges = List((0, 2), (1, 3), (2, 2), (3, 3))
    val f = forward(freeEdges, freeLabels, freeReps)
    val t = inverse(freeEdges, freeLabels, freeReps)
    all {
      fiberWeights(fixedLabels, fixedReps) == List(1, 1),
      forward(repeatedEdges, fixedLabels, fixedReps) == List(List(0, 2), List(0, 1)),
      inverse(repeatedEdges, fixedLabels, fixedReps) == List(List(0, 0), List(2, 1)),
      uniformCounts(freeEdges, freeLabels, freeReps), fiberWeights(freeLabels, freeReps) == List(2, 2),
      countCorrespondence(f, t, List(2, 2)),
      0.to(1).forall(i => 0.to(1).forall(j => f[i][j] == t[j][i])),
    }
  })

  run transposeOrientationTest = init.expect({
    val f = List(List(1, 1), List(0, 1))
    val t = List(List(1, 0), List(1, 1))
    val h = List(1, 1)
    val m = List(2, 2)
    all {
      countCorrespondence(f, t, m),
      rowAction(t, weighted(h, m)) == List(2, 4),
      transposeAction(t, weighted(h, m)) == List(4, 2),
      forwardDeficit(f, h, 2) == List(0, 1),
      inverseDeficit(t, weighted(h, m), 2) == weighted(forwardDeficit(f, h, 2), m),
    }
  })

  run mixedConservativeWeightedTest = init.expect({
    val f = List(List(0, 1), List(0, 1))
    val t = List(List(0, 0), List(2, 1))
    val h = List(1, 1)
    val m = List(2, 1)
    all {
      countCorrespondence(f, t, m), weighted(h, m) == List(2, 1),
      forwardDeficit(f, h, 1) == List(0, 0),
      inverseDeficit(t, weighted(h, m), 1) == List(0, 0),
      inverseDeficit(t, h, 1) == List(-1, 0),
    }
  })

  run mixedStrictWeightedTest = init.expect({
    val labels = List(0, 1, 1)
    val representatives = List(0, 1)
    val es = List((0, 1), (0, 2), (1, 0), (2, 0))
    val f = forward(es, labels, representatives)
    val t = inverse(es, labels, representatives)
    val h = List(1, 1)
    val m = fiberWeights(labels, representatives)
    all {
      uniformCounts(es, labels, representatives), m == List(1, 2),
      f == List(List(0, 2), List(1, 0)), t == f, countCorrespondence(f, t, m),
      forwardDeficit(f, h, 2) == List(0, 1),
      inverseDeficit(t, weighted(h, m), 2) == List(0, 2),
      inverseDeficit(t, weighted(h, m), 2) == weighted(forwardDeficit(f, h, 2), m),
      inverseDeficit(t, h, 2) == List(1, 0),
    }
  })
}
