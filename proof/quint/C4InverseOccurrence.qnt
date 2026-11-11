// Independent finite controls for literal inverse occurrences and swap counts.
// The tested finite domains are explicit; no compact-domain coverage is asserted.
module C4InverseOccurrenceDefinitions {
  pure def count(w, n, a) = range(0, n).foldl(0, (out, i) => out + (if (w[i] == a) 1 else 0))
  pure def prefix(w, n) = (count(w, n, 0), count(w, n, 1), count(w, n, 2))
  pure def add(x, y) = (x._1 + y._1, x._2 + y._2, x._3 + y._3)
  pure def sub(x, y) = (x._1 - y._1, x._2 - y._2, x._3 - y._3)
  pure def neg(x) = (-x._1, -x._2, -x._3)
  pure def dot(ls, r) = ls[0] * r._1 + ls[1] * r._2 + ls[2] * r._3
  pure def incidence(s, r) = (
    count(s[0], s[0].length(), 0) * r._1 + count(s[1], s[1].length(), 0) * r._2 + count(s[2], s[2].length(), 0) * r._3,
    count(s[0], s[0].length(), 1) * r._1 + count(s[1], s[1].length(), 1) * r._2 + count(s[2], s[2].length(), 1) * r._3,
    count(s[0], s[0].length(), 2) * r._1 + count(s[1], s[1].length(), 2) * r._2 + count(s[2], s[2].length(), 2) * r._3)
  pure def child(s, p, i, j) = (s[p._1][i], s[p._2][j],
    add(incidence(s, p._3), sub(prefix(s[p._1], i), prefix(s[p._2], j))))
  pure def validPosition(w, i) = i >= 0 and i < w.length()
  pure def incoming(s, p, q, i, j) =
    if (validPosition(s[p._1], i) and validPosition(s[p._2], j))
      s[p._1][i] == q._1 and s[p._2][j] == q._2 and
      incidence(s, p._3) == add(q._3, sub(prefix(s[p._2], j), prefix(s[p._1], i)))
    else false
  pure def swap(p) = (p._2, p._1, neg(p._3))
  pure def diagonal(p) = p._1 == p._2 and p._3 == (0, 0, 0)
  pure def positiveLex(r) = r._1 > 0 or (r._1 == 0 and r._2 > 0) or (r._1 == 0 and r._2 == 0 and r._3 > 0)
  pure def canonical(p) = if (p._1 > p._2 or (p._1 == p._2 and positiveLex(p._3))) swap(p) else p
  pure def mass(p, ls) = {
    val d = dot(ls, p._3)
    val left = if (-d > 0) -d else 0
    val right = if (ls[p._1] < ls[p._2] - d) ls[p._1] else ls[p._2] - d
    if (right > left) right - left else 0
  }
  pure def scaled(s, ls, beta) = beta > 0 and ls.indices().forall(a =>
    ls[a] > 0 and dot(ls, prefix(s[a], s[a].length())) == beta * ls[a])
  pure def children(s, p) = range(0, s[p._1].length()).foldl(List(), (out, i) =>
    range(0, s[p._2].length()).foldl(out, (row, j) => row.append(child(s, p, i, j))))

  // Each edge has four fields: parent packet, top index, bottom index, child packet.
  // Equal endpoint pairs at different indices remain distinct entries.
  pure def hasPacket(ps, p) = ps.indices().exists(i => ps[i] == p)
  pure def actualEdges(s, ps) = ps.foldl(List(), (out, p) =>
    range(0, s[p._1].length()).foldl(out, (row, i) =>
      range(0, s[p._2].length()).foldl(row, (es, j) => {
        val q = child(s, p, i, j)
        if (hasPacket(ps, q)) es.append((p, i, j, q)) else es
      })))
  pure def swapEdge(e) = (swap(e._1), e._3, e._2, swap(e._4))
  pure def swapClosed(ps) = ps.indices().forall(i => hasPacket(ps, swap(ps[i])))
  pure def edgeSwapClosed(es) = es.indices().forall(i =>
    es.select(e => e == swapEdge(es[i])).length() == 1)
  pure def representatives(ps) = ps.select(p => p == canonical(p))
  pure def weight(ps, q) = ps.select(p => canonical(p) == q).length()
  pure def outgoing(es, p, q) = es.select(e => e._1 == p and canonical(e._4) == q).length()
  pure def incomingCount(es, p, q) = es.select(e => e._4 == p and canonical(e._1) == q).length()
  pure def uniform(es, ps) = ps.indices().forall(i => representatives(ps).indices().forall(j =>
    outgoing(es, ps[i], representatives(ps)[j]) == outgoing(es, canonical(ps[i]), representatives(ps)[j]) and
    incomingCount(es, ps[i], representatives(ps)[j]) == incomingCount(es, canonical(ps[i]), representatives(ps)[j])))
  pure def weightedTransport(es, ps) = representatives(ps).indices().forall(i => representatives(ps).indices().forall(j =>
    weight(ps, representatives(ps)[i]) * incomingCount(es, representatives(ps)[i], representatives(ps)[j]) ==
      weight(ps, representatives(ps)[j]) * outgoing(es, representatives(ps)[j], representatives(ps)[i])))
  pure def transpose(es, ps) = representatives(ps).indices().forall(i => representatives(ps).indices().forall(j =>
    incomingCount(es, representatives(ps)[i], representatives(ps)[j]) == outgoing(es, representatives(ps)[j], representatives(ps)[i])))

  pure val binaryImages = Set(List(0, 0), List(0, 1), List(1, 0), List(1, 1))
  pure val offsets = Set(-2, -1, 0, 1, 2)
  pure val lengths = List(1, 1, 1)
  pure val strictSigma = List(List(1), List(0, 1, 2), List(1))
  pure val strictLengths = List(1, 2, 1)
  pure val strictCarrier = List(
    (List(0, 1), List(1, 0)), (List(1, 0), List(0, 1)),
    (List(1, 2), List(2, 1)), (List(2, 1), List(1, 2)))
  pure def marks(pair) = range(0, pair._1.length()).foldl(List(), (out, i) =>
    range(0, pair._2.length()).foldl(out, (row, j) => row.append(
      (pair._1[i], pair._2[j], sub(prefix(pair._1, i), prefix(pair._2, j))))))
  pure val strictStates = strictCarrier.foldl(List(), (out, p) => out.concat(marks(p)))
    .select(p => mass(p, strictLengths) > 0)
  pure def selected(mask, i) = (mask / (2^i)) % 2 == 1
  pure def strictSubset(mask) = strictStates.select(p => representatives(strictStates).indices().exists(i =>
    selected(mask, i) and canonical(p) == representatives(strictStates)[i]))
  pure val mixedSigma = List(List(0, 0), List(0, 0), List(0, 0))
  pure val mixedStates = List((0, 1, (0, 0, 0)), (1, 0, (0, 0, 0)), (0, 0, (0, 0, 0)))
  pure val leakingSigma = List(List(0, 0), List(1, 1), List(2, 2))
  pure val leakingStates = List((0, 1, (0, 0, 0)), (1, 0, (0, 0, 0)))
  pure def boundedInverseClosed(s, ps) = ps.indices().forall(k =>
    0.to(2).forall(a => 0.to(2).forall(b => offsets.forall(x => offsets.forall(y => offsets.forall(z =>
      0.to(1).forall(i => 0.to(1).forall(j => {
        val p = (a, b, (x, y, z))
        not(incoming(s, p, ps[k], i, j)) or hasPacket(ps, p)
      }))))))))
  pure def positiveForwardClosed(s, ps) = ps.indices().forall(k => {
    val cs = children(s, ps[k])
    cs.indices().forall(i => mass(cs[i], lengths) == 0 or hasPacket(ps, cs[i]))
  })
}

module C4InverseOccurrence {
  import C4InverseOccurrenceDefinitions.*
  var active: bool
  action init = active' = true

  run domainCountTest = init.expect(all {
    active, binaryImages.size() == 4, offsets.size() == 5,
    4 * 4 * 2 * 2 * 5 * 5 * 2 * 2 == 6400,
    strictStates.length() == 12, representatives(strictStates).length() == 6,
    0.to(63).map(mask => strictSubset(mask)).size() == 64,
  })

  run literalInverseIdentityTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    0.to(1).forall(a => 0.to(1).forall(b => offsets.forall(x => offsets.forall(y =>
      0.to(1).forall(i => 0.to(1).forall(j => {
        val p = (a, b, (x, y, 0))
        incoming(s, p, child(s, p, i, j), i, j)
      }))))))
  })))

  run incomingMarkGuardsTest = init.expect({
    val p = (0, 1, (1, -1, 0))
    val q = child(strictSigma, p, 0, 1)
    all {
      q == (1, 1, (-2, 0, -1)), incoming(strictSigma, p, q, 0, 1),
      not(incoming(strictSigma, p, (0, q._2, q._3), 0, 1)),
      not(incoming(strictSigma, p, q, -1, 1)),
      not(incoming(strictSigma, p, q, 0, 3)),
      not(incoming(strictSigma, p, q, 0, 0)),
    }
  })

  run swappedLiteralDigitsTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    0.to(1).forall(a => 0.to(1).forall(b => offsets.forall(x => offsets.forall(y =>
      0.to(1).forall(i => 0.to(1).forall(j => {
        val p = (a, b, (x, y, 0))
        val e = (p, i, j, child(s, p, i, j))
        all {
          swapEdge(swapEdge(e)) == e,
          swapEdge(e)._2 == j, swapEdge(e)._3 == i,
          swapEdge(e)._4 == child(s, swap(p), j, i),
          incoming(s, swap(p), swapEdge(e)._4, j, i),
        }
      }))))))
  })))

  run interiorPullbackTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    scaled(s, lengths, 2) and 0.to(1).forall(a => 0.to(1).forall(b =>
      offsets.forall(x => offsets.forall(y => 0.to(1).forall(i => 0.to(1).forall(j => {
        val p = (a, b, (x, y, 0))
        mass(child(s, p, i, j), lengths) == 0 or mass(p, lengths) > 0
      }))))))
  })))

  run diagonalInteriorDescendantsTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    0.to(1).forall(a => 0.to(1).forall(i => 0.to(1).forall(j => {
      val q = child(s, (a, a, (0, 0, 0)), i, j)
      mass(q, lengths) == 0 or (i == j and diagonal(q))
    })))
  })))

  run boundaryDiagonalCountercontrolTest = init.expect({
    val p = (0, 0, (0, 0, 0))
    val q = child(mixedSigma, p, 0, 1)
    all {
      diagonal(p), incoming(mixedSigma, p, q, 0, 1),
      q == (0, 0, (-1, 0, 0)), mass(q, lengths) == 0, not(diagonal(q)),
      mass((0, 1, (1, 0, 0)), lengths) == 0,
    }
  })

  run wrongScalingPullbackCountercontrolTest = init.expect({
    val wrong = List(2, 1, 1)
    val p = (0, 0, (2, 0, -2))
    val q = child(strictSigma, p, 0, 0)
    all {
      not(scaled(strictSigma, wrong, 2)), scaled(strictSigma, strictLengths, 2),
      incoming(strictSigma, p, q, 0, 0),
      mass(p, wrong) == 0, mass(q, wrong) == 1,
      mass(p, strictLengths) == 1, mass(q, strictLengths) == 2,
    }
  })

  run swapFixedIffDiagonalTest = init.expect(0.to(1).forall(a => 0.to(1).forall(b =>
    offsets.forall(x => offsets.forall(y => {
      val p = (a, b, (x, y, 0))
      (swap(p) == p) == diagonal(p) and swap(swap(p)) == p
    })))))

  run scalarZeroIsNotFixedTest = init.expect({
    val p = (0, 0, (1, -1, 0))
    all { dot(lengths, p._3) == 0, mass(p, lengths) == 1, not(diagonal(p)), swap(p) != p }
  })

  // All 1600 bounded parent inputs and their 16 two-step digit histories.
  run finiteTwoStepAncestryTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    0.to(1).forall(a => 0.to(1).forall(b => offsets.forall(x => offsets.forall(y => {
      val p = (a, b, (x, y, 0))
      val cs = children(s, p)
      cs.indices().forall(i => {
        val q = cs[i]
        val ds = children(s, q)
        ds.indices().forall(j => {
          val r = ds[j]
          mass(r, lengths) == 0 or (mass(q, lengths) > 0 and mass(p, lengths) > 0 and
            (diagonal(r) or (not(diagonal(p)) and not(diagonal(q)) and swap(p) != p and swap(q) != q)))
        })
      })
    }))))
  })))

  run actualFreeDomainSwapCountsTest = init.expect({
    val es = actualEdges(strictSigma, strictStates)
    all {
      es.length() > 0, swapClosed(strictStates), edgeSwapClosed(es),
      strictStates.indices().forall(i => not(diagonal(strictStates[i]))),
      representatives(strictStates).indices().forall(i => weight(strictStates, representatives(strictStates)[i]) == 2),
      uniform(es, strictStates), weightedTransport(es, strictStates), transpose(es, strictStates),
      es.indices().forall(i => incoming(strictSigma, es[i]._1, es[i]._4, es[i]._2, es[i]._3)),
    }
  })

  run allSwapClosedSubdomainsTest = init.expect(0.to(63).forall(mask => {
    val ps = strictSubset(mask)
    val es = actualEdges(strictSigma, ps)
    swapClosed(ps) and edgeSwapClosed(es) and uniform(es, ps) and weightedTransport(es, ps) and transpose(es, ps)
  }))

  run missingSwapEdgeCountercontrolTest = init.expect({
    val es = actualEdges(strictSigma, strictStates)
    val broken = es.select(e => e != es[0])
    all {
      edgeSwapClosed(es), uniform(es, strictStates),
      broken.length() == es.length() - 1,
      not(edgeSwapClosed(broken)), not(uniform(broken, strictStates)),
    }
  })

  run actualMixedOrbitWeightsTest = init.expect({
    val es = actualEdges(mixedSigma, mixedStates)
    val free = mixedStates[0]
    val fixed = mixedStates[2]
    all {
      es.length() == 6, swapClosed(mixedStates), edgeSwapClosed(es), uniform(es, mixedStates),
      weight(mixedStates, free) == 2, weight(mixedStates, fixed) == 1,
      outgoing(es, free, fixed) == 2, incomingCount(es, fixed, free) == 4,
      weightedTransport(es, mixedStates), not(transpose(es, mixedStates)),
    }
  })

  run repeatedOccurrenceIdentityTest = init.expect({
    val es = actualEdges(mixedSigma, mixedStates)
    val p = mixedStates[0]
    val selectedEdges = es.select(e => e._1 == p)
    val endpoints = selectedEdges.foldl(Set(), (out, e) => out.union(Set((e._1, e._4))))
    all {
      selectedEdges.length() == 2, endpoints.size() == 1,
      selectedEdges[0]._2 == 0, selectedEdges[0]._3 == 0,
      selectedEdges[1]._2 == 1, selectedEdges[1]._3 == 1,
      selectedEdges[0]._4 == selectedEdges[1]._4,
      outgoing(es, p, mixedStates[2]) == 2,
    }
  })

  run nonSwapClosedDomainCountercontrolTest = init.expect({
    val ps = List(mixedStates[0], mixedStates[2])
    val es = actualEdges(mixedSigma, ps)
    all { not(swapClosed(ps)), not(edgeSwapClosed(es)), weight(ps, mixedStates[0]) == 1 }
  })

  run inverseClosedForwardLeakTest = init.expect({
    val p = leakingStates[0]
    val cs = children(leakingSigma, p)
    val es = actualEdges(leakingSigma, leakingStates)
    all {
      scaled(leakingSigma, lengths, 2), swapClosed(leakingStates), edgeSwapClosed(es),
      boundedInverseClosed(leakingSigma, leakingStates), not(positiveForwardClosed(leakingSigma, leakingStates)),
      es.length() == 2, cs.length() == 4,
      cs[0] == p, cs[3] == (0, 1, (1, -1, 0)), not(hasPacket(leakingStates, cs[3])),
      cs.foldl(0, (out, q) => out + mass(q, lengths)) == 2,
      cs.select(q => hasPacket(leakingStates, q)).foldl(0, (out, q) => out + mass(q, lengths)) == 1,
      mass(cs[3], lengths) == 1,
    }
  })
}
