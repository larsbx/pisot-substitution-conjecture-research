// Source-derived support certificates, independent of the Lean proof terms.
// Tests reconstruct every literal balanced cut and ordered child occurrence.
// No source closure is inferred from a productive root or a sampled walk.
module PscR1SupportCertificate {
  pure def inflate(images, w) = w.foldl(List(), (out, a) => out.concat(images[a]))
  pure def mass(w) = (w.select(a => a == 0).length(), w.select(a => a == 1).length())
  pure def cuts(u, v) = range(0, u.length() + 1).select(k =>
    mass(u.slice(0, k)) == mass(v.slice(0, k)))
  pure def children(images, p) = {
    val (top, bottom) = p
    val u = inflate(images, top)
    val v = inflate(images, bottom)
    val z = cuts(u, v)
    range(0, z.length() - 1).foldl(List(), (out, j) =>
      out.append((u.slice(z[j], z[j + 1]), v.slice(z[j], z[j + 1]))))
  }
  pure def stateOK(p) = {
    val (u, v) = p
    u.length() > 0 and u.length() == v.length() and
      cuts(u, v) == List(0, u.length())
  }
  pure def target(p) = {
    val (u, v) = p
    u.length() == 1 and u == v
  }
  pure def validTableIds(pairs, rows) =
    if (rows.length() != pairs.length()) false else
      rows.indices().forall(s => rows[s].indices().forall(k =>
        rows[s][k] >= 0 and rows[s][k] < pairs.length()))
  pure def rowMatches(images, pairs, rows, s) =
    children(images, pairs[s]) ==
      rows[s].foldl(List(), (out, t) => out.append(pairs[t]))

  pure def graphStrict(pairs, rows, keep) =
    if (not(validTableIds(pairs, rows)) or not(keep.subseteq(pairs.indices()))) false else
      keep.size() > 0 and keep.forall(s => not(target(pairs[s])) and
        rows[s].indices().forall(j => keep.contains(rows[s][j])))

  pure def strictCheck(images, pairs, rows, keep) =
    if (not(graphStrict(pairs, rows, keep))) false else
      keep.forall(s => stateOK(pairs[s]) and rowMatches(images, pairs, rows, s))

  pure def rankCheck(images, pairs, rows, rank) =
    if (not(validTableIds(pairs, rows)) or rank.length() != pairs.length()) false else
      pairs.indices().forall(s =>
        rank[s] >= 0 and stateOK(pairs[s]) and rowMatches(images, pairs, rows, s) and
        (target(pairs[s]) or rows[s].indices().exists(j => rank[rows[s][j]] < rank[s])))

  pure val binaryImages = List(List(0,1), List(1,0))
  pure val binaryPairs = List(
    (List(0,0,1),List(1,0,0)), (List(0,1),List(1,0)),
    (List(1,0),List(0,1)), (List(0),List(0)), (List(1),List(1)))
  pure val binaryRows = List(List(1,3,4,2),List(1,2),List(2,1),List(3,4),List(4,3))
  pure val binaryBad = Set(1,2)
  pure val binaryWrong = Set(0,1,2)
  pure val omittedExits = List(List(1,2),List(1,2),List(2,1),List(3,4),List(4,3))
  pure val reordered = List(List(1,3,4,2),List(2,1),List(2,1),List(3,4),List(4,3))
  pure val duplicated = List(List(1,3,4,2),List(1,2,1),List(2,1),List(3,4),List(4,3))

  // 0->01,1->0: complete four-state literal graph. The first two states
  // form a target-avoiding cycle WITH exits to singleton diagonals.
  pure val fibImages = List(List(0,1),List(0))
  pure val fibPairs = List((List(0,1),List(1,0)), (List(1,0),List(0,1)),
    (List(0),List(0)), (List(1),List(1)))
  pure val fibRows = List(List(2,1),List(2,0),List(2,3),List(2))
  pure val fibRank = List(1,1,0,0)
  pure val fibTruncated = List(List(1),List(0),List(2,3),List(2))

  pure def expand(rows, seen) = seen.union(rows.indices().filter(t =>
    seen.exists(s => rows[s].indices().exists(k => rows[s][k] == t))))
  pure def reach(rows, s) = range(0, rows.length()).foldl(Set(s), (seen, _) => expand(rows, seen))

  var active: bool
  var current: int
  action init = all { active' = true, current' = 0 }
  action avoidTarget = all {
    active,
    current == 0 or current == 1,
    current' = fibRows[current][1],
    active' = active,
  }
  action step = avoidTarget

  run binaryLiteralRowsTest = init.expect(
    binaryPairs.indices().forall(s => rowMatches(binaryImages,binaryPairs,binaryRows,s)))
  run binaryExactStrictSupportTest = init.expect(
    strictCheck(binaryImages,binaryPairs,binaryRows,binaryBad))
  run binaryProductiveRootDoesNotClearSupportTest = init.expect(all {
    reach(binaryRows,0).exists(s => target(binaryPairs[s])),
    not(reach(binaryRows,1).exists(s => target(binaryPairs[s]))),
    not(strictCheck(binaryImages,binaryPairs,binaryRows,binaryWrong)),
  })
  run omittedDiagonalExitsRejectedTest = init.expect(all {
    graphStrict(binaryPairs,omittedExits,binaryWrong),
    not(strictCheck(binaryImages,binaryPairs,omittedExits,binaryWrong)),
  })
  run reorderedOccurrencesRejectedTest = init.expect(
    not(strictCheck(binaryImages,binaryPairs,reordered,binaryBad)))
  run changedMultiplicityRejectedTest = init.expect(
    not(strictCheck(binaryImages,binaryPairs,duplicated,binaryBad)))
  run emptySupportRejectedTest = init.expect(
    not(strictCheck(binaryImages,binaryPairs,binaryRows,Set())))
  run positiveCompleteRankTest = init.expect(all {
    rankCheck(fibImages,fibPairs,fibRows,fibRank),
    fibPairs.indices().forall(s => reach(fibRows,s).exists(t => target(fibPairs[t]))),
  })
  run rankDoesNotRequireAllEdgesDecreaseTest = init.expect(all {
    rankCheck(fibImages,fibPairs,fibRows,fibRank),
    fibRows[0][1] == 1, fibRows[1][1] == 0,
    fibRank[0] == fibRank[1],
  })
  run rankCertificateBadRankRejectedTest = init.expect(
    not(rankCheck(fibImages,fibPairs,fibRows,List(0,0,0,0))))
  run truncatedPositiveCarrierRejectedTest = init.expect(all {
    graphStrict(fibPairs,fibTruncated,Set(0,1)),
    not(strictCheck(fibImages,fibPairs,fibTruncated,Set(0,1))),
    not(rankCheck(fibImages,fibPairs,fibTruncated,fibRank)),
  })
  run productiveTargetAvoidingCycleTest =
    init.then(avoidTarget).then(avoidTarget).then(avoidTarget).then(avoidTarget)
      .expect(current == 0 and not(target(fibPairs[current])) and
        rankCheck(fibImages,fibPairs,fibRows,fibRank))
}
