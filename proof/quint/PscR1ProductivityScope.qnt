// Literal binary substitution control. Every cut and ordered factor is
// computed from the words, independently of the Lean finite graph table.
// Characteristic polynomial x(x-2) is reducible: NOT a PIP counterexample.
module PscR1ProductivityScope {
  pure val images = List(List(0, 1), List(1, 0))
  pure val pairs = List(
    (List(0, 0, 1), List(1, 0, 0)), // 0: productive irreducible root
    (List(0, 1), List(1, 0)),       // 1: strict plus
    (List(1, 0), List(0, 1)),       // 2: strict minus
    (List(0), List(0)),             // 3: diagonal zero
    (List(1), List(1))              // 4: diagonal one
  )
  pure def inflate(w) = w.foldl(List(), (out, a) => out.concat(images[a]))
  pure def mass(w) = (w.select(a => a == 0).length(), w.select(a => a == 1).length())
  pure def cuts(u, v) = range(0, u.length() + 1).select(k =>
    mass(u.slice(0, k)) == mass(v.slice(0, k)))
  pure def factors(u, v) = {
    val z = cuts(u, v)
    range(0, z.length() - 1).foldl(List(), (out, j) =>
      out.append((u.slice(z[j], z[j + 1]), v.slice(z[j], z[j + 1]))))
  }
  pure def children(p) = {
    val (u, v) = p
    factors(inflate(u), inflate(v))
  }
  pure val rows = List(List(1, 3, 4, 2), List(1, 2), List(2, 1), List(3, 4), List(4, 3))
  pure def isStrict(s) = s == 1 or s == 2
  pure def isTarget(s) = s == 3 or s == 4

  // Finite successor traversal. The choice of child ordinal is explicit;
  // the root alternatives must never be collapsed to one verdict.
  var current: int
  var enteredStrict: bool
  action init = all { current' = 0, enteredStrict' = false }
  action takeChild(ordinal) = all {
    ordinal >= 0,
    ordinal < rows[current].length(),
    current' = rows[current][ordinal],
    enteredStrict' = (enteredStrict or isStrict(rows[current][ordinal])),
  }
  action step = {
    nondet ordinal = rows[current].indices().oneOf()
    takeChild(ordinal)
  }
  val strictNeverReachesTarget = if (enteredStrict) isStrict(current) and not(isTarget(current)) else true

  run completeLiteralRowsTest = init.expect(all {
    pairs.indices().forall(s => children(pairs[s]) ==
      rows[s].foldl(List(), (out, t) => out.append(pairs[t]))),
    cuts(inflate(List(0,0,1)), inflate(List(1,0,0))) == List(0,2,3,4,6),
  })
  run legalIrreducibleRootTest = init.expect(all {
    inflate(inflate(inflate(List(0)))) == List(0,1,1,0,1,0,0,1),
    inflate(inflate(inflate(List(0)))).slice(5,8) == List(0,0,1),
    inflate(inflate(inflate(List(0)))).slice(4,7) == List(1,0,0),
    cuts(List(0,0,1), List(1,0,0)) == List(0,3),
    mass(List(0,0,1)) == mass(List(1,0,0)),
  })
  run completeStrictClosureTest = init.expect(all {
    children(pairs[1]) == List(pairs[1], pairs[2]),
    children(pairs[2]) == List(pairs[2], pairs[1]),
    rows[1].indices().forall(j => isStrict(rows[1][j])),
    rows[2].indices().forall(j => isStrict(rows[2][j])),
    not(isTarget(1)), not(isTarget(2)),
  })
  run productiveRootDiagonalBranchTest =
    init.then(takeChild(1)).expect(current == 3 and isTarget(current) and not(enteredStrict))
  run productiveRootStrictBranchTest =
    init.then(takeChild(0)).then(takeChild(1)).then(takeChild(1))
      .expect(current == 1 and enteredStrict and strictNeverReachesTarget)
  // An intentionally incomplete edge list would hide the strict branch.
  // This test asserts rejection of that truncated literal factorization.
  run droppedStrictChildrenRejectedTest = init.expect(
    children(pairs[0]) != List(pairs[3], pairs[4]))
}
