// An explicitly factored pair of two individually irreducible,
// balanced children: top 01|01, bottom 10|10.
// The only internal balanced return is at their shared boundary (index 2).
// A source germ crossing children must not be mistaken for a return
// strictly inside a child. This is a deterministic **finite control**,
// not a Pisot strict-SCC exclusion or all-source recurrence theorem.
module PscR1ChildBoundary {
  pure val top = List(0, 1, 0, 1)
  pure val bottom = List(1, 0, 1, 0)
  pure def count(w, a) = w.select(x => x == a).length()

  var cut: int
  action init = cut' = 0
  action insideFirstChild = cut' = 1
  action atSharedBoundary = cut' = 2
  action insideSecondChild = cut' = 3
  action step = any { insideFirstChild, atSharedBoundary, insideSecondChild }

  val alignedMassReturn =
    count(top.slice(0, cut), 0) == count(bottom.slice(0, cut), 0) and
    count(top.slice(0, cut), 1) == count(bottom.slice(0, cut), 1)

  val childBoundaryOrNoReturn =
    if (cut == 1 or cut == 3) not(alignedMassReturn) else true

  run firstChildInteriorRejectedTest =
    init.then(insideFirstChild)
      .expect(cut == 1 and not(alignedMassReturn))

  run sharedBalancedBoundaryTest =
    init.then(atSharedBoundary)
      .expect(cut == 2 and alignedMassReturn)

  run secondChildInteriorRejectedTest =
    init.then(insideSecondChild)
      .expect(cut == 3 and not(alignedMassReturn))
}
