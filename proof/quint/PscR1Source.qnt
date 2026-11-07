// Literal source-word witnesses for the additional R1F interior-return
// elimination condition. These three-letter words are exact, not
// arbitrary affine vectors. No numerical geometry, randomness or
// source legality for a complete strict descendant SCC is asserted.
module PscR1SourceReturn {
  var top0: int
  var top1: int
  var top2: int
  var bottom0: int
  var bottom1: int
  var bottom2: int

  action init = all {
    top0' = 0, top1' = 0, top2' = 1,
    bottom0' = 0, bottom1' = 1, bottom2' = 0,
  }

  // Balanced but reducible: top=001, bottom=010. For asynchronous
  // source prefix top[:1] vs bottom[:0], the difference is e0 and the
  // bottom next letter is 0. Aligning at index one exposes a zero cut.
  action matchingBottomNext = all {
    top0' = 0, top1' = 0, top2' = 1,
    bottom0' = 0, bottom1' = 1, bottom2' = 0,
  }

  // Balanced and irreducible: top=001, bottom=100. The same
  // asynchronous source prefix defect e0 occurs but the bottom next
  // letter is 1, not 0; no balanced interior cut is forced.
  action differentBottomNext = all {
    top0' = 0, top1' = 0, top2' = 1,
    bottom0' = 1, bottom1' = 0, bottom2' = 0,
  }

  action step = any { matchingBottomNext, differentBottomNext }

  val topCountZero =
    (if (top0 == 0) 1 else 0) +
    (if (top1 == 0) 1 else 0) +
    (if (top2 == 0) 1 else 0)
  val bottomCountZero =
    (if (bottom0 == 0) 1 else 0) +
    (if (bottom1 == 0) 1 else 0) +
    (if (bottom2 == 0) 1 else 0)
  val topCountOne =
    (if (top0 == 1) 1 else 0) +
    (if (top1 == 1) 1 else 0) +
    (if (top2 == 1) 1 else 0)
  val bottomCountOne =
    (if (bottom0 == 1) 1 else 0) +
    (if (bottom1 == 1) 1 else 0) +
    (if (bottom2 == 1) 1 else 0)

  val balancedFullWords =
    topCountZero == bottomCountZero and
    topCountOne == bottomCountOne

  // Source cut top at 1, bottom at 0 has defect +e0.
  val sourceUnitDefect = top0 == 0

  // Literal aligned balanced cuts at word indices 1 or 2.
  val returnAtOne = top0 == bottom0
  val returnAtTwo =
    (if (top0 == 0) 1 else 0) + (if (top1 == 0) 1 else 0) ==
      (if (bottom0 == 0) 1 else 0) + (if (bottom1 == 0) 1 else 0) and
    (if (top0 == 1) 1 else 0) + (if (top1 == 1) 1 else 0) ==
      (if (bottom0 == 1) 1 else 0) + (if (bottom1 == 1) 1 else 0)

  val germBottomMatchesDefect = bottom0 == 0
  val irreducible = not(returnAtOne) and not(returnAtTwo)

  run alignedReturnForcedBySourceLetterTest =
    init.then(matchingBottomNext)
      .expect(balancedFullWords and sourceUnitDefect
        and germBottomMatchesDefect and returnAtOne and not(irreducible))

  run mismatchCanRemainIrreducibleTest =
    init.then(differentBottomNext)
      .expect(balancedFullWords and sourceUnitDefect
        and not(germBottomMatchesDefect) and not(returnAtOne)
        and not(returnAtTwo) and irreducible)
}
