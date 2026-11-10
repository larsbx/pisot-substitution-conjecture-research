// Bounded, independent literal-word checks for the concrete C4 bridge.
// This model does not generate a Pisot corpus or assert uniform productivity.
// Every quantified finite domain below is exhaustively evaluated in one test.
module C4OccurrenceDefinitions {
  pure def prefix(w, n) = range(0, n).foldl(List(), (out, i) => out.append(w[i]))
  pure def count(w, a) = w.foldl(0, (n, b) => n + (if (a == b) 1 else 0))
  pure def parikh(w) = (count(w, 0), count(w, 1))
  pure def balanced(u, v) = u.length() == v.length() and parikh(u) == parikh(v)
  pure def cuts(u, v) = range(0, u.length() + 1)
    .select(i => parikh(prefix(u, i)) == parikh(prefix(v, i)))
  pure def strictParent(u, v) = balanced(u, v) and u.length() >= 2 and
    cuts(u, v) == List(0, u.length())
  pure def inflate(s, w) = w.foldl(List(), (out, a) => out.concat(s[a]))
  pure def ordinal(cs, i) = cs.select(k => k <= i).length() - 1
  pure def inherited(s, u, v, k) = cuts(u, v)
    .select(i => inflate(s, prefix(u, i)).length() == k).length() > 0
  pure def weightPrefix(w, i, lengths) = range(0, i)
    .foldl(0, (out, j) => out + lengths[w[j]])
  pure def interiorOverlap(u, v, i, j, lengths) = all {
    weightPrefix(u, i, lengths) < weightPrefix(v, j + 1, lengths),
    weightPrefix(v, j, lengths) < weightPrefix(u, i + 1, lengths),
  }
  pure def boundaryContact(u, v, i, j, lengths) = all {
    weightPrefix(u, i, lengths) <= weightPrefix(v, j + 1, lengths),
    weightPrefix(v, j, lengths) <= weightPrefix(u, i + 1, lengths),
  }
  pure def newbornAt(s, u, v, lo, hi) = {
    val top = inflate(s, u)
    val bot = inflate(s, v)
    val cut = if (lo > 0) lo else hi
    all {
      0 < cut, cut < top.length(),
      cuts(top, bot).select(k => k == cut).length() == 1,
      not(inherited(s, u, v, cut)),
      if (lo > 0) top[cut] == bot[cut] else top[cut - 1] == bot[cut - 1],
    }
  }

  pure val words = Set(0, 1).allListsUpTo(4).filter(w => w.length() >= 2)
  pure val images = Set(List(0), List(1), List(0, 0), List(0, 1), List(1, 0), List(1, 1))
  pure val lengths = Set(List(1, 1), List(1, 2), List(1, 3),
    List(2, 1), List(2, 2), List(2, 3), List(3, 1), List(3, 2), List(3, 3))
}

module C4OccurrenceBridge {
  import C4OccurrenceDefinitions.*
  var active: bool
  action init = active' = true

  run domainCountTest = init.expect(all {
    active, words.size() == 28, images.size() == 6, lengths.size() == 9,
    words.fold(0, (n, u) => n + words.filter(v => strictParent(u, v)).size()) == 16,
    16 * images.size() * images.size() == 576,
  })

  // All 16 ordered binary strict parents of length 2..4 and all 36
  // nonerasing binary substitutions with image length 1..2: 576 inputs.
  run allSingletonsGiveNewbornTest = init.expect(words.forall(u => words.forall(v =>
    if (strictParent(u, v)) images.forall(a => images.forall(b => {
      val s = List(a, b)
      val top = inflate(s, u)
      val bot = inflate(s, v)
      val cs = cuts(top, bot)
      0.to(cs.length() - 2).forall(j =>
        if (cs[j + 1] == cs[j] + 1) newbornAt(s, u, v, cs[j], cs[j + 1]) else true)
    })) else true)))

  run alignedLetterIsSingletonTest = init.expect(words.forall(u => words.forall(v =>
    if (balanced(u, v)) 0.to(u.length() - 1).forall(i =>
      if (parikh(prefix(u, i)) == parikh(prefix(v, i)) and u[i] == v[i]) {
        val cs = cuts(u, v)
        val j = ordinal(cs, i)
        cs[j] == i and cs[j + 1] == i + 1
      } else true) else true)))

  // Positive integer lengths are finite controls, not an encoding of all
  // Perron vectors. No irreducibility or Pisot assertion is made here.
  run interiorOverlapKeepsOrdinalTest = init.expect(words.forall(u => words.forall(v =>
    if (balanced(u, v)) lengths.forall(ls =>
      0.to(u.length() - 1).forall(i => 0.to(v.length() - 1).forall(j =>
        not(interiorOverlap(u, v, i, j, ls)) or
          ordinal(cuts(u, v), i) == ordinal(cuts(u, v), j)))) else true)))

  run boundaryTouchIsInsufficientTest = init.expect({
    val w = List(0, 1)
    all {
      boundaryContact(w, w, 0, 1, List(1, 2)),
      not(interiorOverlap(w, w, 0, 1, List(1, 2))),
      ordinal(cuts(w, w), 0) != ordinal(cuts(w, w), 1),
    }
  })

  run repeatedFactorValuesLoseOccurrenceTest = init.expect({
    val w = List(0, 0)
    all {
      prefix(w, 1) == List(w[1]), cuts(w, w) == List(0, 1, 2),
      ordinal(cuts(w, w), 0) != ordinal(cuts(w, w), 1),
      not(interiorOverlap(w, w, 0, 1, List(1, 2))),
    }
  })

  run erasureAndSingletonParentControlsTest = init.expect({
    val u = List(0, 1)
    val v = List(1, 0)
    val erase = List(List(), List(0))
    val identity = List(List(0), List(1))
    all {
      strictParent(u, v), inflate(erase, u) == List(0), inflate(erase, v) == List(0),
      not(0.to(1).exists(k => 0 < k and k < inflate(erase, u).length())),
      not(strictParent(List(0), List(0))),
      inflate(identity, List(0)).length() == 1,
    }
  })

  run parentIrreducibilityIsNecessaryTest = init.expect({
    val w = List(0, 1)
    val identity = List(List(0), List(1))
    all {
      balanced(w, w), not(strictParent(w, w)),
      cuts(w, w) == List(0, 1, 2), inherited(identity, w, w, 1),
    }
  })

  run bothNewbornSidesTest = init.expect({
    val u = List(0, 1)
    val v = List(1, 0)
    val left = List(List(0, 1), List(0))
    val right = List(List(1, 0), List(0))
    all {
      newbornAt(left, u, v, 0, 1), // cut 1 uses the letter to its left: Sync_-.
      newbornAt(right, u, v, 2, 3), // cut 2 uses the letter to its right: Sync_+.
    }
  })

  // An abstract four-vertex graph suffices to refute universal-path and
  // nominated-visit replacements of the existential target. It is explicitly
  // not a realizable Pisot counterexample or a complete overlap graph.
  run existentialRouteAllowsAvoidingCycleTest = init.expect({
    val edges = Set((0, 1), (1, 1), (1, 2), (3, 3))
    val productive = edges.contains((0, 1)) and edges.contains((1, 2))
    val reachable = range(0, 4).foldl(Set(0), (known, _) => known.union(
      Set(0, 1, 2, 3).filter(j => known.exists(i => edges.contains((i, j))))))
    all {
      productive, edges.contains((1, 1)),
      reachable == Set(0, 1, 2), not(reachable.contains(3)),
    }
  })
}
