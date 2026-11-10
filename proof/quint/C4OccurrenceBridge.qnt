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

  // Indexed lookup retains the chunk ordinal, including when values repeat.
  // Empty chunks are allowed in this generic list control, though red factors
  // are nonempty. No index is dereferenced until a containing chunk is found.
  pure def joinChunks(chunks) = chunks.foldl(List(), (out, w) => out.concat(w))
  pure def offset(chunks, k) = range(0, k).foldl(0, (n, j) => n + chunks[j].length())
  pure def locate(chunks, i) = range(0, chunks.length()).select(k =>
    offset(chunks, k) <= i and i < offset(chunks, k) + chunks[k].length())
  pure def localPosition(chunks, k, i) = i - offset(chunks, k)
  pure def factors(w, cs) = range(0, cs.length() - 1)
    .foldl(List(), (out, k) => out.append(w.slice(cs[k], cs[k + 1])))

  // Exact integer Parikh arithmetic for arbitrary finite binary words.
  // Matrix columns are the populations of the two substitution images.
  pure def residual(u, v, i, j) = (
    count(prefix(u, i), 0) - count(prefix(v, j), 0),
    count(prefix(u, i), 1) - count(prefix(v, j), 1))
  pure def add2(x, y) = (x._1 + y._1, x._2 + y._2)
  pure def incidence(s, r) = (
    count(s[0], 0) * r._1 + count(s[1], 0) * r._2,
    count(s[0], 1) * r._1 + count(s[1], 1) * r._2)
  pure def affineNext(s, r, forcing) = add2(incidence(s, r), forcing)
  pure def orientedResidual(sign, r) = if (sign == 1) r else (-r._1, -r._2)
  pure def imagePosition(s, w, i, digit) = inflate(s, prefix(w, i)).length() + digit

  pure val words = Set(0, 1).allListsUpTo(4).filter(w => w.length() >= 2)
  pure val images = Set(List(0), List(1), List(0, 0), List(0, 1), List(1, 0), List(1, 1))
  pure val lengths = Set(List(1, 1), List(1, 2), List(1, 3),
    List(2, 1), List(2, 2), List(2, 3), List(3, 1), List(3, 2), List(3, 3))
  pure val lookupParts = Set(0, 1).allListsUpTo(2)
  pure val lookupChunks = lookupParts.allListsUpTo(3)
  pure val lookupWords = Set(0, 1).allListsUpTo(4)
  pure val transportWords = lookupParts.filter(w => w.length() > 0)
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

  // All 400 ordered lists of at most three chunks, each an arbitrary binary
  // word of length 0..2. Across them there are 1,620 in-range global indices.
  run lookupDomainCountTest = init.expect(all {
    lookupParts.size() == 7, lookupChunks.size() == 400,
    lookupChunks.fold(0, (n, chunks) => n + joinChunks(chunks).length()) == 1620,
    lookupWords.size() == 31,
    lookupWords.fold(0, (n, u) => n + lookupWords.filter(v => balanced(u, v)).size()) == 99,
  })

  run globalToLocalReconstructionTest = init.expect(lookupChunks.forall(chunks => {
    val w = joinChunks(chunks)
    0.to(w.length() - 1).forall(i => {
      val found = locate(chunks, i)
      if (found.length() == 1) {
        val k = found[0]
        val j = localPosition(chunks, k, i)
        all {
          0 <= j, j < chunks[k].length(), i == offset(chunks, k) + j,
          chunks[k][j] == w[i],
          joinChunks(prefix(chunks, k)).concat(prefix(chunks[k], j)) == prefix(w, i),
          joinChunks(prefix(chunks, k)).concat(prefix(chunks[k], j))
            .concat(List(w[i])).concat(chunks[k].slice(j + 1, chunks[k].length()))
            .concat(joinChunks(chunks.slice(k + 1, chunks.length()))) == w,
        }
      } else false
    })
  }))

  run exteriorAddressRejectedTest = init.expect(lookupChunks.forall(chunks => all {
    locate(chunks, -1) == List(),
    locate(chunks, joinChunks(chunks).length()) == List(),
    locate(chunks, joinChunks(chunks).length() + 1) == List(),
  }))

  // Actual complete balanced reductions in this bounded word universe;
  // generic chunk lookup agrees with the zero-return factor ordinal.
  run balancedFactorLookupTest = init.expect(lookupWords.forall(u => lookupWords.forall(v =>
    if (balanced(u, v)) {
      val cs = cuts(u, v)
      val top = factors(u, cs)
      val bot = factors(v, cs)
      all {
        joinChunks(top) == u, joinChunks(bot) == v,
        0.to(u.length() - 1).forall(i => all {
          locate(top, i) == List(ordinal(cs, i)),
          locate(bot, i) == List(ordinal(cs, i)),
          localPosition(top, ordinal(cs, i), i) == i - cs[ordinal(cs, i)],
        }),
      }
    } else true)))

  // Six arbitrary nonempty binary words of length 1..2, all 36 nonerasing
  // substitutions with image length 1..2, all source indices and valid digits.
  // The 10,400 cases include unbalanced word pairs and non-PIP substitutions.
  run transportDomainCountTest = init.expect(all {
    transportWords.size() == 6,
    transportWords.size() * transportWords.size() * images.size() * images.size() == 1296,
    images.fold(0, (n, a) => n + images.fold(0, (m, b) => m +
      transportWords.fold(0, (p, u) => p + transportWords.fold(0, (q, v) => q +
        range(0, u.length()).foldl(0, (r, i) => r +
          range(0, v.length()).foldl(0, (t, j) =>
            t + List(a, b)[u[i]].length() * List(a, b)[v[j]].length())))))) == 10400,
  })

  run literalAffineSquareTest = init.expect(images.forall(a => images.forall(b =>
    transportWords.forall(u => transportWords.forall(v =>
      0.to(u.length() - 1).forall(i => 0.to(v.length() - 1).forall(j => {
        val s = List(a, b)
        val top = inflate(s, u)
        val bot = inflate(s, v)
        0.to(s[u[i]].length() - 1).forall(p => 0.to(s[v[j]].length() - 1).forall(q => {
          val ti = imagePosition(s, u, i, p)
          val bi = imagePosition(s, v, j, q)
          val r = residual(u, v, i, j)
          val forcing = residual(s[u[i]], s[v[j]], p, q)
          all {
            top[ti] == s[u[i]][p], bot[bi] == s[v[j]][q],
            prefix(top, ti) == inflate(s, prefix(u, i)).concat(prefix(s[u[i]], p)),
            prefix(bot, bi) == inflate(s, prefix(v, j)).concat(prefix(s[v[j]], q)),
            residual(top, bot, ti, bi) == affineNext(s, r, forcing),
          }
        }))
      })))))))

  run balancedPrefixTrimmingTest = init.expect(lookupWords.forall(u => lookupWords.forall(v =>
    if (balanced(u, v)) {
      val cs = cuts(u, v)
      0.to(u.length() - 1).forall(i => 0.to(v.length() - 1).forall(j => {
        val k = ordinal(cs, i)
        if (k == ordinal(cs, j)) all {
          parikh(prefix(u, cs[k])) == parikh(prefix(v, cs[k])),
          residual(u, v, i, j) == residual(u.slice(cs[k], cs[k + 1]),
            v.slice(cs[k], cs[k + 1]), i - cs[k], j - cs[k]),
        } else true
      }))
    } else true)))

  // A physical track swap also exchanges both source indices and both digits.
  // It negates the entire transported residual, including digit forcing.
  run trackSwapCovarianceTest = init.expect(images.forall(a => images.forall(b =>
    transportWords.forall(u => transportWords.forall(v =>
      0.to(u.length() - 1).forall(i => 0.to(v.length() - 1).forall(j => {
        val s = List(a, b)
        0.to(s[u[i]].length() - 1).forall(p => 0.to(s[v[j]].length() - 1).forall(q => {
          val ti = imagePosition(s, u, i, p)
          val bi = imagePosition(s, v, j, q)
          val forward = affineNext(s, residual(u, v, i, j), residual(s[u[i]], s[v[j]], p, q))
          val reversed = affineNext(s, residual(v, u, j, i), residual(s[v[j]], s[u[i]], q, p))
          all {
            residual(inflate(s, v), inflate(s, u), bi, ti) == orientedResidual(-1, forward),
            reversed == orientedResidual(-1, forward),
            orientedResidual(1, forward) == forward,
          }
        }))
      })))))))

  // Nonzero witnesses prevent either term of the affine identity disappearing
  // in a vacuous zero-residual fixture. These substitutions are general words.
  run affineTermsAreNecessaryTest = init.expect({
    val u = List(0, 1)
    val v = List(1, 0)
    val stretch = List(List(0, 0), List(1))
    val digit = List(List(0, 1), List(0))
    val r = residual(u, v, 1, 1)
    val f = residual(digit[0], digit[1], 1, 0)
    all {
      r == (1, -1), incidence(stretch, r) == (2, -1),
      residual(inflate(stretch, u), inflate(stretch, v), 2, 1) == (2, -1),
      affineNext(stretch, r, (0, 0)) == (2, -1),
      affineNext(stretch, r, (0, 0)) != r,
      f == (1, 0), residual(inflate(digit, u), inflate(digit, v), 1, 0) == f,
      affineNext(digit, (0, 0), f) == (1, 0),
      affineNext(digit, (0, 0), f) != (0, 0),
    }
  })

  run sameLetterSplitStaysSplitTest = init.expect({
    val s = List(List(0, 0), List(0, 0))
    val u = List(0, 1)
    val v = List(1, 0)
    val top = inflate(s, u)
    val bot = inflate(s, v)
    val ti = imagePosition(s, u, 0, 1)
    val bi = imagePosition(s, v, 1, 1)
    val cs = cuts(top, bot)
    all {
      ti == 1, bi == 3, top[ti] == bot[bi],
      cs == List(0, 1, 2, 3, 4), ordinal(cs, ti) != ordinal(cs, bi),
      residual(top, bot, ti, bi) == (-2, 0),
      residual(top, bot, ti, bi) == affineNext(s, residual(u, v, 0, 1),
        residual(s[u[0]], s[v[1]], 1, 1)),
      not(interiorOverlap(top, bot, ti, bi, List(1, 1))),
    }
  })
}
