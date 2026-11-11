// Finite independent controls for normalized literal inverse-row records.
// The model does not certify compact-piece coverage or the twelve-source packet.
module C4LiteralInverseBindingDefinitions {
  pure def count(w, n, a) = range(0, n).foldl(0, (out, i) => out + (if (w[i] == a) 1 else 0))
  pure def prefix(w, n) = (count(w, n, 0), count(w, n, 1), count(w, n, 2))
  pure def add(x, y) = (x._1 + y._1, x._2 + y._2, x._3 + y._3)
  pure def sub(x, y) = (x._1 - y._1, x._2 - y._2, x._3 - y._3)
  pure def neg(x) = (-x._1, -x._2, -x._3)
  pure def incidence(s, r) = (
    count(s[0], s[0].length(), 0) * r._1 + count(s[1], s[1].length(), 0) * r._2 + count(s[2], s[2].length(), 0) * r._3,
    count(s[0], s[0].length(), 1) * r._1 + count(s[1], s[1].length(), 1) * r._2 + count(s[2], s[2].length(), 1) * r._3,
    count(s[0], s[0].length(), 2) * r._1 + count(s[1], s[1].length(), 2) * r._2 + count(s[2], s[2].length(), 2) * r._3)
  pure def child(s, p, i, j) = (s[p._1][i], s[p._2][j],
    add(incidence(s, p._3), sub(prefix(s[p._1], i), prefix(s[p._2], j))))
  pure def swap(p) = (p._2, p._1, neg(p._3))
  pure def positiveLex(r) = r._1 > 0 or (r._1 == 0 and r._2 > 0) or (r._1 == 0 and r._2 == 0 and r._3 > 0)
  pure def canonical(p) = if (p._1 > p._2 or (p._1 == p._2 and positiveLex(p._3))) swap(p) else p
  pure def swapEdge(e) = (swap(e._1), e._3, e._2, swap(e._4))
  pure def sourceNormalize(e) = if (e._4 == canonical(e._4)) e else swapEdge(e)
  // Forward edge (raw ancestor, i, j, inverse source) -> inverse row slot.
  pure def encode(e) = {
    val n = sourceNormalize(e)
    (n._4, canonical(n._1), n._2, n._3, n._1 != canonical(n._1))
  }
  pure def raw(slot) = if (slot._5) swap(slot._2) else slot._2
  pure def decode(slot) = (raw(slot), slot._3, slot._4, slot._1)
  pure def validSlot(s, slot) = {
    val p = raw(slot)
    slot._3 >= 0 and slot._3 < s[p._1].length() and
      slot._4 >= 0 and slot._4 < s[p._2].length() and
      slot._1 == canonical(slot._1) and slot._2 == canonical(slot._2) and
      child(s, p, slot._3, slot._4) == slot._1
  }
  pure def translation(s, slot) = if (slot._5)
    add(slot._1._3, prefix(s[raw(slot)._2], slot._4))
    else prefix(s[raw(slot)._1], slot._3)
  pure def expectedTranslation(s, slot) = add(prefix(s[raw(slot)._1], slot._3),
    if (slot._5) incidence(s, raw(slot)._3) else (0, 0, 0))
  pure val binaryImages = Set(List(0, 0), List(0, 1), List(1, 0), List(1, 1))
  pure val offsets = Set(-1, 0, 1)
  pure def boundedEdges(s) = 0.to(1).fold(Set(), (out, a) =>
    0.to(1).fold(out, (as, b) => offsets.fold(as, (bs, x) => offsets.fold(bs, (xs, y) =>
      0.to(1).fold(xs, (ys, i) => 0.to(1).fold(ys, (is, j) => {
        val p = (a, b, (x, y, 0))
        is.union(Set((p, i, j, child(s, p, i, j))))
      }))))))
  pure def has(ps, p) = ps.indices().exists(i => ps[i] == p)
  pure def internalSlots(s, ps) = ps.foldl(List(), (out, p) =>
    range(0, s[p._1].length()).foldl(out, (pss, i) =>
      range(0, s[p._2].length()).foldl(pss, (es, j) => {
        val q = child(s, p, i, j)
        if (has(ps, q) and q == canonical(q))
          es.append(encode((p, i, j, q))) else es
      })))
  pure def sameSlots(expected, submitted) = expected.length() == submitted.length() and
    expected.indices().forall(i => submitted.select(x => x == expected[i]).length() == 1)
  pure def sameTargets(expected, submitted) = expected.length() == submitted.length() and
    expected.indices().forall(i =>
      expected.select(x => x._1 == expected[i]._1 and x._2 == expected[i]._2).length() ==
      submitted.select(x => x._1 == expected[i]._1 and x._2 == expected[i]._2).length())
  pure val repeatedSigma = List(List(0, 0), List(0, 0), List(0, 0))
  pure val repeatedStates = List((0, 1, (0, 0, 0)), (1, 0, (0, 0, 0)), (0, 0, (0, 0, 0)))
  // Birth list index k discovers state k+1 from a strictly earlier row.
  pure def validBirths(bs) = bs.indices().forall(k => bs[k]._1 >= 0 and bs[k]._1 < k + 1)
  pure def birthEdges(bs) = bs.indices().fold(Set(), (out, k) => out.union(Set(
    ((bs[k]._1, false), (k + 1, bs[k]._2)),
    ((bs[k]._1, true), (k + 1, not(bs[k]._2))))))
  pure def reach(es, roots, n) = 0.to(n).fold(roots, (known, _) =>
    es.fold(known, (acc, e) => if (known.contains(e._1)) acc.union(Set(e._2)) else acc))
}

module C4LiteralInverseBinding {
  import C4LiteralInverseBindingDefinitions.*
  var ready: bool
  action init = ready' = true

  run boundedDomainTest = init.expect(binaryImages.size() == 4 and offsets.size() == 3 and
    boundedEdges(List(List(0, 1), List(1, 0), List(0, 0))).size() == 144)

  run normalizedLiteralRoundTripTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    boundedEdges(s).forall(e => decode(encode(e)) == sourceNormalize(e) and validSlot(s, encode(e)))
  })))

  run normalizedSwapMateTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    boundedEdges(s).forall(e => e._4 == swap(e._4) or encode(e) == encode(swapEdge(e)))
  })))

  run geometricTranslationTest = init.expect(binaryImages.forall(u => binaryImages.forall(v => {
    val s = List(u, v, List(0, 0))
    boundedEdges(s).forall(e => translation(s, encode(e)) == expectedTranslation(s, encode(e)))
  })))

  run orientationBitRequiredTest = init.expect({
    val s = List(List(0, 1), List(1, 0), List(0, 0))
    boundedEdges(s).exists(e => {
      val slot = encode(e)
      val erased = (slot._1, slot._2, slot._3, slot._4, false)
      slot._5 and validSlot(s, slot) and not(validSlot(s, erased))
    })
  })

  run repeatedPositionInventoryTest = init.expect({
    val slots = internalSlots(repeatedSigma, repeatedStates)
    val first = slots[0]
    val mate = slots.select(s => s._1 == first._1 and s._2 == first._2 and s._5 == first._5 and s != first)[0]
    val forged = slots.foldl(List(), (out, s) => out.append(if (s == mate) first else s))
    all {
      slots.length() == 6, sameSlots(slots, slots),
      slots.indices().forall(i => validSlot(repeatedSigma, slots[i])),
      forged.indices().forall(i => validSlot(repeatedSigma, forged[i])),
      sameTargets(slots, forged), not(sameSlots(slots, forged)),
      not(sameSlots(slots, slots.select(s => s != first))),
    }
  })

  run earlierBirthsReachBothOrientationsTest = init.expect(Set(false, true).forall(f => Set(false, true).forall(g =>
    0.to(1).forall(parent => {
      val bs = List((0, f), (parent, g))
      val reached = reach(birthEdges(bs), Set((0, false), (0, true)), 3)
      validBirths(bs) and 0.to(2).forall(i => Set(false, true).forall(b => reached.contains((i, b))))
    }))))

  run circularBirthsRejectedTest = init.expect({
    val bs = List((2, false), (1, false))
    val reached = reach(birthEdges(bs), Set((0, false), (0, true)), 3)
    not(validBirths(bs)) and reached == Set((0, false), (0, true))
  })

  run swappedBirthMateRequiredTest = init.expect({
    val bs = List((0, true), (1, false))
    val es = birthEdges(bs)
    val oneSheet = es.filter(e => e._1._2 == false)
    val reached = reach(oneSheet, Set((0, false), (0, true)), 3)
    validBirths(bs) and reach(es, Set((0, false), (0, true)), 3).size() == 6 and reached.size() < 6
  })
}
