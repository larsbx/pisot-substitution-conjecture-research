// Independently replay every row of both fixed source domains.
module PscR2OrderedOccurrences {
  pure val trib = List(List(0, 1), List(0, 2), List(0))
  pure val control = List(List(1), List(0, 1, 2), List(1))
  pure val seed = (List(0, 1), List(1, 0))
  pure def inflate(images, w) = range(0, w.length()).foldl(List(), (out, i) =>
    range(0, images[w[i]].length()).foldl(out, (acc, j) =>
      acc.append({ letter: images[w[i]][j], parent: i, offset: j })))
  pure def letters(w) = w.foldl(List(), (out, x) => out.append(x.letter))
  pure def count(w, a) = w.select(x => x == a).length()
  pure def balanced(u, v) = Set(0, 1, 2).forall(a => count(u, a) == count(v, a))
  pure def children(images, pair) = {
    val u = inflate(images, pair._1)
    val v = inflate(images, pair._2)
    val top = letters(u)
    val bottom = letters(v)
    val cuts = range(0, top.length() + 1).select(k => balanced(top.slice(0, k), bottom.slice(0, k)))
    range(0, cuts.length() - 1).foldl(List(), (out, i) => {
      val lo = cuts[i]
      val hi = cuts[i + 1]
      val a = top.slice(lo, hi)
      val b = bottom.slice(lo, hi)
      val sign = if (a[0] > b[0]) -1 else 1
      out.append({ child: (a, b), ord: i, start: lo, end: hi,
        ti: u[lo].parent, to: u[lo].offset, bi: v[lo].parent, bo: v[lo].offset, sign: sign })
    })
  }

  pure def packet(images, cap) = range(0, cap).foldl({ states: List(seed), edges: List() }, (p, src) =>
    if (src >= p.states.length()) p
    else children(images, p.states[src]).foldl(p, (q, e) => {
      val matches = range(0, q.states.length()).select(i => q.states[i] == e.child)
      val dst = if (matches.length() == 0) q.states.length() else matches[0]
      val states = if (matches.length() == 0) q.states.append(e.child) else q.states
      { states: states, edges: q.edges.append(List(src, dst, e.ord, e.start,
        e.end, e.ti, e.to, e.bi, e.bo, e.sign)) }
    }))

  pure def residualVector(states, row) = {
    val state = states[row[0]]
    val top = state._1.slice(0, row[5])
    val bottom = state._2.slice(0, row[7])
    val scale = row[9] - 1
    List(scale * (count(top, 0) - count(bottom, 0)),
      scale * (count(top, 1) - count(bottom, 1)),
      scale * (count(top, 2) - count(bottom, 2)))
  }
  pure def vectorAt(p, i) = residualVector(p.states, p.edges[i])
  pure def closed(p, rows) = rows.indices().forall(i =>
    p.edges[rows[i]][1] == p.edges[rows[(i + 1) % rows.length()]][0])
  pure def sumCoordinate(p, rows, a) = rows.foldl(0, (acc, i) => acc + vectorAt(p, i)[a])

  pure val t = packet(trib, 11)
  pure val c = packet(control, 4)
  var active: bool
  action init = active' = true

  run completeDomainsTest = init.expect(all {
    active,
    t.states.length() == 11, t.edges.length() == 25,
    c.states.length() == 4, c.edges.length() == 8,
    packet(trib, 10).edges.length() < t.edges.length(),
  })

  run parallelAndSignedAddressTest = init.expect(all {
    active,
    t.edges[9] == List(4, 0, 1, 1, 3, 1, 0, 0, 1, 1),
    t.edges[11] == List(4, 0, 3, 5, 7, 3, 0, 2, 1, 1),
    t.edges[5] == List(2, 4, 1, 1, 5, 0, 1, 1, 0, -1),
  })

  run actualCycleRefusesPotentialTest = init.expect(all {
    active,
    (t.edges[5][0], t.edges[5][1]) == (2, 4),
    (t.edges[9][0], t.edges[9][1]) == (4, 0),
    (t.edges[1][0], t.edges[1][1]) == (0, 2),
    sumCoordinate(t, List(5, 9, 1), 2) == 2,
  })

  run tribonacciLinearFamilyTest = init.expect(all {
    active,
    t.edges.indices().forall(i => Set(List(0, 0, 0), List(0, 0, 2)).contains(vectorAt(t, i))),
    closed(t, List(5, 9, 1)),
    sumCoordinate(t, List(5, 9, 1), 2) == 2,
    sumCoordinate(t, List(5, 9, 1), 0) == 0,
  })

  run reducibleLinearFamilyTest = init.expect(all {
    active,
    c.edges.indices().forall(i => Set(List(0, 0, 0), List(2, 0, 0), List(0, 0, 2)).contains(vectorAt(c, i))),
    closed(c, List(3, 6)),
    closed(c, List(5, 7)),
    sumCoordinate(c, List(3, 6), 0) == 2,
    sumCoordinate(c, List(3, 6), 2) == 0,
    sumCoordinate(c, List(5, 7), 0) == 0,
    sumCoordinate(c, List(5, 7), 2) == 2,
  })
}
