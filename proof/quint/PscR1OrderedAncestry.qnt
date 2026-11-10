// Independent literal-source replay for the depth-six cut at 51.
module PscR1OrderedAncestry {
  pure val images = List(List(0, 1), List(0, 2), List(0))
  pure def inflate(w) = w.foldl(List(), (out, a) => out.concat(images[a]))
  pure def track(w, n) = range(0, n).foldl(w, (word, _) => inflate(word))
  pure def heads(w) = range(0, w.length()).foldl(List(), (out, i) =>
    range(0, images[w[i]].length()).foldl(out, (acc, j) => acc.append((i, j))))
  pure def count(w, a) = w.select(x => x == a).length()
  pure def diff(u, v) = List(count(u, 0) - count(v, 0),
    count(u, 1) - count(v, 1), count(u, 2) - count(v, 2))
  pure def add(x, y) = List(x[0] + y[0], x[1] + y[1], x[2] + y[2])
  pure def m(x) = List(x[0] + x[1] + x[2], x[0], x[1])

  pure def stepAt(level, t, b) = {
    val u = track(List(0, 1), level)
    val v = track(List(1, 0), level)
    val (i, r) = heads(u)[t]
    val (j, s) = heads(v)[b]
    { i: i, j: j, r: r, s: s, a: u[i], b: v[j],
      x: diff(u.slice(0, i), v.slice(0, j)),
      c: diff(images[u[i]].slice(0, r), images[v[j]].slice(0, s)) }
  }

  pure val s5 = stepAt(5, 51, 51)
  pure val s4 = stepAt(4, s5.i, s5.j)
  pure val s3 = stepAt(3, s4.i, s4.j)
  pure val s2 = stepAt(2, s3.i, s3.j)
  pure val s1 = stepAt(1, s2.i, s2.j)
  pure val s0 = stepAt(0, s1.i, s1.j)

  var active: bool
  action init = active' = true

  run literalCycleTest = init.expect(all {
    active,
    diff(track(List(0, 1), 6).slice(0, 51), track(List(1, 0), 6).slice(0, 51)) == List(0, 0, 0),
    (s0.i, s0.j, s0.r, s0.s, s0.a, s0.b) == (1, 1, 0, 0, 1, 0),
    (s1.i, s1.j, s1.r, s1.s, s1.a, s1.b) == (2, 2, 0, 1, 0, 0),
    (s2.i, s2.j, s2.r, s2.s, s2.a, s2.b) == (4, 4, 1, 0, 0, 1),
    (s0.a, s0.b, s0.x) == (s3.a, s3.b, s3.x),
    add(m(s0.x), s0.c) == s1.x,
    add(m(s1.x), s1.c) == s2.x,
    add(m(s2.x), s2.c) == s3.x,
    add(m(add(m(s0.c), s1.c)), s2.c) == List(0, -1, 0),
  })

  run arithmeticCandidateNeedsAddressTest = init.expect(all {
    active,
    add(m(List(1, 0, 0)), List(-1, 0, 0)) == List(0, 1, 0),
    add(m(List(0, 1, 0)), List(-1, 0, 0)) == List(0, 0, 1),
    m(List(0, 0, 1)) == List(1, 0, 0),
    s0.x != List(1, 0, 0),
    s0.c != List(-1, 0, 0),
  })

  // This basis calculation uses a separate row expression for U(I-M^3)V.
  pure def diagReplay(y) = {
    val v = List(y[0] - y[1] - y[2], y[1] + y[2], y[2])
    val a = m(m(m(v)))
    val q = List(v[0] - a[0], v[1] - a[1], v[2] - a[2])
    List(-q[2], q[1] - 2 * q[2], -q[0] + 3 * q[2])
  }

  run periodThreeSmithBasisTest = init.expect(all {
    active,
    diagReplay(List(1, 0, 0)) == List(1, 0, 0),
    diagReplay(List(0, 1, 0)) == List(0, 1, 0),
    diagReplay(List(0, 0, 1)) == List(0, 0, 2),
  })

  // The exact source seed has diagonal letter coincidences after one
  // inflation; its depth-six ancestry loops are NOT strict nonproductive
  // BPA components. This is a genuinely literal word-level exclusion
  // of a false positive in the R1F finite candidate survey.
  run productiveSwapSeedTest = init.expect(all {
    active,
    inflate(List(0, 1)) == List(0, 1, 0, 2),
    inflate(List(1, 0)) == List(0, 2, 0, 1),
    inflate(List(0, 1))[0] == inflate(List(1, 0))[0],
    inflate(List(0, 1))[2] == inflate(List(1, 0))[2],
  })
}
