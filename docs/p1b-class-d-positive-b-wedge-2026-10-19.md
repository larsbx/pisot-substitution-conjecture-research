# Class-D positive-b residual: exact wedge test — 2026-10-19

**Status:** active proof attempt for issue #139. This note introduces no theorem
until the exact two-parameter closure runs succeed. It reuses the already
audited Theorem W engine rather than adding a new quotient or sampled census.

## 1. Exact residual domains

The complete class-D residual parameterization is

```text
s = +1: p = 3 + 3a + b, q = 2 + 3a + b, r = 2a + b
s = -1: p = 5 + 3a + b, q = 6 + 3a + b, r = 4 + 2a + b
a >= 0, b >= 0.
```

Merged PR #277 certifies both infinite boundary lines `b=0`. The remaining
domains are exactly `b>=1`.

Put `c=b-1>=0`. Then the two open interiors are single affine wedges:

```text
s = +1:
(p,q,r) = (4,3,1) + a(3,3,2) + c(1,1,1)

s = -1:
(p,q,r) = (6,7,5) + a(3,3,2) + c(1,1,1).
```

The directions in `(q,r)` are again `(3,2)` and `(1,1)`, determinant
one, so every integer point of each positive-b residual appears exactly once.

## 2. Why this is the highest-value test

`psc.symbolic_line.ClassWedge` already proves complete two-parameter
seed-overlap closure on an affine quadrant when:

1. the PIP property is certified uniformly;
2. every sign at the Perron root is certified by the nonvanishing-norm /
   quadrant machinery;
3. the symbolic seed graph closes completely;
4. every symbolic vertex reaches offset zero;
5. the symbolic graph agrees with exact graphs at two interior points.

This is exactly the #139 target on this scoped class. No projected-vector
lifting gap is introduced: the engine constructs the actual seed-patch overlap
graph and its complete child relation.

## 3. Exact test

The dedicated workflow runs:

```sh
cd kernel
pixi run mojo run -I . symbolic_line_certificate.mojo wedge D 4 3 1 3 3 1 1 2 1
pixi run mojo run -I . symbolic_line_certificate.mojo wedge D 6 3 1 7 3 1 5 2 1
```

A successful job must report a complete symbolic graph in a certified quadrant
and exact graph equality at the engine's two cross-check points. A failure is
also useful evidence: it names the first uncaptured sign, changing graph, run
bound or state-cap obstruction. No failure is to be interpreted as a
counterexample to boundary hitting unless the exact mathematical predicate
itself is falsified.

## 4. Acceptance after a successful run

Success of a wedge core alone is not yet the whole quadrant if the engine moves
its certified corner to `a>=a0, c>=c0`. The finite strips outside that core
must then be certified by the engine's exact boundary-line mechanism, exactly
as in Theorem W. The result can be promoted only after those strips are pinned
and replayed.

If both wedges and all required strips certify, class-D boundary hitting is
closed completely by combining:

- Corollary W1 for `r>=q-1`;
- PR #277 for both `b=0` residual boundaries;
- the two positive-b wedge certificates here.

That would close #139 on all determinant-two class D, not universal #139.

## 5. Firewalls

- no uniform contraction margin is assumed;
- no unimodularity is introduced;
- no projected path substitutes for an occurrence-labelled overlap path;
- the failed literal transport of the sealed `b=0` spine is not reused;
- no finite sample is a theorem;
- a capped/undecided exact run refuses promotion.

## 6. Rank-one b-direction and the occurrence compensation law

The positive-b direction adds one extra `y` to **every** image. In letter
order `(x,c,y)` the incidence matrix therefore has the exact form

```text
M(a,b) = M(a,0) + b e_y 1^T.
```

For an overlap offset vector `w` this gives

```text
M(a,b) w = M(a,0) w + b (1^T w) e_y.
```

Hence an occurrence-labelled child

```text
w' = M(a,b)w + prefix_bottom - prefix_top
```

can retain a b-independent target only if the selected prefix difference
absorbs the term

```text
-b (1^T w) e_y.
```

This is the exact compensation law. It explains the PR #277 negative control:
the sealed boundary row `(c,y,-2,4,-3)` has `1^T w=-1` and keeps FIRST/FIRST
prefixes, so it supplies no compensating `+b e_y` and the edge moves.

A successful two-parameter certificate therefore has only two legitimate
forms:

1. let the symbolic child state itself depend affinely on b; or
2. choose occurrence indices whose y-prefix difference changes by exactly
   `-b(1^T w)`.

No new quotient is needed. The existing ClassWedge engine already allows
affine state coordinates and affine run positions, so the candidate workflow
is testing precisely whether this compensation closes on a finite symbolic
family.

If the wedge engine fails, its first uncaptured run-position/sign decision
should be interpreted against this law before introducing any additional
state coordinate.

