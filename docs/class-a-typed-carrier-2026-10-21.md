# Class A: typed affine carrier and uniform graph-size lower bound (2026-10-21)

Status: **uniform lower-bound consequence of the established explicit run-index paths; candidate typed cover with exact finite verification only.** This is a next-step research artifact for #139, not a proof of arbitrary-n closure or boundary hitting. Independent human review remains pending.

## Literature and input gate

Reuse the scoped Akiyama–Lee, Minervino–Thuswaldner, and Barge stop/go decision in [p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md) and its exact prefix/strict-geometry conventions. No theorem about non-unit Rauzy realization or uniform coincidence is imported. The [rectangle failure](class-a-cover-obstruction-2026-10-21.md) rules out its untyped superset as an inductive cover; the new construction **retains letter types and the correlated coordinates**. Formal overlaps must not be identified with reachable overlaps on sampled parameters alone.

Work in the determinant-two PIP class-A line
`x -> x y^(n+1) x, c -> c y^n x, y -> x y^(n+1) c` for integer `n>=4`. The canonical graph starts from all three oriented swap pairs, retains proper-prefix occurrence indices, uses bottom-minus-top offsets, and terminates at equal-letter offset-zero coincidence.

## Uniform lower bound (proved from existing path identities)

**Proposition.** For every integer `n>=4`, the canonical exact swap-seed overlap graph has at least `6n-2` distinct vertices.

**Status:** proved (scoped uniform graph-size lower bound from existing coefficient-checked run-index paths and exact reversal symmetry; independent human review pending). This does not establish universal typed-carrier closure or arbitrary-parameter hitting.

The existing coefficient-checked formulas in [the run-index proof](p1b-class-a-run-index-2026-10-21.md) provide seed-reachable states
`A_k=(c,y,k,-k,0)` and `Y_k=(y,y,k,-k,0)` for `2<=k<=n`, and `B_k=(y,x,k,-k-1,1)` for `0<=k<=n`. The four-step bootstrap reaches `A_2`; the `Y_(k+1)` ladder reaches `A_n`; the exit from `A_n` reaches `B_n` and every `B_k` by descending edges. Every listed occurrence is strict, and the prior proof checks its zero-based indices for all `n>=4`.

Swap the two tracks and negate the offset: `(u,v,w) -> (v,u,-w)`. This maps every actual ordered occurrence to the reversed ordered occurrence and maps each canonical swap seed to its reverse, hence preserves reachability and strictness. The resulting mirror families are disjoint from the original families: the non-diagonal type pairs are reversed, and `Y_k` versus its mirror have opposite nonzero offsets. There are `(n-1)+(n-1)+(n+1)=3n-1` states before mirroring and `3n-1` after mirroring. Therefore `|G_n|>=6n-2` for all `n>=4`.

This is a uniform result about graph **complexity**, not a bound on first-hit depth or a proof of the remaining seedwise productivity premise. Together with the earlier `L(A_n)>n/10`, it rules out any literal fixed-cardinality carrier that must embed every reachable vertex injectively. It does not rule out finite symbolic quotient descriptions with unbounded integer indices.

## Typed affine carrier: precise candidate

Represent a state by `(top,bottom,k,c,y)` with integral offset `w=(k,c,y)`; let `s=k+c+y`. The candidate comprises **89 affine intervals in 75 typed slices**. Each eight-integer row in `kernel/psc/class_a_typed_carrier.mojo` means:

`(top, bottom, s, y, a, b, c, d)` includes `k` satisfying `a*n+b <= k <= c*n+d`, with the middle offset recovered as `s-k-y`.

These rows were *inferred* by grouping the already archived **exact complete n=4 and n=18 graph exports** by `(top,bottom,s,y)`, coalescing consecutive `k` values, and fitting endpoint slopes among `-1,0,1`. Two pairs of adjacent singletons coalesce at n=4 and split for larger n:
`(c,c,s=-1,y=0): k=1 or n-2`,
`(c,c,s=1,y=0): k=2-n or -1`.
The code retains them as separate singleton intervals. This is an *inferred candidate*, not an interpolation theorem.

An **exact symbolic counting identity**, obtained by adding `(upper-lower+1)` over all row intervals, gives `40n+115`. Within each typed slice the intervals are pairwise disjoint for integer `n>=4`; that follows by comparing their affine endpoints and their smallest separation at n=4. Therefore the candidate has exactly `40n+115` integral labels for every integer `n>=4`. **No claim is made that all those labels are real overlaps, seed-reachable, or hitting for arbitrary n.**

The former rectangle countermodel `V_n=(x,c,-n-1,n+4,-2)` has type `(x,c,s=1,y=-2)`, which is absent from the candidate's slices, as is its child `W_n` with `s=2`. This is *not* a proof of their uniform nonreachability: that would require parameter-uniform forward closure of the typed carrier.

## Exact finite checker and distinction from a theorem

The new canonical `kernel/psc/class_a_typed_carrier.mojo` enumerates **all** candidate labels at a selected `4<=n<=24`, builds the exact complete swap-seed graph with its 20,000-state fail-closed cap and Perron geometry, and checks:

1. Every candidate is a strict real overlap; no duplicate or malformed interval row is admitted.
2. The candidate and seed graph are identical *as labelled vertex sets*, not merely as counts.
3. Every actual ordered child of every nonterminal candidate stays inside the candidate, retaining both occurrence indices through the existing exact zipper reader.
4. Every canonical swap seed is included, and every complete-graph vertex has a finite offset-zero descendant.

For `n=4` and `18`, the original archived exact graph exports give `275` and `835` vertices, respectively, with all depths finite. Their independent Fraction-field replay is preserved in `oracles/python/class_a_run_index.py`. The extra `n=8` regression has expected `435` vertices, as in the accepted survey. **These are exact but finite checks.** Executing this new Mojo test on the branch and obtaining fresh CI results are still required before calling even those new checker runs accepted.

The checker deliberately refuses outside the specified parameter budget, any incomplete graph, a missing row, an extra real formal vertex, a bad occurrence child, and a negative first-hit depth. Removing a slice is an explicit negative control. It does not infer a universal closure by extrapolating a table.

Replay after obtaining the locked Mojo environment:

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_typed_carrier.mojo
pixi run --locked mojo run -I . class_a_typed_carrier.mojo 18
```

## Exact gap to close for Issue #139

The next **mathematical** obligation is to prove, for **every integer n>=4**, that this 89-row candidate contains every canonical seed, that every candidate is a valid strict overlap, and that *all actual ordered children* land in one of the rows, with no sampling or 20,000-state cap. This could be discharged by a finite family of exhaustive affine-index and exact Perron-root inequality cases with replayable certificates. The visible table of rows is an explicit quantified proof target; a finite sample is not a substitute. Once closure is established, find a parameter-dependent ranking or a guaranteed exit from every closed component, **not merely one path on the A/B/Y ladder**. The special s=±1 slices and the row-boundary/corner occurrences deserve separate counterexample controls.

This programme has not discharged the remaining A family regions or any C residual, and does not affect class D, aligned #138, general #139/#84, G1 or PSC. No governed theorem status or ledger promotion is justified by this candidate.
