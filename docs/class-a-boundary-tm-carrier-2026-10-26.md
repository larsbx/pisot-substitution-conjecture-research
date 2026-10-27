# Boundary T_m: all child kinds and a uniform 50-label image

Status: scoped exact child carrier for the two seed-derived T_m families;
not a globally forward-closed carrier or boundary-hitting theorem.
Independent human review pending. This completes the same child-kind
experiment authorized by the [existing three-source stop/go](class-a-boundary-child-carrier-2026-10-26.md).
No new spectral/tiling transfer or stronger hypothesis is introduced.

## Work shown

### Assumptions and hypotheses

Keep precisely the boundary chambers of PR #348 and the
[first/run and first/last calculation](class-a-boundary-first-run-2026-10-26.md).
Both actual seed run/run children have label `T_m=(y,y,-1,1,m)`,
`m=r,r+1`, with r=1 minus, r=2 plus k<=3, r=1 plus k>=4.
Write N=n+eps, L=N+1 for the actual last occurrence, and F=0.
Every run ordinal below is intersected with `1..N`; an empty interval means
no child. Retain ordered occurrence multiplicity rather than only letters.

### Derivation / reduction

Normalize Ly=1, `b=1-eps/beta`, `a=b+u`, `B=beta*(m-u)`.
The first/run/last child intervals have starts `0,a+i-1,a+N` and lengths
`a,1,b`. Subtraction gives the nine strict guards in the predecessor note.
The following table resolves **every** guard. In run/run columns delta=j-i;
other run columns give the run ordinal. First/first and first/last are the
previously derived predicates; no unstated child cases are discarded.

| Chamber / source | run/first i | run/run delta | run/last i | last/first | last/run j | last/last |
| --- | --- | --- | --- | --- | --- | --- |
| minus T_1 | none | t,t+1 | k+2..k+3 | no | none | t=0 |
| minus T_2 | k+3..k+5 | -k-5,-k-4 | none | t<=2 | t-2..t-1 | no |
| plus k<=3 T_2 | none | 3-k,4-k | n+k-2..n+k-1 | no | none | k=3 |
| plus k<=3 T_3 | n+k-1..N | none | none | yes | none | no |
| plus k>=4 T_1 | none | k+t+12,k+t+13 | k-7..k-6 | no | none | no |
| plus k>=4 T_2 | k-6..k-3 | 3-k,4-k | none | no | k+t+9..k+t+10 | k=4 |

Every endpoint is literal; the universal word clip is essential, for example
run/run minus T_2 has no child until t>=3 and plus T_1 until k>=8.
For a run/run delta, the complete range is
`max(1,1-delta)<=i<=min(N,N-delta)`, with j=i+delta.

Here is enough exact sign algebra to reconstruct the rounding in every row.
Put alpha=beta-(n+3+eps); the earlier coefficient certificate gives
`u-alpha=1+2eps/beta`.

* Minus: `B_1=-t-1+2/beta`, `B_2=k+4+w`, where
  `w=alpha+2/beta` satisfies 0<w<1. The new upper-bound identity is
  `beta^2*(1-w)=beta*(beta-t-5)+2>0`, since beta>t+k+5.
  Also `v=alpha+1/beta` lies in (0,1), as previously certified.
* Plus: `B_1=-k-t-12-2/beta`, `B_2=k-4+w`, with
  `w=alpha-2/beta` in (0,1) and `B_3=n+k+2v`,
  `v=alpha-1/beta`. At k>=4, 0<v<1; at k<=3, u>2 implies
  `v>1-3/beta>1/2` because beta>n+4>=8. All plus members satisfy
  `2/beta<alpha<1+2/beta`, proved coefficientwise in the predecessor.

For example run/first is `B-a<i<B+1`. For plus T_2 this is
`k-6-3/beta<i<k-3+w`, hence exactly i=k-6..k-3, clipped to the word.
Run/last is `B+N<i<B+N+b+1`. For minus T_1 its endpoints are
`k+1+2/beta` and `k+3+3/beta`, giving i=k+2..k+3.
Last/run is `N-B<j<N-B+1+b`; last/last is `-b<B<b`.
These open fractional bounds give the other table entries directly.

Two less immediate exclusions are retained explicitly. Plus T_3 has
`B_3>n+1`, so no run/run pairs can intersect: the largest compensating
run difference is -n. It has no last/run child either. For k>=1 its last/run
upper endpoint `3-k-2alpha+1/beta < 1-k+5/beta < 1`.
At k=0 the cubic gives
`(alpha-1)*beta=2-alpha+2/beta>1` using alpha<1+2/beta;
thus alpha>1+1/beta, and that upper endpoint is again <1.

Last/first requires `0<B-N<a+b`. Minus T_2 has
`B-N=2-t+w`, so precisely t<=2; the upper margin is always strict because
`B-N-(a+b)=-t-1+2/beta<0`. Plus T_3 has B-N>0 from v>1/2, and its
upper-margin difference equals B_2<0 on k<=3. Other cases are excluded by
the sign of B or B-N. Last/last minus T_1 reduces to t<3/beta, hence t=0.
Plus T_2 gives k=3 (negative B) and k=4 (positive B); the exact alpha bounds
exclude every other k. All these statements concern actual word children.

The full target offset is always
`(m-1,m+1,m*N-d)+prefix_bottom-prefix_top`, with
`prefix_F=(0,0,0)`, `prefix_run(i)=(1,0,i-1)`,
`prefix_L=(1,0,N)`. In particular every child has c=m+1>=2.

## The exact uniform image has 50 typed labels

Eliminating the parameters in the table gives the following finite image.
For each row, vary y over the inclusive integer interval. Tuples in the
middle columns are the first two Parikh coordinates (x,c), not tile types.

| Child types | (x,c) | y interval | Labels |
| --- | --- | --- | --- |
| x/x | (0,2) | -4..-3 | 2 |
| x/x | (1,3) | -9..-3 | 7 |
| x/y | (1,2) | -5..-2 | 4 |
| x/y | (2,3) | -9..-6 | 4 |
| x/c | (1,2) | -5..-2 | 4 |
| y/x | (0,3) | -5..-2 | 4 |
| y/x | (1,4) | -8..-6 | 3 |
| y/y | (0,2) | -3..-1 | 3 |
| y/y | (1,3) | -6..-5 | 2 |
| y/c | (0,2) | -3..-1 | 3 |
| y/c | (1,3) | -6..-5 | 2 |
| c/x | (0,3) | -5..-3 | 3 |
| c/x | (1,4) | -9..-6 | 4 |
| c/y | (1,3) | -6..-5 | 2 |
| c/c | (0,2) | -3 | 1 |
| c/c | (1,3) | -6..-5 | 2 |

The upper containment follows by substituting each allowed index range into
the full prefix formula, not from the sample union. Conversely every one of
these 50 labels has an actual exact finite witness. The native regression
reaches all 50 in k=0..9,t=0..4, and the independent receipt preserves one
complete occurrence witness for each. Thus 50 is the exact union over
chambers, **not** 50 children for each member. A member's exact selected
subpacket is synthesized by the guard table.

### Evidence and replay

Canonical `kernel/psc/class_a_boundary_tm_children.mojo` provides the full
predicate, an O(N) ordered-occurrence carrier, its 50-label envelope and
target verification. It enumerates at most two diagonal run/run index strips,
plus bounded endpoint ranges; it does not take an O(N^2) Cartesian product.
The native regression deliberately does enumerate every pair independently,
checks literal target transport against Perron geometry, verifies every
synthesized edge, rejects duplicates, and records attainment of all 50 labels.

Native: `kernel/tests/test_class_a_boundary_tm_children.mojo`, 100 members.
Independent oracle: `oracles/python/class_a_boundary_tm_children.py`,
182 members, 364 source cells, **133,042 ordered pairs / 6,370 accepted**.
All nine child kinds occur in that finite control. The receipt includes 50
typed labels and their actual eps,k,t,m,i,j witnesses. Every sign decision
is exact; the existing rational-refinement budget refuses instead of guessing.

From root:
```sh
python -m pytest -q tests/test_class_a_boundary_tm_children.py
python oracles/python/class_a_boundary_tm_children.py
python tools/make_proof_bank.py --check
```
From kernel/:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_tm_children.mojo
pixi run --locked mojo run -I . class_a_boundary_next_run.mojo
```
Dedicated native/Python acceptance remains head-specific. No Lean source or
governed theorem status changes in this increment.

### Negative controls

Nonexistent ordinals, altered target offsets, disjoint endpoint or run pairs,
duplicate synthesized occurrences, lost target labels and the old false
assumption that a word-legal child must intersect all refuse. All exclusions
and actual-word clips in the table are compared against exact geometry.

### Non-claims / remaining gaps

The table is complete for these two source families only. The 50 target
labels have not been proved forward closed or assigned a well-founded rank.
They have c>=2, outside the original seed star, so no closed obstruction or
zero-offset hit is inferred. Universal BH, A1-prime, G1 and PSC remain open.

The smallest explicit next source is `U=(x,y,1,2,-3)` on the entire minus
chamber. It is reached by actual ordered pairs `(1,2)` from the aligned
seed to T_1, then `(0,t+1)` from T_1 to U. Both strict overlaps and both
word bounds are already certified. Its descendants, and those of the other
49 image labels, require closure/descent work. This is a precise unbounded
next case rather than a claim that the two-level carrier finishes BH.
