# A1′ positive four-run / three-run tail: source review and literal witnesses

Date: 2026-11-14. This note reconstructs the source review and derivation
after the execution environment changed and the previous scratch checkout
became unavailable. The completed ordinary development source build is
recorded below; independent endpoint auditing and hosted acceptance are
separate gates.

## Target and prior scope

The target is the positive-sign Theorem K family F pattern
`zyzy + y^Delta | zyz` in `docs/p1a-a1-prime-2026-10-05.md`:

```
sigma(o)=y,
sigma(y)=o z^a y^b z^c y^(d+Delta) o,
sigma(z)=o z^r y^(b+d) z^t o,
a,b,c,d,r,t >= 1, r+t=a+c-1.
```

The full A1′ note through Theorem Zeta and the October 6–8 side-notes
ledger were reviewed before proof implementation. The previously considered
two-run pattern `(zy | yz)` is already closed by Psi; `(zy | zyz)` was
closed by the later `z_floor` sweep. Both were dropped. The present four-run
positive pattern remains among the October 8 timeouts; a timeout is not a
negative mathematical conclusion. Zeta already closes positive `Z_2<=2`,
so the first genuinely new residual case is `Z_2=3`.

## Primary-source stop/go

1. Marcy Barge, *Pure discrete spectrum for a class of one-dimensional
   substitution tiling systems*, Theorem 3.13 and Remark 3.14,
   https://arxiv.org/pdf/1403.7826. Initial-letter injectivity and an
   eventual common final letter are load-bearing. The endpoint maps of
   family F alternate `(y,o,o)` and `(o,y,y)` under powers, so the theorem
   does not supply the proposed result.
2. Tarek Sellami, *Balanced pair algorithm for a class of cubic
   substitutions*, Turkish Journal of Mathematics 39 (2015), 91–102,
   https://journals.tubitak.gov.tr/math/vol39/iss1/9/,
   DOI `10.3906/mat-1407-3`. The publisher statement concerns two unimodular
   beta-substitutions with the same incidence matrix and cubic
   `X^3-aX^2-bX-1`. Its uniform certificate method is relevant, but the
   present determinant-two family does not meet that contract. The
   publisher PDF returned 403; no fresh full-text inspection is claimed.
3. Shigeki Akiyama and Jeong-Yup Lee, *Overlap coincidence to strong
   coincidence in substitution tiling dynamics*, Corollary 4.5,
   https://arxiv.org/pdf/1403.0377. This gives prefix coincidence after
   overlap coincidence is established; that premise is unavailable here.

Proceed with literal ordered-word witnesses. No novelty is claimed for
Parikh bookkeeping, marked inflation, or parametric certificates.

## Complete parameter reduction

This reduction assumes the primitive irreducible Pisot hypotheses of
Theorem K. For its positive sign, existing Lemma Phi4 first gives
`Delta>=0`. Put `e=b+d`, `Z=r+t=a+c-1`. Existing Phi2/Phi6 in the A1′ note remove:

* `a<=r`: the prefix walks cross at positions `a+1` and `a`.
* `a=r+1`: the common point `t=a=r+1` has next letters `(y,y)`;
  the last z followed by the final `y^Delta` supplies the proper factor
  needed by Phi6.
* `a>=r+2` and `e>=Delta`: the first common baseline point has letters
  `(z,z)`, and a proper factor adjacent to the middle y-run of `w_2` has
  the required Parikh vector `Delta e_y+e_z`.

The residue has `a>=r+2`, hence `Z>=3`, and `Delta=e+j`, `j>=1`.
The necessary Pisot inequality is

```
f(1)=(Z-1)(Delta-1)-2e-4<0,
```

equivalently, on integers,

```
(Z-3)e+(Z-1)(j-1)<=3.
```

Since `e>=2`, `Z>=5` is impossible. At `Z=3`, `j` is 1 or 2 and the
only residual split is `(a,c,r,t)=(3,1,1,2)`. At `Z=4`, `j=1`, `e=2`
or `3`, and

```
(a,c,r,t) in {(3,2,1,3),(4,1,1,3),(4,1,2,2)},
(b,d) in {(1,1),(1,2),(2,1)}.
```

This reduction was independently checked by the coordinating researcher and
by a second source review of the existing Phi2/Phi6 statements. In the
`a=r+1` case the selected point is not the first common point: `t=1` is
already common with letters `(z,z)`. The argument uses the specified later
point `t=a` with letters `(y,y)`.
Unless Phi2/Phi6 and the reduction are formalized too, the whole run-shape
corollary is a mathematical combination of cited lemmas with new Lean
endpoints, not a single Lean theorem covering the whole shape.

## The Z=3, j=1 six-level witness

For `e>=2`, allow arbitrary words `v,w` with
`pi(v)=(0,2e-2,1)`, `pi(w)=(0,e-2,2)`, and literal images

```
sigma(o)=y,
sigma(y)=o z z z y v y y o,
sigma(z)=o z y y w o.
```

The top address is `[0,4,2e+5,2e+4,2e+5,2e+6]` and the bottom address
is `[1,3,0,0,2,e+4]`. Their successive top-minus-bottom residuals are

```
0, -e_o, 2(e_z-e_y), e_o-2e_y+2e_z,
e_o-2e_y+2e_z, e_z-e_y, 0.
```

The selected letter pairs are `(o,y),(y,z),(y,y),(y,o),(y,y),(y,z),(o,o)`.
Only the stated endpoint letters and exact middle counts are used.
The original layer is obtained with positive `b,d`, `e=b+d`,
`v=y^(b-1) z y^(b+2d-1)` and `w=y^(b+d-2) z z`.

## The Z=3, j=2 six-level witness

Take positive `b,d`, `e=b+d`, and

```
sigma(o)=y,
sigma(y)=o z^3 y^b z y^(b+2d+2) o,
sigma(z)=o w o, pi(w)=(0,e,3).
```

The entire middle of the z image may be reordered. The top address is
`[0,e+5,e+6,e+6,2e+6,2e+7]`; the bottom is `[2,0,0,4,2,e+4]`.
Residuals are

```
0, -e_o-e_z, -e_o-e_y+e_z, e_o-2e_y+3e_z,
2e_o-2e_y+2e_z, -e_y+e_z, 0.
```

The two middle top prefixes have counts `(1,e,4)` and `(1,e+1,4)`;
`d>=1` places their following y letters in the final run. No position
inside the arbitrary z-image middle is selected.

The independent arithmetic target, recorded before implementation, is

```
M_(e,j)=[[0,2,2],[1,2e+j,e],[0,4,3]],
chi_(e,j)=X^3-(2e+j+3)X^2+(2e+3j-2)X-2,
e>=2, j in {1,2}.
```

Primitivity, irreducibility, and Pisot root location must be proved for the
actual incidence matrix derived from these word images, without numerical
root approximation or an unrelated-matrix assumption.

## Uniform three-level replacement for the nine Z=4 literals

The original expanded target was the nine residual literals above. Before
their proof implementation, a stronger uniform certificate was found.
With positive `b,d`, `e=b+d`, `Delta=e+1`, the following addresses work:

| `(a,c,r,t)` | Top address | Bottom address | Common letter |
| --- | --- | --- | --- |
| `(3,2,1,3)` or `(4,1,1,3)` | `[0,e+7,b+8]` | `[2,2,b+6]` | `y` |
| `(4,1,2,2)` | `[0,e+8,5]` | `[2,3,e+5]` | `y` |

Both first steps give `(-1,0,-1)`. In the first row, the next residual
is `(-2,0,0)`; the last step selects y occurrences two places apart in
the final y-run, cancelling the inflated residual `(0,-2,0)`.
In the second row, the next residual is `(-2,1,-1)`; its inflation is
`(0,e-1,1)`. The final prefix counts are `(1,0,4)` and `(1,e-1,5)`,
which cancel it exactly. The guard `d>=1` ensures the latter prefix is
past the final z and before a selected y. These identities hold even
outside the Pisot residue; no all-parameter Pisot assertion is made there.

The pinned Mojo reader calibration was unavailable. Its first invocation
could not locate the standard library; automatic approval review then
rejected the compiler environment because it may emit external telemetry
containing a locally stored identifier. No compiler retry occurred after
the rejection. A small bounded exact-integer calculation in the
orchestration runtime suggested these positive witnesses; their prefix
counts and cancellations were then reconstructed algebraically. This is
discovery evidence only. Acceptance requires Lean proofs of actual
iterated-word prefix factorizations using marked inflation.

## Scope

The planned completion adapter uses the literal first-letter map
`(y,o,o)` and gives simultaneous coincidence at one common depth. If
`sigma^n(o)=p c u` and `sigma^n(y)=q c t` with `pi(p)=pi(q)`, then at
depth `n+1` the three images have respective prefixes `(q,p,p)`, all
followed by `c`. The suffixes are `t`, `u sigma^n(tail(sigma(y)))`, and
`u sigma^n(tail(sigma(z)))`. This is a literal append/iterate identity.
Thus the two six-level residual endpoints give simultaneous shared prefix
witnesses at depth seven, and the Z=4 endpoint gives them at depth four.
The intended formal quantifier order is `exists prefix suffix, forall a`,
with a single common letter and pairwise equal Parikh prefix vectors.

### Additional hand derivation, not an added Lean endpoint

The first Z=4 address formula is independent of Z and of the total y count
in the y image. Let `a>=2`, `b,c,d>=1`, `Delta>=2`, `e=b+d`, `N=a+c`,
and take

```
sigma(o)=y,
sigma(y)=o z^a y^b z^c y^(d+Delta) o,
sigma(z)=o z y^e z^(N-2) o.
```

Then the top address `[0,e+N+2,b+N+3]` and bottom address
`[2,2,b+N+1]` give a third-iterate y coincidence. The first residual is
`-e_o-e_z`. Its inflation has coordinates `(-2,-e-1,-N+1)`; the second
digit prefixes have counts `(1,e+1,N)` and `(1,0,1)`, leaving `-2e_o`.
The final prefixes lie two y letters apart in the final run, so they
cancel `M(-2e_o)=-2e_y`.

The second top mark has final-run offset `d+1`; `Delta>=2` makes it a
genuine selected y. The third top mark has final-run offset two;
`d+Delta>=3` makes that selected y genuine as well. This also gives a
three-level hand witness on the original ordered Z=3 boundary layers.
It does not replace the six-level arbitrary-middle statements, whose
orders are less restricted. The formula is recorded for future reuse;
the current compiled source has the narrower stated scope, and no separate
kernel acceptance is claimed for this larger statement.

No universal A1′, no BH, no balanced-pair finiteness, and no PSC conclusion
is asserted by these family results. Every claimed actual prefix endpoint
must pass source compilation and axiom auditing before promotion.

## Completed development source replay

The final `A1PrimeTailCoincidence.lean` source has SHA-256
`f1c4480b95159800bb52cd42164763d01e6ab6045dc72b07874f164409a0eaf1`.
An ordinary pinned Lean 4.34.0-rc2 / repository-pinned Mathlib development
build completed with terminal exit zero in 10.167120 seconds, with the
source unchanged during execution. This is
[attempt 6](../evidence/bh-finite-reachability-2026-11-14/development/a1-coincidence/coincidence-attempt-6.json).
Its source snapshot and log are retained beside the receipt. No result
depends on merely finding an object file without a terminal compiler exit.

The source exposes actual residual-pair factorizations through
`six_level_coincidence`, `second_layer_six_level`, and `z4_three_level`.
The endpoints `first_layer_simultaneous`, `second_layer_simultaneous`, and
`z4_simultaneous` choose shared prefix and suffix functions before
quantifying over all three letters, at common depths seven, seven, and
four respectively. The common letters are o, o, and y. The independent
arithmetic lemma `residual_parameter_cases` proves the exact Z/j/e
classification stated above.

Recovered-environment attempts 1–3 failed on tactic elaboration and
definitional-reduction issues; attempt 4 passed the core witness module.
Attempt 5 failed only while adding the common-depth adapter, and attempt 6
passed the complete source. All six terminal receipts and logs are
retained. Source snapshots were captured for attempts 2–6; attempt 1 has
its source hash but no separately captured source snapshot. The lost prior
environment receives no successful replay credit. The final source emits
nonsemantic tactic-style warnings; none changes its proved statements.

The independent literal-type and axiom audit also completed with terminal
exit zero: [audit receipt](../evidence/bh-finite-reachability-2026-11-14/development/a1-arithmetic/audit-001.json),
[audit log](../evidence/bh-finite-reachability-2026-11-14/development/a1-arithmetic/audit-001.log).
It checked 15 independently stated endpoint types and rejected 30 negative
controls. Across the coincidence and arithmetic modules it scanned 249
declarations, including 189 theorems; the coincidence module contributed
179 declarations and 125 theorems. Every audited declaration used only
`propext`, `Classical.choice`, and `Quot.sound`, or a subset. The
[full arithmetic replay](../evidence/bh-finite-reachability-2026-11-14/development/a1-arithmetic/pisot-002.json)
separately bound the primitive irreducible Pisot conclusions to the actual
two Z=3 word families and checked the residual run-split reduction.
These are local source-bound results; the repository's fresh isolated and
hosted acceptance stages remain the coordinating integration workflow.
