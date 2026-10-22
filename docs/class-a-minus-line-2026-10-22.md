# Class A: uniform carrier closure and descent on the minus line (n+1, n, n-1) (2026-10-22)

**Status:** repository-proved, computer-assisted, scoped to the determinant-two
class-A minus line `(p,q,r)=(n+1,n,n-1)` for every integer `n>=1`; independent
human review pending. Every reachable overlap state of the canonical swap-seed
graph of this line has an offset-zero descendant: the strict-zipper obligation
of #139 is discharged on this second one-parameter family. Gaps `d>=2`, the
other class-A regions, the class-C residual, universal #139/#84, G1 and PSC
remain open. No ledger claim is promoted; the status is that of the certificate.

## Stop/go and scope

This is the sibling of [class-a-carrier-closure-2026-10-22.md](class-a-carrier-closure-2026-10-22.md)
(merged PR #310), which proved boundary hitting on the plus line
`(n+1,n,n+1)`. The targeted literature decision of
[p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md)
(Akiyama–Lee's finite overlap algorithm, Minervino–Thuswaldner's non-unit
representation, Barge's initial-letter theorem, which fails here because the
initial-letter map `(x,c,x)` is not injective) covers the whole determinant-two
class A, both signs; no new prior art bears on swapping the sign of the third
run, and nothing is imported. The [rectangle countermodel](class-a-cover-obstruction-2026-10-21.md)
remains the standing negative control: every check below is at typed-label level.

The minus line is a residual uniform family: in the domain `eps=-1`,
`n>=1, 1<=d<=2n-1` of the run-index note, the previously certified lines
`p=2q+k`, `k=0..3`, meet `d=1` only at `n<=1`. Concurrent open PR #311 records
the same two-sign Perron geometry `L` and `P(n,d,eps,h)`; the formulas below
are derived and checked independently here (two implementations, one of which
reads them off the characteristic polynomial) and nothing depends on #311.

Decision: **proceed** with the method of #310 on this one line, reusing its
certificate rather than re-implementing it. The certificate modules are now
parametrized by the line (`psc/class_a_line.mojo`); on the plus line their
outputs are byte-identical to the archived #310 receipts (below).

## Setting

Letters `(x,c,y)=(0,1,2)`, offsets bottom minus top, images

```text
sigma_n(x) = x y^(n+1) x,   sigma_n(c) = c y^n x,   sigma_n(y) = x y^(n-1) c.
```

The incidence matrix has columns `(2,0,n+1)`, `(1,1,n)`, `(1,1,n-1)`; its
characteristic polynomial is `chi(t)=t^3-(n+2)t^2+(n-2)t+2`. With `h=1/(beta-1)`,

```text
P(n,h) = h^3 chi(1+1/h) = 1 - (n-1) h - (n+3) h^2 - h^3 = 0,
hence  n h (1+h) = 1 + h - 3 h^2 - h^3.
```

`n^3 P(n,1/n) = -3n-1 < 0` and `(n+1)^3 P(n,1/(n+1)) = n^2-2 > 0` give
`1/(n+1) < h_n < 1/n` for `n>=2` (note: larger than on the plus line, where
`h_n < 1/(n+1)`); the certificate itself only uses `P(n0,1/n0)<0` together
with `P(n,0)=1` and monotonicity of `P` in `n` and in `h>0`, and re-proves
that inequality exactly before every run. The other two roots of `chi` lie in
the open unit disc, so the positive root of `P` is the Perron one.

Scaled left eigenvector: `L = (L_x, L_c, L_y) = (1+3h+h^2, 1+2h, 1+h)`, so
`L_x > L_c > L_y` (on the plus line `L_y > L_c`). The identity
`h M^T L - (1+h) L = -P (1,1,1)` holds coefficient-wise in `n` and `h`. With
`w=(k,c,y)`, `s=k+c+y`,

```text
T(w) = k L_x + c L_c + y L_y = s (1+2h) + k h(1+h) - y h,
```

and `(t,b,w)` is a strict overlap iff `-L_b < T(w) < L_t`.

**Children (Lemma 4 of #310, with the sign changes).** For top/bottom
segments FIRST/RUN/LAST of `sigma(t)`, `sigma(b)` with first-letter counts
`pi` and y counts `m`, the child is

```text
k' = k + s + (pi_x^b - pi_x^t),   c' = s - k + (pi_c^b - pi_c^t),
y' = k + n s - y + (m_b - m_t),    s' = 2 s + (pi^b - pi^t) + y',
```

because `M w = (k+s, s-k, n s + k - y)`. The y run of `sigma(y)` has length
`n-1`. At fixed segments and row index `j`, `T'` increases in `y'` with slope
`L_c - h = 1+h > 0` and in `j` with slope `h(1+h) > 0`; this is what the
window and gap arguments of #310 Theorem A need, and the realizable `j` for a
given `y'` again form an affine interval because `k` enters `y'` with slope 1
(gap `d=1`). For `d>=2` that slope is `d` and the argument does not apply;
`ALine` refuses any line but `d=1`, `eps=+-1`.

## Exact finite survey

`kernel/class_a_minus_line.mojo survey 24`: every complete graph completes under
the 20,000-state cap and every vertex reaches offset zero.

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 12 | 16 | 18 | 24 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| vertices | 174 | 204 | 274 | 300 | 338 | 378 | 418 | 458 | 618 | 778 | 858 | 1098 |
| max first hit | 5 | 5 | 5 | 6 | 7 | 7 | 8 | 9 | 11 | 14 | 15 | 19 |

Finite observations, not claims: the count is `40n+138` for `n>=5` and the
maximum first-hit depth equals `ceil(2n/3)+3` for `4<=n<=24`.

## The typed carrier (104 rows, 99 slices)

Grouping the labels of the exact exports `n=5..24` by `(top,bottom,s,y)` and
coalescing consecutive `k` gives the same number of maximal runs in every
slice and every export, with every run endpoint exactly affine in `n`
(`oracles/python/class_a_descent_table.py --line minus --rows-mojo`). That
synthesis is not evidence. The result, `kernel/psc/class_a_minus_carrier.mojo`,
has 104 rows `(top,bottom,s,y,a,b,c,d)`, `a n + b <= k <= c n + d`, and
`40n+138` labels. At `n=4` the graph has 300 vertices and two slices split
differently, so `n=4` is outside the table and is covered by its finite
certificate. One row, `(y,y,s=0,y=0)`, `-n <= k <= n`, has width `2n` (the
plus carrier has no row of slope 2).

## Theorem A' (uniform forward closure)

**Theorem A'.** For every integer `n>=8`: (i) every carrier label is a strict
overlap; (ii) the nine strict seed overlaps of the three oriented swap pairs are
carrier labels and the other three seed candidates are not strict overlaps;
(iii) every ordered child occurrence of every non-terminal carrier label is a
carrier label. Hence `G_n` is contained in the carrier `C_n`.

Proof. Exactly the proof of #310 Theorem A, with the line data above:
Lemma 1 (elimination of `n` with `n h(1+h)=1+h-3h^2-h^3`), Lemma 2 (exact
Sturm sign on `(0, 1/n0]`, refusing on a root or a vanishing bound), Lemma 3
(affine comparisons on the integer ray `n>=n0`), and the window/gap case split
over nine segment pairs and `|y'|<=5`. ∎

| Count | `n0 = 8` | `n0 = 10` |
| --- | ---: | ---: |
| rows / member sign pairs | 104 / 208 | 104 / 208 |
| segment pairs / `(row, segments, y')` cases | 936 / 10,296 | 936 / 10,296 |
| cases with a realizable range / gaps excluded by geometry | 4,508 / 3,842 | 4,446 / 3,780 |
| window sign checks / terminal splits | 1,872 / 65 | 1,872 / 65 |
| real seeds in carrier / non-strict seed candidates | 9 / 3 | 9 / 3 |
| conservative interval clips | 56 | 0 |

`n0=7` also closes (250 clips); `n0<=6` refuses (a terminal index enters a gap
for some `n` and not others), so `n<=7` is left to the finite certificates.

## Theorem B' (uniform descent) and Corollary C'

**Theorem B'.** For every integer `n>=8` there is a 176-piece affine potential
`X(n,j) = a n + b j + c >= 0` on the carrier (pieces partition each row; 8
pieces are the offset-zero targets) and 265 descent rows, each naming one
symbolic ordered child occurrence (top segment, bottom segment, `y'`, child
piece) of every member of an affine sub-interval, such that the occurrence is
realizable, parent and child are strict overlaps, the child lies in the named
piece, and `X_child <= X_parent - 1`. Hence every carrier label reaches offset
zero within `max X <= 2n+11` inflations.

Proof. `psc.class_a_carrier_descent.certify_descent_line`, unchanged from
#310 except for the line data: partition checks are affine identities, the
drop and non-negativity are affine-in-`n` inequalities on the ray, and
strictness at both ends of each affine sub-interval suffices because `T` is
affine increasing in `j`. ∎

The potential is not first-hit depth. On the target row `(y,y,0,0)` the
first-hit plateaus shift with `n mod 3` (right of the target the depths run
`2,3,4,5,6,6,7,8,8,...`, while at the row's left end `k=-n` they begin with
`0`, `3` or `4` unit decrements for `n = 2, 0, 1 (mod 3)`, exports `n=8..24`),
so no affine piece boundary fits the exact depth; the generator fits that row with `depth <= floor(X/3) <= depth+1`
instead. The verifier never uses depth: only non-negativity and the strict drop.

**Corollary C' (boundary hitting on the minus line).** For every integer
`n>=1`, every vertex of the complete canonical swap-seed overlap graph of
`(n+1,n,n-1)` has a finite offset-zero descendant. For `n>=8` this is
Theorems A' and B'; for `1<=n<=7` it is the exact complete-graph certificate
(all depths finite, graph complete under the cap), and for `5<=n<=7` the
carrier also equals the graph label set exactly.

## Work shown

### Assumptions and hypotheses

Determinant-two class-A normal form with `d=1`, `eps=-1`, i.e. exactly the
images above, `n>=1` (PIP is re-screened by `build_seed_overlap_tables_screened`
for every finite member and follows for all `n` from the run-index note's
domain). Canonical swap seeds, retained proper-prefix occurrence indices,
bottom-minus-top offsets, equal-letter offset-zero termination: the conventions
of #310, unchanged.

### Derivation / reduction

Above: `P`, `L`, `T`, the child update, the two monotonicities; then #310's
Lemmas 1–4 and the proofs of Theorems A and B with this line's data. The
eigen identity and elimination are checked coefficient-wise
(`check_line_identity`), and the Python verifier re-derives `P(n,h)` from the
characteristic polynomial of the incidence matrix it reads off the images.

### Evidence and replay

From `kernel/`:

```bash
pixi run --locked mojo run -I . tests/test_class_a_minus_line.mojo
pixi run --locked mojo run -I . class_a_minus_line.mojo certify 8
pixi run --locked mojo run -I . class_a_minus_line.mojo survey 24
pixi run --locked mojo run -I . tests/test_class_a_carrier_closure.mojo   # plus line, unchanged receipts
```

From the repository root:

```bash
python oracles/python/class_a_carrier_closure.py 8 --line minus
python -m pytest -q tests/test_class_a_minus_line.py tests/test_class_a_carrier_closure.py
sha256sum -c evidence/class-a-minus-line-2026-10-22/SHA256SUMS
```

Packet: `evidence/class-a-minus-line-2026-10-22/`. The Mojo certificate and the
independent Python verifier report identical counts. The plus-line native test
log, the plus oracle JSON and the plus generator output (from re-exported
graphs whose digests equal the archived ones) are byte-identical to the #310
packet, so the refactor changed no plus-line conclusion.

### Negative controls

`n0=6` closure and `n0=7` descent refuse; the minus carrier on the plus line
and the plus carrier on the minus line refuse; removing carrier row 0, 50 or
103 is an escape; a raised child potential, a removed descent row, a
mislabelled child `y'` and a wrong child piece refuse; `ALine(0)` refuses the
eigen identity; an exhausted cap refuses a verdict. The generator alone
(without the slack fit or the slope-two breakpoint) fails to produce a table:
recorded, not hidden.

### Non-claims / remaining gaps

Only `(n+1,n,n-1)`. Gap `d>=2` (where `y'` has slope `d` in `j` and realizable
indices form progressions; PRs #311/#312 investigate `d=2`), the other A
regions, the C residual `d>=4`, aligned #138, universal #139/#84, G1 and PSC
are open. The written argument is not Lean-formalized; independent human
review is pending. The finite-survey formulas are observations. The data-driven
generator is not evidence; the two verifiers are.
