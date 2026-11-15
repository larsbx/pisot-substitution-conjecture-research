# Plus Class A: eight upper-cycle occurrence exits

Date: November 15, 2026 (America/New_York).
Problem source: [the deferred upper-entry memo](class-a-plus-upper-entry-target-2026-11-14.md)
at PR #581, `9f0138d213357b866e7ceef0dcbfab96a667526d`.
Integration base: main `a19670c521927a8f6ac7e08f26cd3d563eafdce3`.
Renewed [source and hypothesis gate](bh-class-a-plus-upper-cycles-stop-go-2026-11-15.md).

## Result and scope

**All eight remaining upper-cycle occurrence cases admit uniform symbolic
paths for every `n>=7`.** The paths use actual FIRST and RUN positions in
the original image words, preserve every integral coordinate and finish at
typed `y/y` coincidence. There is no exceptional list of values of `n`.

A two-edge decrement through an actual `x/y` packet replaces the failed
RUN-only proposal. It works whenever `JH>=3` in the wider upper amplitude
chamber. Two three-edge base formulas cover the remaining three pairs.
For the eight requested cases the complete depths are
`3,3,5,7,3,5,2,2`, respectively. Genuine track reversal supplies the negative
sources at the same depths.

The quantifiers of the contributions remain distinct:

| Contribution | Scope |
| --- | --- |
| Written two-edge decrement | `n>=7`, `1<=J<=n+7`, `H>=1`, `JH>=3`, `vH<1/2` |
| Written complete eight-case theorem | Every `n>=7`, the eight listed `(J,H)` pairs, both orientations |
| Canonical executable interface | The eight cases, checked arithmetic and explicit finite resource bounds |
| Lean endpoint | The eight cases for unbounded `n>=7`; literal ordered paths and traced prefixes; strictness under explicit positive inflation data |
| Independent exact replay | The fixed finite grid documented below, with complete original prefixes |

This local result starts at the stated cycle packets. It does not establish
that an arbitrary central trajectory reaches one of them, or that an
arbitrary strict source enters the central region. The recurrence,
all-source entrance, small-member and universal BH obligations remain open
here.

## 1. Literal words, coordinates and lengths

Use ordered coordinates `(x,c,y)` and the literal words

```text
sigma(x) = x y^(n+d) x,
sigma(c) = c y^n x,
sigma(y) = x y^(n+1) c.
```

Throughout the written upper decrement set

```text
n>=7, J=2n+12-d, 1<=J<=n+7,
chi(X)=X^3-(n+4)X^2+(J-n-7)X-2.
```

There is a unique root `beta` in `(n+4,n+6)`: the exact values and derivative
bound are

```text
chi(n+4) = (J-n-7)(n+4)-2 < 0,
chi(n+6) = (n+6)(n+5+J)-2 > 0,
chi'(X) >= n^2+7n+9+J > 0  for X>=n+4.
```

Put

```text
h=1/beta, v=J/(beta+1),
Ly=1, Lc=1-h, Lx=3+3h-v.
```

These agree with the deferred memo's eigenlengths because
`v=2+4h-d/(beta-1)`. The cubic gives `beta=n+5+2h-v`, from which

```text
beta Lx = 2Lx+(n+d),
beta Lc = Lc+n+Lx,
beta Ly = Lx+(n+1)+Lc.
```

All three lengths are positive: `0<h<1/11` and
`v<(n+7)/(n+5)<2`, so `Lx>1`. Thus the root yields actual positive
substitution scaling. The local path proof uses that scaling and the
explicit bounds, without a recurrence theorem, half-tie exclusion, seed
reachability, finite carrier or spectral consequence.

All original indices are zero-based:

| Parent | FIRST | RUN | LAST |
| --- | --- | --- | --- |
| `x` | `0:x` | `1..n+d:y` | `n+d+1:x` |
| `c` | `0:c` | `1..n:y` | `n+1:x` |
| `y` | `0:x` | `1..n+1:y` | `n+2:c` |

Write `e_x=(1,0,0)`, `e_y=(0,0,1)`. The FIRST prefix is zero. At a RUN
index `i` in either `sigma(x)` or `sigma(y)`, the original prefix is
`e_x+(i-1)e_y`. In `sigma(c)` it is `(0,1,i-1)`; changing a parent letter
therefore changes its prefix map.

The bottom-minus-top transport is

```text
M(p,q,r)=(2p+q+r,q+r,(n+d)p+nq+(n+1)r),
w'=M w+bottomPrefix-topPrefix.
```

The typed packet `ab(p,q,r)` has shift `u=Lx*p+Lc*q+r` and is strict
exactly when `-Lb<u<La`. Define

```text
W_H=yy(H,3H,-6H), with physical shift -vH.
```

For the wider decrement assume `H>=1` and `vH<1/2`. Centrality of all eight
requested sources is automatic: `JH<=4` and `beta+1>n+5>=12`.

## 2. Uniform two-edge decrement

Let `s=JH>=3`. The actual path is

```text
W_H
  --(0,s-2)----> xy(1-H,-3H,6H-3)
  --(s-J+4,1)-> W_(H-1).
```

The first top occurrence is FIRST `x`; its bottom occurrence is RUN `y`.
The next top occurrence is a RUN in `sigma(x)`, not `sigma(y)`.

### Complete offsets

The first incidence image is

```text
M(H,3H,-6H)=(-H,-3H,(6-J)H).
```

Adding the exact prefix difference `(1,0,s-3)` gives the stated `x/y`
packet. Its incidence image is

```text
M(1-H,-3H,6H-3)=(H-1,3H-3,(J-6)H+9-J).
```

The next prefix difference is `(0,0,-(s-J+3))`. This gives
`(H-1,3H-3,-6H+6)`, with both terminal letters `y`.

### Literal index bounds

Since `s<(beta+1)/2<(n+7)/2<=n`, the integer `s` satisfies `s<=n-1`.
Therefore

```text
1<=s-2<=n-3<n+1,
4<=s-J+4=J(H-1)+4<=n+2<=n+d.
```

Every position is a genuine original RUN occurrence, including `s=3,4`
and `n=7`.

### Strictness and composition

The three shifts are `-vH`, `3h+v(H-1)` and `-v(H-1)`.
The first and last are central. The middle shift is positive and

```text
Lx-(3h+v(H-1))=3-vH>5/2.
```

It lies strictly between `-Ly` and `Lx`. The target is positive
`W_(H-1)`, so decrements concatenate without alternating the track order.

This also handles the memo's larger `JH>=5` cycle heights. That wider
written lemma is deliberately separate from the eight-case executable and
formal scope. It supplies no eventual-tail or all-source argument.

## 3. Exceptional bases

### `J=1`, `H=1` or `2`

Here `d=2n+11`. Use

```text
W_H
  --(0,0)-------------> xx(-H,-3H,5H)
  --(1,1+(n+4)H)-----> yy(0,2H,-2H)
  --(1,2H+1)---------> yy(0,0,0).
```

The complete incidence images are

```text
M W_H=(-H,-3H,5H),
M(-H,-3H,5H)=(0,2H,-(n+6)H),
M(0,2H,-2H)=(0,0,-2H).
```

The corresponding original prefix differences are zero,
`(0,0,(n+4)H)` and `(0,0,2H)`. The second bottom index obeys
`1+(n+4)H<=2n+9<=3n+11=n+d`; the last bottom index obeys
`2H+1<=5<=n+1`.

The shifts are `-vH`, `-H+vH`, `-2Hh` and zero. For the `x/x` state,

```text
Lx-H+vH=3-H+3h+v(H-1)>0.
```

Its negative shift is therefore strictly inside the `x/x` overlap
interval. The next `y/y` packet is strict because `2Hh<=4h<1`.

### `J=2`, `H=1`

Here `d=2n+10`. Use

```text
W_1
  --(0,0)-------> xx(-1,-3,4)
  --(0,2n+6)---> xy(0,1,-1)
  --(1,2)-------> yy(0,0,0).
```

The complete incidence images are

```text
M W_1=(-1,-3,4),
M(-1,-3,4)=(-1,1,-2n-6),
M(0,1,-1)=(0,0,-1).
```

The prefix differences are zero, `(1,0,2n+5)` and `(0,0,1)`.
The second top occurrence is FIRST `x`, with zero prefix.
The second bottom RUN belongs to `sigma(x)` since `2n+6<=3n+10=n+d`.
The last two positions are RUN occurrences.

The shifts are `-v`, `-2+v`, `-h` and zero. The `x/x` state is strict
because `Lx-2+v=1+3h>0`; the `x/y` state is strict because
`-1<-h<0<Lx`.

## 4. Complete eight-case transcript table

Each index pair is `(topIndex,bottomIndex)` in the current parent words.
The targets are listed in the same order. `yy0` denotes the full packet
`yy(0,0,0)`.

| `J,H` | Depth | Original ordered indices | Complete typed targets |
| --- | ---: | --- | --- |
| `1,1` | 3 | `(0,0);(1,n+5);(1,3)` | `xx(-1,-3,5);yy(0,2,-2);yy0` |
| `1,2` | 3 | `(0,0);(1,2n+9);(1,5)` | `xx(-2,-6,10);yy(0,4,-4);yy0` |
| `1,3` | 5 | `(0,1);(6,1);(0,0);(1,2n+9);(1,5)` | `xy(-2,-9,15);yy(2,6,-12);xx(-2,-6,10);yy(0,4,-4);yy0` |
| `1,4` | 7 | `(0,2);(7,1);(0,1);(6,1);(0,0);(1,2n+9);(1,5)` | `xy(-3,-12,21);yy(3,9,-18);xy(-2,-9,15);yy(2,6,-12);xx(-2,-6,10);yy(0,4,-4);yy0` |
| `2,1` | 3 | `(0,0);(0,2n+6);(1,2)` | `xx(-1,-3,4);xy(0,1,-1);yy0` |
| `2,2` | 5 | `(0,2);(6,1);(0,0);(0,2n+6);(1,2)` | `xy(-1,-6,9);yy(1,3,-6);xx(-1,-3,4);xy(0,1,-1);yy0` |
| `3,1` | 2 | `(0,1);(4,1)` | `xy(0,-3,3);yy0` |
| `4,1` | 2 | `(0,2);(4,1)` | `xy(0,-3,3);yy0` |

Every preterminal full vector is nonzero. Thus the paths stop at their
first integral zero, which is also typed coincidence. The same matrix
coordinates at `J=3` and `J=4` do not identify their different substitutions
or first indices.

## 5. Exact original prefix identities

For edge `t` let `p_t,q_t` be the original top and bottom proper-prefix
Parikh vectors. Set

```text
P_0=Q_0=0,
P_(t+1)=M P_t+p_t,
Q_(t+1)=M Q_t+q_t.
```

These are actual prefixes of the iterated source words. At each stage the
next selected occurrence lies in the inflation of the previously selected
letter; induction both establishes this word-level statement and gives

```text
w_t=M^t W_H+Q_t-P_t.
```

At typed zero, `M^m W_H=P-Q` for the specific original prefixes constructed
by that transcript. To display the full vectors compactly, capital symbols
below denote pairs `(P,Q)`. Matrix multiplication and addition act on both
triples componentwise, with the fixed `J,d` for the row in question.

For one two-edge decrement, define `E_(J,s)=(P_E,Q_E)` by

```text
P_E=(1,0,s-J+3),
Q_E=(s,s-3,(n+1)s+9-J).
```

The two local prefix pairs are `(0,(1,0,s-3))` and
`((1,0,s-J+3),(1,0,0))`. Hence

```text
M^2 W_H=P_E-Q_E+W_(H-1),
P_E-Q_E=(1-s,3-s,-ns-6).
```

For the `J=1` base write `A_H=(P_A,Q_A)`:

```text
P_A=(3,0,3n+11),
Q_A=(3+(n+4)H,(n+4)H,3n+11+H(n+2)(n+3)).
```

For the `J=2,H=1` base write `B=(P_B,Q_B)`:

```text
P_B=(1,0,0),
Q_B=(2n+8,2n+5,2n^2+10n+16).
```

Thus every requested path has the following complete original prefix pair:

| `J,H` | `m` | `(P,Q)`, satisfying `M^m W_H=P-Q` |
| --- | ---: | --- |
| `1,1` | 3 | `A_1` |
| `1,2` | 3 | `A_2` |
| `1,3` | 5 | `M^3 E_(1,3)+A_2` |
| `1,4` | 7 | `M^5 E_(1,4)+M^3 E_(1,3)+A_2` |
| `2,1` | 3 | `B` |
| `2,2` | 5 | `M^3 E_(2,4)+B` |
| `3,1` | 2 | `E_(3,3)` |
| `4,1` | 2 | `E_(4,4)` |

All three coordinates remain present. Matrix notation avoids long expanded
polynomials without projecting onto a physical shift or losing the `c`
coordinate. The actual original prefix pair is fixed by its complete
occurrence transcript.

Track reversal maps `ab(w)` to `ba(-w)`, exchanges every original pair
`(i,j)` with `(j,i)`, and swaps `P,Q`. Its identity is therefore
`M^m(-W_H)=Q-P`. Negating coordinates without exchanging occurrences is
not a valid reversal.

## 6. Exact replay, formal interface and provenance

The self-contained independent oracle is
[`class_a_plus_upper_independent.py`](../oracles/python/class_a_plus_upper_independent.py).
It counts literal words and imports no PSC arithmetic or path code. With
`a=3p+q+r` and `b=3p-q`, it decides a shift sign using the exact numerator

```text
a beta^2+(a+b-Jp) beta+b
  = beta(beta+1)*(Lx*p+Lc*q+r).
```

All coefficients and interval endpoints are exact integers or rationals.
The checker validates the cubic bracket, literal Parikh columns and actual
positive scaling. Each member permits at most 256 root refinements and
50,000 original occurrences; exhaustion returns no verdict.

The **fresh replacement-environment run** covers
`n=7..65,127,255,1024,4096`, all eight cases and both orientations:
**1,008 complete paths, 3,780 edges and maximum depth seven**. It verifies
strictness, literal types, original indices and both complete prefixes at
every step. Eight corrupted certificates are refused: wrong middle type,
negative index, index past LAST, truncated path, false zero, noncomposable
middle, wrong original prefix, and continued zero. Two further controls
require resource refusals. All accepted path signs separate on the initial
root bracket, so zero refinements were needed for them.

Replay into a new or empty directory:

```sh
python oracles/python/class_a_plus_upper_independent.py \
  --output-dir /tmp/psc-plus-upper-independent-replay
```

Fresh files are in the
[independent replay packet](../evidence/class-a-plus-upper-cycles-2026-11-15/independent-replay/summary.json),
with a complete transcript, immutable source snapshot and manifest.
The exact restored source SHA-256 is
`b8b6b93423ac4baf67660ed3d8d3f26c40ca1f1b867afe8e931164fa1aaee579`;
the fresh transcript SHA-256 is
`e843be77ee0d174c79ea6aeb02b5de6e6b235b9fb683653dd68c17b570bc488b`.
Both match the digests recorded before the earlier environment became
unavailable. That match is verified anew; **the old raw files are not
claimed to survive**. The new packet is a fresh execution, and no old
unarchived native or Lean receipt substitutes for current acceptance.

The largest independently checked original-prefix coordinate is
`19015488163671150150991`, which exceeds `Int64`. The oracle's unbounded
integers do not confer acceptance on native machine-integer examples that
would exceed their checked arithmetic bounds.

The formal target uses the same indexed paths, both original `MarkTrace`
witnesses and complete incidence powers. The packet convention stores
`delta=-w`, so the original identity uses `M^m*(-delta)=P-Q`.
Positive tile lengths and inflation scaling are explicit at the strict
path endpoint; strictness can be pulled backward from the same typed-zero
transcript. The written root construction above supplies such lengths,
while automatic formal Perron identification is a separate obligation.
Fresh formal/native/hosted receipts, and the exact inherited source files,
are recorded by the integration evidence packet; compilation of one
endpoint does not accept the whole deferred upper theorem.

## 7. Preserved failure and remaining obligations

At `JH=4`, the retired RUN-only pair sequence begins `(1,4),(1,n+2)`.
Its second literal target is

```text
yc(H-1,3H-1,4-6H),
```

with shift `-2h-v(H-1)`. This is a strict mixed overlap, but its type is
`y/c`, and the next parent prefix map differs. At `JH<=3`, the retired
second bottom index is even beyond LAST. The new paths use different
actual occurrences and retain the correct types.

The next mathematical obligation is to connect arbitrary central sources
to the cycle consumer. The deferred upper-family assembly still needs:

1. The exact literal nearest-RUN recurrence, including half-tie exclusion
   and reconstruction of the complete state.
2. The proposed boundedness argument with both initial integer coordinates
   and the periodic-tail classification, with independent exact acceptance
   and a precise formal specialization.
3. An upper-specific all-source entrance proof retaining the packing
   estimates, boundary budgets, selected descendants and original ancestry.
4. The separate `n<=6` obligation and any necessary source/seed adapters.
5. Full formal/source-bound assembly and the required exact-head acceptance.

These local paths do not close universal BH #139, arbitrary-ternary
A1-prime, C4, PSC, an all-alphabet theorem or a spectral implication. The
broader two-edge written lemma, eight-case formal statement, finite replay,
hosted outcomes and independent human review keep their distinct status.
