# Plus Class A: central recurrence and complete occurrence exits

Date: November 15, 2026. This continues the
[deferred upper-entry target](class-a-plus-upper-entry-target-2026-11-14.md)
at `9f0138d213357b866e7ceef0dcbfab96a667526d` and the
[eight cycle exits](class-a-plus-upper-cycle-exits-2026-11-15.md) merged in
PR #583. The targeted
[primary-source stop/go](bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md)
was recorded before this increment's theorem-facing implementation.

## Result and scope

**Written central-source theorem.** For every integer `n>=7`, every
`n+5<=d<=2n+11`, and every integral `y/y` source whose normalized physical
shift has absolute value at most `1/2`, there is a finite composable path
of original ordered child occurrences to typed `y/y` zero. Every packet
on the path is strict. The path retains the complete integral vectors
and the original iterated-prefix identity. No finite list of exceptional
values of `n` is required within this scope.

The proof first realizes the strict nearest recurrence by literal RUN
indices. A finite invariant box gives boundedness from **both** initial
integral coordinates. Its periodic tails are constant after a parity
change. Full packet reconstruction then yields zero or an alternating
`W_H,-W_H` tail. The complete cycle exits use the two-edge decrement of
PR #583 at all admissible heights, followed by its two exceptional bases.

The following scopes remain distinct:

| Layer | Exact scope |
| --- | --- |
| Written proof below | Every integral central `y/y` source in the stated unbounded upper parameter family |
| Canonical executable constructor | Checked integer states, exact field predicates, unbounded prefix integers and explicit operational caps |
| Independent replay | The declared finite 818-source grid, with exact literal words, nearest indices and all prefix identities |
| Lean declarations | Only the exact statements established by their separately recorded source-isolated build and axiom audit |
| Still required for an upper all-source theorem | Entry from every strict source into this central domain, including all type and boundary cases |

An executable refusal is not a counterexample to the written theorem.
Finite replay is not a proof for all sources. This note supplies no
arbitrary-source entry theorem, no result for the separate `n<=6` upper
members, and no universal BH #139, A1-prime, C4, G1, PDS or PSC conclusion.

## 1. Exact family and positive lengths

Use coordinates `(x,c,y)`, bottom-minus-top offsets, and the actual words

```text
sigma(x)=x y^(n+d) x,
sigma(c)=c y^n x,
sigma(y)=x y^(n+1) c.
```

Set

```text
J=2n+12-d,                  1<=J<=n+7,
N=n+4,
chi(X)=X^3-N X^2+(J-n-7)X-2.
```

The root `beta` is uniquely specified by `n+4<beta<n+6`:

```text
chi(n+4)=(J-n-7)(n+4)-2<0,
chi(n+6)=(n+6)(n+5+J)-2>0,
chi'(X)>=n^2+7n+9+J>0 for X>=n+4.
```

There is no root in `1<X<=n+4`, since
`X^2(X-N)+(J-n-7)X-2<0` there. The only possible rational roots of this
monic cubic are `1,-1,2,-2`, and

```text
chi(1)=-d,
chi(-1)=-J,
chi(2)=-2(n+d),
chi(-2)=-2(n+J+6).
```

They are nonzero. Thus `beta` has degree three over the rationals.

Define

```text
h=1/beta,       A=2h,        C=beta-(n+4),
v=1+A-C=J/(beta+1),          beta=n+5+A-v,
Ly=1,          Lc=1-h,       Lx=3+3h-v=beta-n-2+h.
```

The identity for `v` follows by reducing against `chi(beta)=0`.
The lengths are positive, and `Lx<3+3/11<4`, `0<Lc<1`. Direct substitution
in the three literal Parikh columns gives

```text
beta Lx=2Lx+n+d,
beta Lc=Lc+n+Lx,
beta Ly=Lx+n+1+Lc.
```

Consequently these are positive substitution eigenlengths. If a positive
eigenlength row is supplied instead, normalization by its `Ly` gives the
same row: subtracting the `c` equation from the `y` equation yields
`beta(Ly-Lc)=Ly`; the `y` equation then gives
`Lx/Ly=beta-n-2+1/beta`. No unstated normalization or replacement field
is used.

The elementary coefficient bounds needed below are

```text
0<A<2/11<1/4,       C>0,       v>0,       C<1+A.
```

For `w=(p,q,r)`, write `u=Lx*p+Lc*q+r`. A typed packet `ab(w)` is strict
exactly when `-Lb<u<La`. The full incidence action is

```text
M(p,q,r)=(2p+q+r, q+r, (n+d)p+nq+(n+1)r).
```

## 2. Half-ties are excluded by the actual cubic

The exact identity

```text
beta*u=p*beta^2+(q+r-(n+2)*p)*beta+(p-q)             (1)
```

is essential. If `beta*u` were a half integer, twice (1) minus the
corresponding odd integer would be a quadratic polynomial vanishing at
`beta` with an odd constant coefficient. This contradicts degree three.
If `u` were a half integer, subtract the corresponding odd multiple of
`beta` instead; the resulting linear coefficient is odd. Thus physical
half-unit boundaries and nearest-gap ties are both absent on all integral
packets. In particular `|u|<=1/2` is equivalent to `|u|<1/2` here.

The scalar maps used below also have no half-ties on arbitrary integer
inputs. For example, if `-A*a+C*b=(2m+1)/2`, multiplication by `2beta`
gives

```text
2b*beta^2+(-2(n+4)b-(2m+1))*beta-4a=0,
```

again impossible because its linear coefficient is odd. The analogous
formula with `-C*b` has the same contradiction. Nearest rounding is
therefore single valued and commutes with negation on these inputs.
Likewise, (1) shows that an integral packet has zero physical shift only
when all three integral coordinates vanish; no projected-zero shortcut
is used to decide coincidence.

## 3. Literal nearest RUN realization

All positions are original zero-based indices:

| Parent | FIRST | RUN | LAST |
| --- | --- | --- | --- |
| `x` | `0:x` | `1..n+d:y` | `n+d+1:x` |
| `c` | `0:c` | `1..n:y` | `n+1:x` |
| `y` | `0:x` | `1..n+1:y` | `n+2:c` |

The prefix at a RUN index `i` in either `sigma(x)` or `sigma(y)` is
`(1,0,i-1)`. A `c` RUN instead has prefix `(0,1,i-1)`.

Let `e` be the unique nearest integer to `beta*u` for a central `y/y`
source. Choose

```text
i=1+max(e,0),       j=1+max(-e,0).                 (2)
```

Since the nearest error is strict,

```text
|e|<beta/2+1/2<(n+7)/2<=n.
```

Thus the integer `e` satisfies the stronger bound `|e|<=n-1`. Both
positions in (2) lie in `1..n`, hence are actual RUN `y` occurrences.
Their bottom-minus-top prefix difference is `(0,0,-e)`. The actual child
is

```text
w'=M w+(0,0,-e),       u'=beta*u-e,
```

so it is again strictly central, and therefore strict as a `y/y` packet.
This proves existence of the next literal step, not merely an equation
for a scalar surrogate.

Let `z_k` denote the successive first integral coordinates. Set

```text
z_0=p,             z_1=2p+q+r.
```

For `a=z_k`, `b=z_(k+1)`, `c=z_(k+2)`, the exact next packet is

```text
w_(k+1)=yy(b, b-2a, c-3b+2a),
u_(k+1)=c+C*b+A*a.                                 (3)
```

The first identity follows from the first two incidence coordinates and
the fact that a RUN difference changes only the third coordinate. The
second uses the explicit length row. Because `u_(k+1)` is central,

```text
z_(k+2)=nearest(-A*z_k-C*z_(k+1)).
```

Now set `t_k=(-1)^k z_k`. Unique nearest rounding and the absence of
half-ties give the autonomous relation

```text
t_(k+2)=nearest(-A*t_k+C*t_(k+1)),
epsilon_k=t_(k+2)-C*t_(k+1)+A*t_k, |epsilon_k|<1/2. (R)
```

This has the sign convention of `ClassAPlusConstantRecurrence.Nearest A C`.
An ordinary floor recurrence, a non-strict tie convention, or the
untransformed sign of `C` cannot be substituted for (R).

## 4. A finite bound retaining both initial coordinates

Let

```text
B=(n+7)(|t_0|+|t_1|+1)
 =(n+7)(|p|+|2p+q+r|+1).                           (4)
```

This is a positive integer. We prove `|t_k|<=B` for every `k` by an
elementary invariant box, with no infinite impulse series or complex-root
estimate.

### 4.1. The region `J>=5`

The exact family identity gives

```text
q0=1-A-C=v-4/beta
  =((J-4)beta-4)/(beta(beta+1))>0.
```

Also

```text
1/(2q0)<beta+1<n+7<=B.
```

The first strict inequality is equivalent to `(2J-9)beta>8`, which holds
because `J>=5` and `beta>11`. If two consecutive absolute values are at
most `B`, relation (R) gives

```text
|t_(k+2)|<(A+C)B+1/2<=B.
```

Both initial values are bounded by (4), so ordinary induction proves
the invariant.

### 4.2. The region `J<=4`

Here the preceding absolute coefficient contraction is false throughout
the region:

```text
beta(beta+1)(1-A-C)=(J-4)beta-4<0.                 (5)
```

Instead `v<1/3`, since `beta>11`. Hence

```text
beta=n+5+A-v>12-1/3=35/3>23/2,
A<4/23,        v<8/25,
A+v<284/575<1/2,
C=1+A-v>1/2+2A>3A.                               (6)
```

Use the sheared coordinate

```text
y_k=2t_(k+1)-t_k.
```

The exact finite updates are

```text
t_(k+1)=(t_k+y_k)/2,
y_(k+1)=(C-1/2-2A)t_k+(C-1/2)y_k+2epsilon_k.      (7)
```

Both coefficients in the second line are positive by (6), and their
sum is `1-2v`. The reserve (4) dominates both initial coordinates:
`|y_0|<=2|t_1|+|t_0|<=B`. Moreover

```text
v=J/(beta+1)>1/(n+7),       2vB>2>=1.
```

If `|t_k|,|y_k|<=B`, equations (7) imply

```text
|t_(k+1)|<=B,
|y_(k+1)|<(1-2v)B+1<=B.
```

This proves the sheared box by finite induction and in particular bounds
every `t_k`. In original coordinates the executable invariant is

```text
|z_k|<=B,       |2z_(k+1)+z_k|<=B  when J<=4;
|z_k|<=B,       |z_(k+1)|<=B       when J>=5.
```

The plus sign in the original sheared expression comes from parity.
A bound based only on `u_0`, or one omitting `z_1=2p+q+r`, would not prove
this invariant for arbitrary integral central sources.

## 5. Periodic transformed tails are constant

Because (R) is deterministic and both coordinates lie in `[-B,B]`, its
integer pairs occupy at most

```text
K=(2B+1)^2
```

states. Two pairs among indices `0..K` coincide. Uniqueness of the next
term propagates this equality, producing a periodic tail. This is a
finite pigeonhole argument on the actual recurrence, without assuming a
finite overlap graph.

It remains to classify a periodic transformed sequence. All sums below
are over one complete positive period, with cyclic indices.

### 5.1. `J>=5`: a maximum propagates backwards

Here `A+C<1`. If a periodic sequence is nonzero, choose its maximum
absolute value `H>=1`; negate the entire sequence if necessary to attain
the value `H`. Suppose an output is `H` but its preceding value is
`b<=H-1`. Its predecessor `a` satisfies `a>=-H`, so

```text
-Aa+Cb<=AH+C(H-1)
      =H-[(1-A-C)(H-1)+1-A]<H-1/2.
```

This contradicts strict nearest rounding to `H`. The preceding value
must also be `H`. Iterating backwards around the period makes the whole
period constant. This is the maximum argument already used by the
[lower-plus recurrence module](../proof/PscVerif/PscVerif/ClassAPlusConstantRecurrence.lean),
now with the coefficient condition verified in the actual upper region.

### 5.2. `J<=4`: an exact cyclic energy identity

By (6), `C>3A`. Define

```text
D_k=t_(k+1)-t_k,
S=sum D_k^2,       T=sum D_k*D_(k+1).
```

Rewrite (R) as

```text
epsilon_k=D_(k+1)-A D_k+v t_(k+1).
```

Periodicity gives the two exact identities

```text
sum t_(k+1)D_(k+1)=-S/2,
sum(D_(k+1)-D_k)^2=2S-2T>=0.
```

The first follows by summing
`2t_(k+1)(t_(k+2)-t_(k+1))
 =t_(k+2)^2-t_(k+1)^2-D_(k+1)^2`; the squared terms telescope.
The second implies `T<=S`. Therefore

```text
sum epsilon_k D_(k+1)=(1-v/2)S-A T
                    >=(1-v/2-A)S
                     =(1+C-3A)S/2>=S/2.           (8)
```

If `S>0`, at least one integer difference is nonzero. Strict rounding
and `|D|<=D^2` for integers give

```text
abs(sum epsilon_k D_(k+1))
 <=sum |epsilon_k| |D_(k+1)|
 <(sum |D_(k+1)|)/2<=S/2,
```

contradicting (8). Hence `S=0`, all differences vanish, and the periodic
sequence is constant. The argument also works on the equality face
`C=3A`; strict rounding supplies the strict contradiction.

Thus every transformed trajectory is eventually equal to an integer
`H0`. Substitution in (R) gives its exact amplitude condition

```text
|v H0|<1/2.                                        (9)
```

This is a constant-tail classification, not a zero-finiteness assertion.
Nonzero constants occur in this upper family.

## 6. Reconstruct the full cycle packet one step later

Define `W_H=yy(H,3H,-6H)`. Its physical shift is `-vH`. For `k>=1`,
equation (3) gives

```text
w_k=yy(z_k, z_k-2z_(k-1), z_(k+1)-3z_k+2z_(k-1)). (10)
```

If `t_k=H0` for all `k>=T`, then `z_k=(-1)^k H0` there. Equation (10)
therefore yields

```text
w_k=W_((-1)^k H0) for all k>=T+1.
```

The delay is required because the complete packet uses `z_(k-1)`. It
cannot be inferred from the pair `(z_k,z_(k+1))` alone at the first
constant-tail index.

A concrete control exists for every `n>=7,J=1`:

```text
w_0=yy(1,2,-5),       u_0=h-v,
z_0=1, z_1=-1,       t_0=t_1=1,
w_0 --(1,1)--> yy(-1,-3,6)=-W_1.
```

The transformed scalar sequence is constant from index zero, yet the
source is not `W_1`. The first literal step supplies the missing full
packet reconstruction. Native and independent selectors must test the
three-coordinate `W` shape, not only the first two scalar values.

In the pigeonhole proof the repeated pair begins at some `T<K`, so the
first full `W` packet is reached after at most `K` nearest steps. The zero
case `H0=0` gives full typed zero after this same delay. The executable
path stops immediately if a full integral zero occurs earlier.

## 7. Complete exits for every admissible cycle height

Let `H>=1`, `s=JH` and `vH<1/2`. Then

```text
s<(beta+1)/2<(n+7)/2<=n,       hence s<=n-1.         (11)
```

The following uses the written decrement from PR #583 at its full
parameter scope, rather than limiting it to the original eight cases.

### 7.1. Two-edge decrement when `s>=3`

```text
W_H --(0,s-2)--> xy(1-H,-3H,6H-3)
    --(s-J+4,1)--> W_(H-1).                        (12)
```

The complete incidence images are

```text
M W_H=(-H,-3H,(6-J)H),
M(1-H,-3H,6H-3)=(H-1,3H-3,(J-6)H+9-J).
```

The two pairs of original local prefixes `(top,bottom)` are

```text
((0,0,0),       (1,0,s-3)),
((1,0,s-J+3),   (1,0,0)).
```

Their differences give exactly the targets in (12). The first bottom
index satisfies `1<=s-2<=n-3`; the second top index is in `sigma(x)` and
satisfies

```text
4<=s-J+4<=n+2<=n+d.
```

Thus both intended RUN positions are literal `y` occurrences. The middle
packet has shift `3h+v(H-1)>0`, and

```text
Lx-(3h+v(H-1))=3-vH>5/2.
```

It is a strict `x/y` packet. Both endpoints are central. The resulting
height is `H-1` with the same orientation, so these two-edge pieces
compose directly.

### 7.2. `J=1`, `H=1` or `2`

```text
W_H --(0,0)--> xx(-H,-3H,5H)
    --(1,1+(n+4)H)--> yy(0,2H,-2H)
    --(1,2H+1)--> yy(0,0,0).                       (13)
```

The local prefix pairs are

```text
((0,0,0), (0,0,0)),
((1,0,0), (1,0,(n+4)H)),
((1,0,0), (1,0,2H)).
```

The full incidence images are `(-H,-3H,5H)`,
`(0,2H,-(n+6)H)` and `(0,0,-2H)`. Literal ranges follow from
`1+(n+4)H<=2n+9<=n+d` and `2H+1<=5<=n+1`.
The shifts after the source are `-H+vH`, `-2Hh`, and zero.
The first is negative and its lower `x/x` margin is
`Lx-H+vH=3-H+3h+v(H-1)>0`; the next is strict since `2Hh<=4h<1`.

### 7.3. `J=2`, `H=1`

```text
W_1 --(0,0)--> xx(-1,-3,4)
    --(0,2n+6)--> xy(0,1,-1)
    --(1,2)--> yy(0,0,0).                          (14)
```

The local prefix pairs are

```text
((0,0,0), (0,0,0)),
((0,0,0), (1,0,2n+5)),
((1,0,0), (1,0,1)).
```

The incidence images are `(-1,-3,4)`, `(-1,1,-2n-6)` and `(0,0,-1)`.
The second bottom position is a RUN in `sigma(x)` because
`2n+6<=n+d=3n+10`. Its shifts are `-2+v`, `-h`, and zero; strictness
follows from `Lx-2+v=1+3h>0` and `-1<-h<0<Lx`.

Repeated (12) reaches zero directly when `J>=3`, or one of (13)–(14)
when `J=1,2`. For negative heights, reverse both actual indices at every
edge, swap the top and bottom letters and prefixes, and negate all three
offset coordinates. This is genuine track reversal and preserves
strictness and transport. Every preterminal complete offset is nonzero.

The cycle-exit depths are

| Case | Complete depth |
| --- | ---: |
| `J>=3` | `2H` |
| `J=2` | `2H+1` |
| `J=1,H=1` | `3` |
| `J=1,H>=2` | `2H-1` |

All are at most `2H+1<=2n-1` by (11). For the eight original small cases
these give `3,3,5,7,3,5,2,2`, in their original order. Combining this with
Section 6 gives the conservative central-source length bound

```text
(2B+1)^2+2n-1, with B defined in (4).
```

The old three-RUN proposal is not silently repaired: at `JH=4` its
second bottom index is still `n+2`, the LAST `c` of `sigma(y)`. Equations
(12)–(14) are different actual occurrence paths.

## 8. Original-prefix composition and the endpoint

For each edge let `p_k,q_k` be the counted proper prefixes in the actual
current top and bottom parent words. Start with `P_0=Q_0=0` and define

```text
P_(k+1)=M P_k+p_k,
Q_(k+1)=M Q_k+q_k.                                 (15)
```

At the word level, inflate the old selected prefix and append the new
local prefix. Thus `P_k,Q_k` are Parikh vectors of actual prefixes of
the two original `k`-fold substituted source letters. Induction on the
literal transport gives the complete identity

```text
w_k=M^k w_0+Q_k-P_k                               (16)
```

at every intermediate packet. The nearest prefix and cycle suffix share
the same full typed middle packet, so their original occurrence marks
concatenate without reinitializing either accumulated prefix.

At the first integral zero, both terminal letters are `y` and

```text
M^m w_0=P_m-Q_m.
```

For the repository packet convention `delta=-w`, this reads
`M^m*(-delta)=P_m-Q_m`. No inverse-incidence integrality, projected-zero
test, quotient occurrence, or reconstructed path in a different word is
used. Explicit strictness above suffices; the generic positive-scaling
backward-interiority lemma provides an additional independent route to
strictness for any correctly typed literal path terminating at zero.

## 9. Independent executable evidence and replay

The canonical construction belongs in Mojo. The independent secondary
oracle is
[`class_a_plus_upper_recurrence_independent.py`](../oracles/python/class_a_plus_upper_recurrence_independent.py).
It imports neither PSC arithmetic nor native selector/path code. It
expands the three literal words, counts all original prefixes and Parikh
columns, and checks exact positive scaling from those counted columns.

All physical decisions use `Fraction` enclosures of the unique cubic
root. For `w=(p,q,r)`, let `a=3p+q+r`, `b=3p-q`. The exact numerator is

```text
beta(beta+1)u = a beta^2+(a+b-Jp)beta+b.
```

Its denominator is positive. Polynomial interval bounds are refined by
rational bisection until the sign is separated. The cubic bracket and
derivative bound are checked. Nonzero rational quadratics cannot vanish
at this degree-three root. An unresolved sign after the explicit 256
refinements returns `NoVerdict`. Literal allocation is capped at 50,000
occurrences, and generation at 256 path edges.

The independent oracle scans the finite integer nearest-gap range and
checks strict two-sided inequalities, rather than invoking the native
selector. It verifies the first full `W`/zero cutoff, the actual nearest
indices before that cutoff, all typed offsets and strict overlaps, and
every identity (15)–(16). Prefix coordinates are Python integers, not
machine integers. A false local prefix, omitted coordinate, illegal
position, premature reconstruction, continued first zero or incomplete
path is rejected.

The deterministic finite source set is the union of:

- `n` in `{7,8,12,31}` and `J` in `{1,2,3,4,5,n+7}`;
- all `p,q` in `{-2,-1,0,1,2}`, with the unique exactly central integer `r`;
- every admissible signed `W_H` for those members;
- the two larger coordinate pairs `(p,q)=(100,-83),(-100,83)`, again with
  their unique exactly central `r`.

Duplicate sources are removed by exact five-coordinate keys. The fresh
[independent replay summary](../evidence/class-a-plus-upper-recurrence-2026-11-15/independent-replay/summary.json)
records 818 accepted sources, 4,728 literal edges and 1,806 nearest edges.
Central `r` is chosen by an independent bounded
integer scan; `Lx<4`, `Lc<1` and the absence of physical half-ties justify
the search range and uniqueness. The calibration reaches maximum nearest
depth 62 and maximum full depth 93. The fixture
`n=31,J=1,w=(100,-83,-225)` attains both maxima, and its largest composed
prefix has 144 decimal digits. These are finite observations, not a
uniform theorem bound.

Reproduce the source-bound packet in a new output directory:

```sh
python oracles/python/class_a_plus_upper_recurrence_independent.py \
  --output-dir /tmp/psc-upper-central-independent-new
python -m pytest tests/test_class_a_plus_upper_recurrence_independent.py
```

The oracle writes an immutable copy named by its source SHA-256,
`exact-transcripts.jsonl`, a summary containing the exact declared source
set digest and all caps, and a manifest of output digests. It refuses to
overwrite a nonempty directory. Fresh retained evidence is linked from
the contribution's evidence README; no missing historical raw run is
claimed to survive from the earlier workspace outage.

The native row protocol is

```text
PLUS_UPPER_CENTRAL_PATH n J p q r central_depth depth B
  [i j top bottom x c y] repeated depth times
  P_x P_c P_y Q_x Q_c Q_y
```

Each row is physically one line. The source letters are fixed `y/y`.
The native adapter independently regenerates the complete required source
set and verifies each row against the literal replay; the six emitted
final prefix coordinates must equal the replayed values. Zero-length
paths still bind the actual member and source before acceptance.

### Formal coverage and the remaining assembly boundary

The source contracts in
[`ClassAPlusUpperRecurrence.lean`](../proof/PscVerif/PscVerif/ClassAPlusUpperRecurrence.lean)
and
[`ClassAPlusUpperCycleCompletion.lean`](../proof/PscVerif/PscVerif/ClassAPlusUpperCycleCompletion.lean)
are intentionally more specific than the complete written central-source
theorem. Their acceptance is the separate source-isolated compilation and
compiled axiom audit recorded in the evidence packet.

| Formal endpoint or bridge | What its hypotheses and conclusion cover |
| --- | --- |
| `ClassAPlusUpperRecurrence.family_coefficients` | Derives the family coefficient identities and the `J` split from explicit parameter bounds, a root in the stated chamber, and its cubic equation |
| `forward_integer_bound` | Bounds every original recurrence coordinate by the explicit reserve from both initial values; the strict recurrence is a premise |
| `eventual_constant_tail`, `eventual_alternating_tail` | Derive eventual constancy or alternation and the amplitude bound for every sequence satisfying the strict recurrence; no orbit bound or periodic-tail premise is supplied |
| `central_gap_in_run`, `run_gap_digit_step` | Bound a supplied strict nearest gap and realize it by two actual ordered RUN indices with all integral coordinates |
| `central_coordinate_recurrence`, `reconstruction_delay` | Recover the strict scalar relation from complete central coordinates, and recover the full `W` shape one step after a supplied alternating tail |
| `ClassAPlusUpperCycleCompletion.all_signed_ordered_paths` | Constructs signed complete cycle exits for every `n>=7`, `1<=J<=n+7` and `J*abs(H)<=n-1`, including zero height |
| `all_traced_strict_prefixes` | Adds both original MarkTrace witnesses, strictness under positive exact inflation data, typed terminal zero and the complete original-prefix equality |

These endpoints do not yet constitute a single Lean theorem taking an
arbitrary integral central packet directly to an original marked path
to zero. The written root-existence and degree-three no-tie argument,
construction of the infinite actual nearest trajectory, derivation of
its full reconstruction data, and concatenation with the cycle exit
must still be connected in that formal interface. Finite native replay
does not discharge those unbounded formal assembly steps. This is
separate from the next mathematical obligation of arbitrary-source
entry, which is not proved even at the written level here.

## 10. Controls, prior art and next obligation

The focused independent tests retain the one-step reconstruction control,
all three target coordinates, all six local prefix coordinates, genuine
signed-track reversal, zero-source binding, source-domain rejection,
the failed global contraction (5), operational-cap refusals and preservation
of an existing evidence archive. All 27 focused tests passed in the
[fresh validation receipt](../evidence/class-a-plus-upper-recurrence-2026-11-15/independent-validation/focused-tests.receipt.json).
The finite replay's maximum root-refinement count was 12, below the cap
of 256. Its immutable source SHA-256 is
`cc97a3f956ab3fd8d8cf22e61e090664d4a3f614112a03c6068e85adb8dc152c`,
and its transcript SHA-256 is
`125a6720fe751493bc5c02a48861d93eb5a898699cec1a156fae063a4dd13698`.
The native implementation and receipt
adapter have separate controls and acceptance records.

The recurrence belongs to the established symmetric shift radix system
methodology. The renewed gate inspected Akiyama–Scheicher's
[*Symmetric shift radix systems and finite expansions*](https://www.emis.de/ft/46698),
Huszti–Scheicher–Surer–Thuswaldner's
[*Three-dimensional symmetric shift radix systems*](https://www.dmg.tuwien.ac.at/nfn/ssrsv10.pdf),
Kirschenhofer–Petho–Surer–Thuswaldner's
[*Finite and periodic orbits of shift radix systems*](https://www.math.tugraz.at/~tichy/publications/finitev8.pdf),
and Minervino–Thuswaldner's
[*The geometry of non-unit Pisot substitutions*](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf).
The contribution here is the stated family specialization, finite
coefficient proof and authenticated occurrence bridge. General recurrence
boundedness and prefix-walk methodology are not claimed as new.

The next mathematical obligation is **arbitrary strict-source entry into
the actual central `y/y` domain**, preserving original ordered occurrences,
the full integral packet and strictness. The lower-plus entry argument
uses its own length and packing constants; it cannot be imported into
this upper chamber by renaming coefficients. The exact length boundary is
`Lx-3=((3-J)*beta+3)/(beta*(beta+1))`: `Lx<3` fails for
`J=1,2,3` and holds for `J>=4`, while `Lx<4` holds everywhere here.
This identifies a boundary for any larger-length entry argument; it does
not discharge the other interval-packing or ancestry hypotheses.
The separate `n<=6` upper
members and any seed/admissibility adapters also remain to be settled.
Only after those results and their exact scoped acceptance are assembled
can this central theorem participate in a complete upper all-source
claim. Universal BH and the broader Pisot substitution conjecture require
their additional stated dependencies.
