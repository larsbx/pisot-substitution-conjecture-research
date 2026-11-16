# Plus Class A: deferred upper-entry target

Date: November 14, 2026 (America/New_York). Starting source: draft PR #579
at `110e7e9ef8243bc24adf80d6e8a375add586d850`.

**Status: proposed next target, recorded from hand derivations only.** The
upper-region mechanism in this note has not been executed, independently
replayed, or formalized. It is not promoted to a repository theorem or an
accepted dependency. In particular this note does not broaden the current
[lower/middle plus-Class-A theorem](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/research/bh-class-a-minus-constant-entry/docs/class-a-plus-constant-entry-2026-11-14.md) (on the unmerged #577 stack),
whose all-source domain is `n>=6,5<=d<=n+4`.

The closest existing [source and hypothesis gate](bh-class-a-plus-constant-stop-go-2026-11-14.md)
reviewed symmetric shift radix systems, nonunit prefix automata, and actual
overlap reachability, but explicitly narrowed implementation to the
lower/middle chamber. A future upper implementation, universal diagnostic
or formal promotion requires its own recorded stop/go decision. The point
of this memo is to retain the proposed formulas and the remaining literal
occurrence obligations so that they do not have to be rediscovered.

## 1. Proposed parameter scope and exact coordinates

Retain the literal ordered plus words

```text
sigma(x)=x y^(n+d) x,
sigma(c)=c y^n x,
sigma(y)=x y^(n+1) c.
```

The first uniform upper target should be

```text
n>=7, n+5<=d<=2n+11.
```

The smaller upper members `0<=n<=6` are a separate finite obligation;
neither the current lower theorem nor this memo disposes of them. All
offsets below use `(x,c,y)` coordinates and the bottom-minus-top convention.
Write `yy(p,q,r)` for the full typed state `(y,y,p,q,r)`. The incidence action
is still

```text
M(p,q,r)=(2p+q+r, q+r, (n+d)*p+n*q+(n+1)*r).
```

For this upper domain, put

```text
J=2n+12-d,                    1<=J<=n+7,
chi(X)=X^3-(n+4)X^2+(n-d+5)X-2,
h=1/beta,                    n+4<beta<n+6,
delta=d/(beta-1),
Ly=1, Lc=1-h, Lx=1-h+delta,
A=2h, C=beta-(n+4), v=1+A-C.
```

The proposed root bracket follows from the exact signs

```text
chi(n+4)=(n+5-d)(n+4)-2<0,
chi(n+6)=(n+6)(3n+17-d)-2>0.
```

The same four rational-root evaluations as in the lower note are nonzero:
`chi(1)=-d`, `chi(-1)=d-2n-12`, `chi(2)=-2(n+d)` and
`chi(-2)=2d-6n-36`. Thus the selected root has degree three. The eigenlength
identity gives

```text
beta=n+3-2h+delta,
v=2+4h-delta=J/(beta+1)>0,
0<A<2/11<1/4,               0<C<1+A.
```

Here `C>0` is the change of sign from the lower chamber. Factoring the
cubic gives `chi(X)=(X-beta)(X^2+C X+A)`. Equivalently, the roots of
`X^2-C X+A` are the negatives of the two other conjugates of `beta`.
If real, those two transformed roots are positive, have product `A<1`
and sum `C<1+A<2`, and satisfy `(1-lambda1)(1-lambda2)=v>0`; both are
therefore less than one. If nonreal, their common modulus is `sqrt(A)<1/2`.
These elementary observations also supply the stability hypotheses used
in Section 3. They must be bound to the actual plus field in any executable
or formal specialization.

## 2. Candidate central recurrence and periodic classification

For a central actual `y/y` state with `|u|<=1/2`, the nearest gap `e` to
`beta*u` can be represented by original RUN indices

```text
i=1+max(e,0), j=1+max(-e,0).
```

Since `beta/2<(n+6)/2<=n` for `n>=7`, one has `|e|<=n`, so both
indices lie in the actual RUN `1..n+1`. The child remains central.
The degree-three identity

```text
beta*u=p*beta^2+(q+r-(n+2)*p)*beta+(p-q)
```

excludes half-integer gap ties and physical half-unit boundaries by the
same odd-coefficient argument as in the lower note. Consequently nearest
rounding is unique and commutes with negation on these actual inputs.

Let `z_j` be the successive first integral coordinates. For
`a=z_j,b=z_(j+1),c=z_(j+2)`, the complete next state is

```text
yy(b,b-2a,c-3b+2a),
u_child=c+C*b+A*a.
```

Thus the upper scalar rule is `c=nearest(-A*a-C*b)`. The parity change
`t_j=(-1)^j*z_j` makes this an autonomous rule

```text
t_(j+2)=nearest(-A*t_j+C*t_(j+1)),
epsilon_j=t_(j+2)-C*t_(j+1)+A*t_j,
|epsilon_j|<1/2.                                      (R)
```

The following hand argument proposes a constant-period classification for
(R) under `0<A<1/4`, `C>0` and `v=1+A-C>0`.

If `C<3A`, then `A+C<1`. In a nonzero periodic orbit choose a positive
maximum absolute value `H` by negating the whole orbit if necessary. An
output `H` cannot have preceding entry `b<=H-1`, because `a>=-H` gives

```text
-A*a+C*b <= A*H+C*(H-1)
          = H-[(1-A-C)*(H-1)+1-A]
          < H-1/2.
```

Hence each occurrence of `H` is preceded by `H`; going backwards around
the period makes the orbit constant.

For `C>=3A`, take all sums over one cyclic period and define

```text
D_j=t_(j+1)-t_j,
S=sum D_j^2,
T=sum D_j*D_(j+1).
```

Rewriting (R) as
`epsilon_j=D_(j+1)-A*D_j+v*t_(j+1)` and using periodicity gives the
exact energy identity

```text
sum epsilon_j*D_(j+1)=(1-v/2)*S-A*T.                  (E)
```

Indeed `sum t_(j+1)*D_(j+1)=-S/2`. Also
`T<=S`, since `sum(D_(j+1)-D_j)^2=2S-2T>=0`. Therefore

```text
sum epsilon_j*D_(j+1)
 >= (1-v/2-A)*S
 = (1+C-3A)*S/2
 >= S/2.
```

If `S>0`, strict rounding and integrality instead imply

```text
abs(sum epsilon_j*D_(j+1))
 < (sum abs(D_(j+1)))/2
 <= S/2,
```

a contradiction. Thus `S=0`, again giving a constant orbit. The strict
rounding error is essential at the equality face `C=3A`.

Translating back would classify nonzero periodic original states as the
alternating pair

```text
W_H=yy(H,3H,-6H), -W_H=yy(-H,-3H,6H), H>=1.
```

Their physical shifts are `-vH` and `vH`. The exact amplitude condition is

```text
vH<1/2, equivalently 2JH<beta+1.                     (C)
```

These are nonzero nearest-selector cycles. A periodic classification
alone still supplies no offset-zero hit.

## 3. Candidate boundedness argument with explicit initial terms

The lower proof's absolute coefficient bound cannot simply be reused:
`A+C=delta-1` can exceed one near `J=1,2,3,4`. Instead, let

```text
U_(-1)=0, U_0=1,
U_(k+1)=C*U_k-A*U_(k-1), k>=0.
```

For the transformed recurrence and each `k>=1`, the complete variation
of constants formula is

```text
t_k=U_(k-1)*t_1-A*U_(k-2)*t_0
    +sum_(j=0)^(k-2) U_(k-2-j)*epsilon_j.            (V)
```

The sum is empty at `k=1`; the `U_(-1)=0` convention handles the other
initial term correctly. An executable bound must retain both `t_0` and
`t_1`; it cannot bound the orbit using only the initial physical shift.

If the two roots `lambda1,lambda2` of `X^2-C X+A` are real, Section 1
puts both in `(0,1)`. The formula

```text
U_k=sum_(r=0)^k lambda1^(k-r)*lambda2^r
```

is nonnegative, includes the repeated-root case, and gives

```text
sum_(k>=0) abs(U_k)=1/[(1-lambda1)(1-lambda2)]=1/v.
```

For a nonreal conjugate pair, both roots have modulus
`rho=sqrt(A)<1/2`; the same finite sum gives
`abs(U_k)<=(k+1)*rho^k`, whence

```text
sum_(k>=0) abs(U_k)<=1/(1-rho)^2<4.
```

Putting `L=max(1/v,4)`, equation (V) yields

```text
abs(t_k)<=L*(abs(t_1)+A*abs(t_0)+1/2), k>=1.
```

Since `1/v=(beta+1)/J<n+7` and `4<n+7`, the following integral reserve
would suffice for all indices, including zero:

```text
C0=(n+7)*(abs(t_0)+abs(t_1)+1).
```

The deterministic integer pairs then occupy at most `(2C0+1)^2` states,
giving an eventual periodic tail. Section 2 would make the transformed
tail constant and the original tail alternating. These analytic and
finite-pair steps have not yet been implemented or Lean-specialized here.
Checked-arithmetic overflow or a smaller executable cap must remain a
refusal, never a substitute for this proposed unbounded argument.

## 4. Proposed three-RUN decrement when `JH>=5`

For `n>=7`, `H>=1`, condition (C), and `JH>=5`, the proposed path is

```text
W_H
 --(1,JH)------------> yy(-H,-3H,6H-1)
 --(1,n+6-JH)--------> yy(H-1,3H-1,4-6H)
 --(1,J(H-1)+3)------> -W_(H-1).
```

All indices are original zero-based positions; positive positions in this
display are intended to be actual RUN occurrences of `sigma(y)`. The
full incidence calculations are

```text
M(H,3H,-6H)=(-H,-3H,(6-J)H),
M(-H,-3H,6H-1)=(H-1,3H-1,(J-6)H-n-1),
M(H-1,3H-1,4-6H)=(1-H,3-3H,(6-J)H+J-8).
```

The three RUN prefix differences add `JH-1`, `n+5-JH`, and
`J(H-1)+2` to the last coordinate, giving the stated full targets.

Condition (C) and `beta<n+6` imply
`JH<(n+7)/2<=n`, hence the integral bound `JH<=n-1`. It gives

```text
1<=JH<=n-1,
7<=n+6-JH<=n+1,
3<=J(H-1)+3<=JH+2<=n+1.
```

Thus each proposed position lies in the literal RUN `1..n+1`.
The four physical shifts are

```text
-vH,
vH-1,
-v(H-1)-2h,
v(H-1).
```

The first and last are central; the second lies in `(-1,-1/2)`. For the
third, `v(H-1)<1/2` and `2h=A<1/4`, so it lies in `(-3/4,0)`.
Centrality of this intermediate is unnecessary; strict `y/y` overlap is
enough. The target is the reversed lower-height cycle state, so repeated
decrement must reverse the two original indices on alternating segments,
not merely negate coordinate labels without changing occurrences.

This is an unexecuted address proposal with a hand-checked algebraic and
range derivation. A future implementation must replay its actual words,
strict edges and complete composed prefixes independently.

## 5. Exact remaining occurrence obligations

The positive cases with `JH<=4` are exactly

| `J` | Remaining heights `H` |
| --- | --- |
| `1` | `1,2,3,4` |
| `2` | `1,2` |
| `3` | `1` |
| `4` | `1` |

Every row also needs genuine track reversal. There is no accepted or
executed uniform actual-occurrence exit table for these eight cases in
this memo. Hand candidates for some rows do not cover the whole table.

The failed extension of the three-RUN formula is concrete. At `JH=4`,
its second bottom index becomes `n+2`, the actual LAST `c` of `sigma(y)`,
not a RUN `y`. The expected second `y/y` packet therefore has the wrong
type. At `JH<=3`, that index is even beyond LAST. These cases require
new literal paths; changing the label while keeping the old indices is
not a valid completion.

An upper all-source conclusion also still requires a separately justified
entry argument and its exact implementation. The lower proof used
`Lx<3`, a packing factor at most three, and its own boundary constants;
the upper chamber needs its own packing bounds. The finite `n<=6` upper
members, any source/seed adapters, all original-prefix composition,
symbolic parameter verification, independent native replay and precise
formal scope must then be assembled explicitly.

The present contribution's mathematical conclusion remains the
lower/middle plus theorem. No complete upper-Class-A theorem, universal
BH, arbitrary-ternary A1-prime, C4, spectral conclusion or all-alphabet
extension is asserted by this deferred record.
