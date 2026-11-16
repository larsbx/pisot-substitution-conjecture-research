# Minus Class A: every strict overlap reaches coincidence for `n>=6`

Date: November 14, 2026. The starting source is draft PR #577 at
`01c4e376a652fd93e981e7b302e989c65774a0de`.

**Status: repository-proved at the stated family scope by the written
argument below; exact-head hosted acceptance and independent human review
remain pending.** The full theorem is not end-to-end Lean formalized.

**Theorem (repository-proved).** For the literal minus-Class-A substitution below, with
`k,t>=0` and `n=k+t+3>=6`, every strict integral overlap admits a finite
composable path of actual ordered child occurrences to typed coincidence,
and hence to full integral offset zero. The original proper prefix
occurrences are retained, and their depth-`m` Parikh vectors satisfy `M^m w=P-Q`.

This is an all-source theorem for the stated family and parameter domain.
It does not require that the source be cyclic, seed-reachable, or in a
supplied finite graph. It does not assert a parameter-independent or
source-independent depth bound. The six parameter pairs with `n<6` have
a separate finite S18 source scope, described below; no all-strict-source
theorem on those six parameters is inferred from their finite graphs.
Universal ternary BH, residual A1′, arbitrary infinite-tiling overlap
realization, and the all-alphabet extension remain separate statements.
Section 7 supplies the explicit adapter to the manuscript’s seed domain.

The [pre-code source and hypothesis review](bh-class-a-central-entry-stop-go-2026-11-14.md)
records the prior art, the failed stronger rank candidates and the
decision to investigate this exact mechanism. The proof has three parts:
finite actual word counts force a sufficiently central `y/y` overlap;
nearest RUN children give a bounded integer recurrence whose periodic
states are classified exactly; every nonzero periodic state has an
explicit legal exit.

## 1. Literal words, signs and exact length facts

Put

```text
K=k+1, n=k+t+3, d=k+2t+5=2n-K, A=n+d=3n-K.
sigma(x)=x y^A x, sigma(c)=c y^n x, sigma(y)=x y^(n-1) c.
```

A state is `(a,b,p,q,r)`, where `a,b` are its top and bottom tile
letters and `w=(p,q,r)` is the **bottom-minus-top** integral Parikh
offset, in coordinate order `(x,c,y)`. Its physical displacement is
`u=L_x p+L_c q+r`. The top tile is `[0,L_a]`, the bottom tile is
`[u,u+L_b]`, and strictness means that their intersection has positive
length. The incidence action and the actual child rule are

```text
M(p,q,r)=(2p+q+r, q+r, A*p+n*q+(n-1)*r),
child_w = M*w + prefix_b(j) - prefix_a(i).
```

Here `i,j` are original zero-based ordinals in the two literal images.
FIRST is `0`; RUN is `1..R_a`, with `R=(A,n,n-1)`; LAST is `R_a+1`.
RUN children are `y`, and their proper prefix is
`e_(first(a))+(i-1)e_y`. In particular, the proper prefix of a LAST
occurrence agrees with the same displayed formula, but its child letter
is the actual last letter. That distinction is kept in every exception.

The already established exact Perron facts, used in
[the signed-strip proof](class-a-x-signed-strip-2026-10-31.md), are

```text
n+2 < beta < n+3,
h=1/beta,
alpha=beta-(n+2), rho=alpha-h,
L_y=1, L_c=1+h, L_x=2+rho,
0<h<rho, rho+3h<1,
v=1-rho-3h=1-alpha-2h=K/(beta+1)>0.
```

The exact tile equation is `length(sigma(a))=beta*L_a`.
On the present domain `n>=6` these imply

```text
beta>8, 0<h<1/8, 0<alpha<1-2h,
1<L_c<2, 2<L_x<3, gamma=alpha+2h=1-v<1.
```

The symbols `v` and `gamma` in this note are scalar constants, not graph
vertices.

## 2. Every strict source has a central `y/y` descendant

Call a `y/y` overlap **central** if its displacement satisfies
`|u|<=1/2`. Since both tiles have length one, this is equivalent to
their common interval having length at least `1/2`.

### 2.1 A strict density gap on every two-level image block

For a word, its letter-`i` density here means its number of `i` letters
per unit of its **physical length**. On each one-level image, the `x`
and `c` densities are at most `1/beta`. This follows from the literal
counts and `L_x>2`, `L_c>1`: the largest of
`2/(beta L_x),1/(beta L_c),1/beta` is `1/beta`, and the same upper
bound applies to `0,1/(beta L_c),1/beta`.

The `y` density on every one-level image is at least `5/beta`.
For the three parents the numerators after factoring out `1/beta` are

```text
A/L_x=beta-2>6,
n/L_c=n/(1+h)>n-1>=5,
n-1>=5.
```

The first equality is the literal `x` tile equation
`beta L_x=A+2L_x`; the strict middle inequality uses
`(n-1)h<1`. The `x` image has the stronger `y` density
`(beta-2)/beta` and has no `c` letters.

Now decompose `sigma^2(a)` into its actual one-level image blocks.
Every `sigma(a)` contains at least one `x`. Those `sigma(x)` blocks
occupy at least the fraction

```text
(beta L_x)/(beta^2 L_a)=L_x/(beta L_a)>=1/beta
```

of the two-level image's physical length, since every `L_a<=L_x`.
Taking the length-weighted averages of the preceding bounds gives,
for **each** parent `a`, the following simultaneous density estimates:

```text
y density >= Y0 = 5/beta+(beta-7)/beta^2,
x density <= X0 = 1/beta,
c density <= C0 = 1/beta-1/beta^2.
```

Consequently they have the strict common gap

```text
eta=Y0-3X0-2C0=(beta-5)/beta^2>3/(n+3)^2>0.       (F)
```

These are finite literal-word inequalities. No asymptotic letter
frequency, Perron-vector convergence, unique ergodicity, or spectral
conclusion is required. The scalar Perron length equation and root
bounds were already stated in Section 1.

### 2.2 Counts on the actual growing overlap interval

For a fixed strict source, let `I` be the open interior of its positive
common interval and
write `ell0=|I|>0`. At depth `m`, the two words are the actual
`sigma^m(a)` and `sigma^m(b)`, with the bottom translated by
`beta^m u`; their common interval is `I_m=beta^m I`, of length
`J=beta^m ell0`.

For every `m>=2`, each word has its actual decomposition into
`sigma^2` blocks. Its intersection with `I_m` consists of full such
blocks and at most two partial boundary blocks. The longest physical
block has length `beta^2 L_x`. The greatest number of letters in a
block is

```text
B=|sigma^2(x)|=A(n+3)+4.
```

Indeed the three two-level letter-count triples are

```text
sigma^2(x): (A+4, A, A(n+1)),
sigma^2(c): (n+3, n+1, A+n^2),
sigma^2(y): (n+2, n, A+n^2-n+1).
```

The `x` block is longest: subtracting the `c` total from it gives
`(n+2)(A-n)>0`, and the `y` total is smaller than the `c` total.

Let `N_i(track,I_m)` count tile centers strictly inside the specified
open interval; touching an outer boundary is not counted.
Summing the full-block density estimates and allowing the two partial
blocks gives

```text
N_y(bottom,I_m) >= Y0*J-2*beta^2*L_x,
N_x(top,I_m)    <= X0*J+2B,
N_c(top,I_m)    <= C0*J+2B.
```

For the first inequality, full blocks cover all but at most
`2 beta^2 L_x` of the interval. Also `Y0<=1`, because it is a lower
bound on the `y` density and every tile has length at least one.
For the upper bounds, the two partial blocks each contain at most
`B` centers; full-block physical length is at most `J`. These are
bounds on the actual interval, not only on entire image words.

### 2.3 A center-count contradiction and an explicit sufficient depth

Suppose there were no central `y/y` pair among the depth-`m` actual
occurrences. Consider a bottom `y`-tile center in `I_m`. If that center
lay in any top `y` tile, the two unit-tile centers would be at distance
at most `1/2`, giving a central `y/y` pair. It must therefore lie in a
top `x` or `c` tile.

Bottom `y` centers are separated by at least one: all tile lengths are
at least one. A top `x` interval has length less than three, so it holds
at most three of these centers. A top `c` interval has length less than
two, so it holds at most two. At most two top tiles meet `I_m` while
their own centers lie outside it. Consequently the following finite
inequality holds, with a fixed boundary allowance:

```text
N_y(bottom,I_m) <= 3*N_x(top,I_m)+2*N_c(top,I_m)+6.
```

Combining this with the block bounds and (F) gives

```text
eta*J <= 2*beta^2*L_x+10B+6
         < 6(n+3)^2+10B+6.                         (N)
```

In particular define the explicit positive integer

```text
T=(n+3)^2 * [2(n+3)^2+4B+2].
```

If `J>=T`, then (F) instead gives

```text
eta*J > 6(n+3)^2+12B+6,
```

contradicting (N). Therefore **every depth `m>=2` satisfying
`beta^m ell0>=T` contains an actual central `y/y` descendant**.
Such a depth exists because `beta>1` and `ell0>0`. This sufficient
bound is deliberately conservative; it is not a shortest-depth claim.
It may depend on the source through its positive common interval.

The proof applies to every strict source, even one outside a finite seed
graph. It uses the actual two image words and their original tile
occurrences. Decode the two selected occurrences through their ancestors:
the positive final common interval is contained in every pair of ancestor
supertiles. Rescaling it backwards proves positive intersection at every
intermediate generation. Thus the found occurrence is reached by a
composable path of strict actual child occurrences, not merely by equality
of projected state labels.

## 3. A legal deterministic RUN selector on central states

Let `(y,y,p,q,r)` be central and put `S=p+q+r`. Choose the nearest integer
`e` to `beta*u`, choosing the smaller integer in a tie, and use
the actual ordinals

```text
i=1+max(e,0), j=1+max(-e,0).
```

They are both RUN. Indeed

```text
|beta*u| <= beta/2 < (n+3)/2 <= n-3/2,
```

where the last inequality is precisely `n>=6`. Every nearest integer
therefore satisfies `|e|<=n-2`, so `1<=i,j<=n-1`. The bottom-minus-top
RUN-prefix difference is `(0,0,-e)`. The child is again `y/y`, and
its physical displacement is `u'=beta*u-e`, hence `|u'|<=1/2`.
Thus this rule stays within genuine central strict overlaps indefinitely.

The complete integral update is

```text
p'=p+S, q'=S-p, r'=A*p+n*q+(n-1)*r-e.
```

This selector needs its centrality and `n>=6` hypotheses. A formally
rounded offset outside those hypotheses need not have legal RUN indices.

### 3.1 Exact recurrence and reconstruction of the full state

Set `z_0=p` and `z_1=p+S` at the initial central state. If a current
adjacent pair is `a=z_j,b=z_(j+1)`, the next central child has the form

```text
(y,y, b, b-2a, c-3b+2a),
u_child = c+alpha*b-2h*a,
```

where `c=z_(j+2)` is the integer selected by the preceding
nearest-child rule. Equivalently,

```text
c = nearest_integer(2h*a-alpha*b), with the larger integer in a tie,
|c-(2h*a-alpha*b)|<=1/2.                         (R)
```

For completeness, `q'=p'-2p=b-2a` follows from the displayed full
incidence update, and writing the child's sum as `c-b` yields its
third coordinate. Substitution of the exact tile lengths then gives
the physical formula for `u_child`. The original rounding and this
recurrence therefore select the same integer: subtracting a rounded
quantity from an integer reverses the tie direction. Both conventions
are deterministic and commute with integral translation. The arguments
below use only the displayed error bound, including its endpoints.

After the first selected step, the adjacent integer pair determines the
entire typed integral child through this formula. Eventual periodicity
of the pair consequently implies eventual periodicity of the actual
overlap states; this is not a projection-only inference.

### 3.2 Boundedness and eventual periodicity

For `H=max(|a|,|b|)`, equation (R) gives

```text
|c| <= (2h+alpha)*H+1/2 = (1-v)*H+1/2.
```

One explicit integer choice is

```text
B=max(|z_0|,|z_1|,n+2).
```

It is at least `1/(2v)`, because
`1/(2v)=(beta+1)/(2K)<(n+4)/2<=n+2`. Whenever `|a|,|b|<=B`,
the same inequality gives `|c|<=B`. The deterministic recurrence
therefore takes values in at most `N=(2B+1)^2` integer pairs and is
eventually periodic. Among its first `N+1` pairs there is a repetition;
within at most `N+1` selected occurrence edges the full state is on a
periodic orbit. This proves boundedness; it does not by itself prove a
zero hit, since nonzero cycles really occur.

### 3.3 Half-unit endpoints and the Lean instantiation boundary

The written selector above permits the closed interval `|u|<=1/2`.
The audited recurrence in
[`ClassACentralRecurrence.lean`](../proof/PscVerif/PscVerif/ClassACentralRecurrence.lean)
uses the strict error `<1/2`. Actual integral sources never lie on the
half-unit boundary, and their nearest-integer step has no tie. Here is
the precise arithmetic reason.

The characteristic polynomial, in the present parameterization, is

```text
chi(X)=X^3-(n+2)X^2-(n-K+1)X+2.
```

It is irreducible over `Q`: a rational root of this monic cubic would
be one of `1,-1,2,-2`, whereas

```text
chi(1)=K-2n,       chi(-1)=-K,
chi(2)=2K-6n,     chi(-2)=-2n-2K-12.
```

All four are negative because `1<=K<=n-2`. Thus `beta` has degree
three over `Q`, so it cannot satisfy a nonzero rational polynomial of
degree at most two. The exact normalized lengths also give

```text
L_x=beta-n-1/beta, L_c=1+1/beta,
beta*u = p*beta^2+(q+r-n*p)*beta+(q-p).            (H)
```

If `beta*u=j+1/2` for an integer `j`, multiplying (H) by two and
moving the right side to the left produces a polynomial vanishing at
`beta`, of degree at most two, with odd constant coefficient
`2(q-p)-2j-1`. It is nonzero, a contradiction. Therefore the exact
nearest-integer choice has no half-integer tie.

If instead `u=1/2` or `u=-1/2`, multiplying that equality by
`2 beta` and using (H) produces such a polynomial with odd coefficient
of `beta`, namely `2(q+r-n*p)-1` or `2(q+r-n*p)+1`. Again it cannot
vanish. Hence every actual integral central state satisfies `|u|<1/2`.
Its child has integral coordinates, so its centered physical displacement,
which is the recurrence error in Section 3.1, also has absolute value
strictly less than `1/2`. In particular the actual cycle amplitudes
satisfy `vH<1/2`, strengthening the weak inequality sufficient for the
written proof.

These deductions justify the **mathematical** specialization of the
strict audited recurrence to this family. They are not themselves a
completed Lean specialization: the current module takes its real
parameter inequalities and strict nearest recurrence as hypotheses.
Its literal RUN-digit and coordinate endpoints do not formalize the
family's cubic irreducibility, the Perron-root estimates, or the finite
block-count entrance proof. The native gap `e` is subtracted from the
last coordinate, whereas the audited literal RUN theorem names the
added gap `g`; their instantiation is `g=-e`. The full family theorem
therefore remains a written proof with the separately stated Lean
subtheorems and exact executable receipts.

## 4. The only nonzero periodic states are alternating states

Consider a periodic integer sequence satisfying (R). A nonzero periodic
sequence must take both signs. For example, if all entries were
nonnegative and a positive maximum `A_+` occurred, then
`A_+<=2h*A_++1/2`; this is impossible because `1-2h>3/4` and
`A_+>=1`. The nonpositive case is the same argument with signs negated.

For a nonzero periodic sequence, now write its positive maximum as
`A_+>=1` and its negative minimum as `-A_-`, where `A_->=1`. At a
positive maximum and a negative minimum, respectively, (R) gives

```text
(1-2h)*A_+ - alpha*A_- <= 1/2,
(1-2h)*A_- - alpha*A_+ <= 1/2.
```

If `A_+>=A_-+1`, the first left-hand side is

```text
v*A_-+(1-2h)*(A_+-A_-) >= 1-2h > 1/2,
```

a contradiction. The second inequality excludes `A_->=A_++1`.
Hence the extrema are `A_+=A_-=H>=1`, and they satisfy

```text
v*H <= 1/2.                                         (C)
```

Every occurrence of an output `H` has preceding entry `-H`.
To see this, first suppose `alpha>=1/2`. If the preceding entry `b`
were at least `-H+1`, its unrounded value would satisfy

```text
2h*a-alpha*b <= (2h+alpha)*H-alpha
                 = H-v*H-alpha < H-1/2,
```

which cannot round to `H`. If `alpha<1/2`, then `h<1/8` gives
`v=1-alpha-2h>1/4`. Condition (C) forces `H=1`. A preceding entry
`b>=0` would give unrounded value at most `2h<1/4`, again too small
to round to one. In both cases the preceding entry is `-H`.
Sign reversal proves that every `-H` is preceded by `H`.

Starting from a maximum and following the periodic sequence backwards
now exhausts the cycle, so it is exactly alternating `H,-H,H,-H,...`.
The full-state reconstruction identifies its two states as

```text
W_H=(y,y,H,3H,-6H), R(W_H)=(y,y,-H,-3H,6H),
shift(W_H)=-v*H.
```

The zero periodic sequence gives the full zero-offset state. There are
no other periodic possibilities. Notice that (C) supplies the exact
guard

```text
KH <= (beta+1)/2 < (n+4)/2 <= n-1,
```

so, by integrality, `KH<=n-2` on the entire `n>=6` domain.

## 5. Actual exits from every nonzero alternating cycle

It remains to leave the selected nearest-integer cycle using other
actual children. Reversal here swaps the two tracks, negates every
offset coordinate and swaps each original ordinal pair. It preserves
strictness and actual occurrence validity.

### 5.1 The general case `KH>=4`

For `W_H` satisfying (C), use the following two literal edges:

```text
W_H --(1,KH)--> (y,y,-H,-3H,6H-1)
    --(0,n+3-KH)--> (x,y,H,3H-1,3-6H)=R(Q_H).
```

The first pair is RUN/RUN, since `4<=KH<=n-2`. The second top
ordinal is FIRST, and its bottom ordinal lies in `[5,n-1]`, hence
is RUN. The image calculations are

```text
M(H,3H,-6H)=(-H,-3H,(6-K)H),
M(-H,-3H,6H-1)=(H-1,3H-1,(K-6)H-n+1).
```

The indicated prefix differences give exactly the displayed targets.
The intermediate physical shift is `vH-1`, strictly between `-1`
and zero, so it is a strict `y/y` overlap.

The [existing guarded positive unit-strip theorem](class-a-x-transfer-plane-2026-10-31.md)
gives `Q_H=(y,x,-H,1-3H,6H-3)` a genuine coincidence suffix of
`2H+1` edges whenever `H>=1` and `KH<=n+3`. Our stronger bound
`KH<=n-2` supplies that premise. Apply true reversal to this suffix.
The full path from `W_H` has at most `2H+3` edges and reaches full
integral zero. The actual FIRST/RUN/LAST conventions of that earlier
theorem remain in force.

### 5.2 The five small positive factorizations `KH<=3`

There are exactly five pairs `(K,H)` to consider. The following paths
work for every `n>=6` in the relevant parameter domain. Non-LAST
positive ordinals in these displays are RUN.

For `K=1`, `H=1` or `H=2`, with `A=3n-1`:

```text
yy(H,3H,-6H)
 --(0,0)------------> xx(-H,-3H,5H)
 --(1,1+(n+2)H)----> yy(0,2H,-2H)
 --(2H+1,1)--------> yy(0,0,0).
```

The second incidence image is `(0,2H,-(n+4)H)` and the RUN
prefix difference is `(0,0,(n+2)H)`. For `H=1`, the moving
ordinal is `n+3`, with upper slack `2n-4`; for `H=2` it is
`2n+5`, with slack `n-6`. Equality at `n=6,H=2` is the final
RUN `A`, not LAST. The final ordinal `2H+1<=5<=n-1` is legal.

For `K=2`, `H=1`, with `A=3n-2`:

```text
yy(1,3,-6) --(0,0)--> xx(-1,-3,4)
 --(0,2n+2)--> xy(0,1,-1) --(2,1)--> yy(0,0,0).
```

The second incidence image is `(-1,1,-2n-2)`; its bottom RUN
prefix is `(1,0,2n+1)`. The moving ordinal has upper slack
`n-4>=2`. Both final ordinals are RUN.

For `K=3`, `H=1`, with `A=3n-3`:

```text
yy(1,3,-6) --(0,1)--> xy(0,-3,3)
 --(1,4)--> yy(0,0,0).
```

The two image vectors are `(-1,-3,3)` and `(0,0,-3)`.
The first prefix difference adds `(1,0,0)` and the second adds
`(0,0,3)`. The bottom ordinal `4<=n-1` is RUN.

For `K=1`, `H=3`, with `A=3n-1`, use the five-edge path:

```text
yy(3,9,-18)
 --(0,1)-----> xy(-2,-9,15)
 --(0,1)-----> xy(3,6,-13)
 --(2n,0)----> yx(-2,-7,11)
 --(1,2n+6)-> yb(0,4,-4)
 --(5,1)-----> yy(0,0,0).
```

At `n=6`, the fourth bottom ordinal is `2n+6=A+1=18`, the
actual LAST `x`; hence `b=x`. At `n>=7`, its upper RUN slack is
`A-(2n+6)=n-7>=0`, and `b=y`. In either case its proper prefix
is `(1,0,2n+5)`. The third top ordinal `2n` has RUN upper slack
`n-1`, and the final top ordinal `5<=n-1` is RUN. Bottom ordinal
one is RUN for either possible letter `b`.

The full vector checks, including this LAST exception, are

```text
M(3,9,-18)=(-3,-9,15),       add (1,0,0);
M(-2,-9,15)=(2,6,-13),      add (1,0,0);
M(3,6,-13)=(-1,-7,2n+10),   subtract (1,0,2n-1);
M(-2,-7,11)=(0,4,-2n-9),    add (0,0,2n+5);
M(0,4,-4)=(0,0,4),         add (0,0,-4).
```

Every displayed path ends at positive full-overlap zero. Its genuine
occurrences contain a common final interval, so pulling that interval
back proves strictness at every predecessor as well. This is also a
direct way to verify all intermediate strictness claims in the five
small cases. Their maximum length is five. Apply genuine reversal
for the negative cycle state.

## 6. Completion with original prefixes and terminalization

Start with any strict source on the `n>=6` domain. Section 2 gives a
finite actual path to a central `y/y` state. Follow the legal nearest
RUN selector. It either hits integral zero along the way or eventually
enters a classified periodic state. The zero periodic state is already
the target; every nonzero periodic state has one of the explicit exits
in Section 5. Concatenating these actual paths proves the theorem.
The previous bounds also give a conservative central-source bound:
`KH<=n-2` implies `H<=n-2`, so the longest needed cycle suffix is
at most `2n-1` edges (and every small exceptional suffix is at most five).
Together with Section 3.2, integral zero is reached within
`(2B+1)^2+2n` edges from the central source. This bound retains the
source-dependent integer `B`; it is not a bound on all strict sources
at once.

For every edge retain the original proper prefixes `P_j,Q_j`, from the
top and bottom source images respectively. The offset recurrence is

```text
w_(j+1)=M*w_j+Q_j-P_j.
```

The chosen occurrences are composable, so their actual depth-`m`
prefix Parikh vectors are

```text
P=sum_(j=0)^(m-1) M^(m-1-j)*P_j,
Q=sum_(j=0)^(m-1) M^(m-1-j)*Q_j.
```

This is the literal prefix-of-a-nested-image recurrence, not an
independent choice of vectors with the same projection. Telescoping
the child equations gives `w_m=M^m w+Q-P`. Since `w_m=0`, it follows
that `M^m w=P-Q` for the retained original occurrences. Their common
positive interval supplies strictness of their decoded ancestors.

The terminal letters at an integral-zero hit need not be equal.
For a production graph that terminalizes zero or typed coincidence,
stop at its first applicable zero hit. A longer nonterminalized literal
transcript is not asserted to refine a terminalized production graph.
This stopping only shortens the successful path and preserves its
original-prefix identity at the chosen stopping depth.

### 6.1 Stronger written conclusion: typed coincidence

The same argument proves a stronger existence statement on `n>=6`:
**every strict integral source has an actual typed-coincidence descendant**.
For this statement retain the density argument's literal transcript to its
central `y/y` target even if an earlier mixed-letter integral-zero state
occurs. Such a state is not terminal under the manuscript's typed-coincidence
policy. If an earlier typed coincidence occurs, it already proves the
statement and the transcript can stop there.

From the central target onwards, the nearest RUN trajectory stays `y/y`.
Its zero periodic state is therefore typed coincidence. Every nonzero cycle
exit in Section 5 ends at `(y,y,0,0,0)`, including the existing reversed
`Q_H` suffix. Thus either branch of the actual construction ends at typed
coincidence. This conclusion also applies when the original source itself
has zero integral offset and unequal tile letters; the density argument
has no nonzero-source hypothesis.

This is a written existence corollary. A BH implementation that stops at
the first integral-zero state certifies the weaker stopping contract;
its emitted mixed-letter-zero endpoint is not evidence that the stronger
continuation was executed. The two receipt scopes must be reported
separately. The stronger argument uses the same original-address and
strict-ancestor construction, and stops only at the first typed hit when
compared with the manuscript's terminalized graph.

## 7. The six small parameter pairs have a different source scope

The parameters excluded by `n>=6` are precisely

```text
(k,t)=(0,0),(0,1),(1,0),(0,2),(1,1),(2,0).
```

All six occur in the pre-existing complete 22-member S18 graph archive.
An exact replay of those six graphs can provide coverage and hits for
their stated actual 18 swap-seed sources, after checking every original
edge, root, discovery and complete-child-closure obligation. Such a
certificate is a finite theorem at that source scope. It cannot establish
productivity of every formal strict integral source at those parameters.

### 7.1 Why the eighteen roots cover the manuscript's seed-patch graph

The manuscript defines `O_sigma` in
[the geometric reformulation](../manuscripts/PSC_balanced_pair_state_2026-09-13.tex)
(`sec:overlap`) as the closure of the level-zero contacts of the aligned
patches `ab/ba`, with typed coincidences terminal. Its headline BH lemma B
(`sec:headline-status`) quantifies over cyclic vertices of that graph.
It does not define this source domain as every overlap of two arbitrary
infinite tilings in a fibre.

Here `L_x>L_c>L_y`. For each ordered-by-length pair `(a,b)` with
`L_a>L_b`, the four contacts of aligned top `ab` and bottom `ba` are

| Top/bottom tiles | Integral bottom-minus-top offset | Strict? |
| --- | --- | --- |
| `a,b` | `0` | yes |
| `a,a` | `e_b` | yes, since `L_b<L_a` |
| `b,b` | `-e_a` | no, since `L_a>L_b` |
| `b,a` | `e_b-e_a` | yes |

Thus the three unordered letter pairs give exactly the nine roots
listed in [the original seed derivation](class-a-nine-swap-to-x-2026-10-31.md#correct-object-and-substitution-parameters).
Reversing the two patches swaps the tile types and negates the full
offset, giving the other nine distinct roots. These are exactly the
`nine_sources()` and reversed sources of
`kernel/psc/class_a_x_productivity.mojo`, and the full `S18` used by the
six certificates. If the manuscript graph chooses only one orientation
of each unordered seed, it is a subgraph of this orientation-complete
source domain; the additional orientations do not omit any source.

The literal child relation is the same on both sides: inflate the two
source tiles, enumerate all ordered original child occurrences, and
retain precisely positive-interior intersections. The full Parikh
recurrence in Section 1 intertwines with the manuscript's physical
`beta*u+bottomPrefix-topPrefix` rule. The
[Class-A integer/cubic bridge](class-a-parikh-cubic-bridge-2026-10-31.md#the-integer-linear-bridge-proved-by-coefficients)
proves injectivity of the full integral offset encoding, so physical
interning identifies no distinct integral states in this chamber.

A typed coincidence has only typed-coincidence children: its two
inflated words agree at the same positions, and different tile interiors
of that common word are disjoint. Therefore terminalizing it loses no
noncoincidence source. Conversely, every noncoincidence contact in an
iterated swap patch has the unique pair of ancestor tiles at the
previous level, whose common positive child interval proves that the
parent contact is strict. Induction supplies exactly the seed-reachable
noncoincidence graph under the same terminal convention. This is also
the explicit ancestry argument in the manuscript's `sec:overlap`.

Consequently, checking all eighteen roots and every literal strict
nonterminal child in each small certificate supplies the coverage
required by the manuscript's seed-patch BH statement. No unproved
identity `Reach(S18)=Reach(X) union {E,R(E)}` is used, and no transfer
from the larger class of literature-realized fibre overlaps is needed
for this particular source domain.

### 7.2 Combined seed-domain statement and the affine target

Combining the all-strict-source theorem for `n>=6` with the completed
six small S18 certificates yields the following exact family conclusion,
subject to the recorded certificate replay:

> For every `k,t>=0` in the displayed literal minus-Class-A chamber,
> every vertex of the orientation-complete swap-seed graph has an actual
> composable ordered-occurrence path to full integral zero.

This covers transient vertices as well as cyclic ones. For a nonzero
source, stop the path at its first zero hit. Its predecessor is nonzero,
and the existing complete
[one-step zero-return classification](class-a-uniform-zero-return-2026-11-02.md)
places that predecessor in one of the nine legal affine segments.
The graph's complete nonterminal child closure keeps the chosen path
inside the same graph until that hit. Zero-offset sources already meet
BH at depth zero. This gives the mathematical entry conclusion requested
by [issue #452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452)
at its stated seed-patch source scope, once its exact-source acceptance
requirements are met.

The two parameter domains have different proof scopes: `n>=6` includes
every formal strict integral source; `n<6` includes exactly the certified
swap-seed descendants. The nonunit case has not been replaced by a
unimodular argument: every path proves a full identity in `Z^3` using
forward multiplication by `M`, with no inverse-integrality assumption.
It can therefore be read in every representation of that integer module.
An independent dictionary for arbitrary overlaps of infinite tilings,
a complete arbitrary-ternary BH theorem, residual aligned A1′, and a
spectral conclusion require their own stated arguments. They are not
additional premises of the literal seed-domain corollary just proved.

### 7.3 Family aligned coincidence follows from the stronger construction

The six small complete certificates end at typed full-zero coincidences.
Combining them with Section 6.1 therefore proves typed productivity of
every vertex of the S18 seed-patch graph throughout the displayed chamber,
subject to the same exact certificate acceptance. In particular the
six left-aligned states `(a,b,0)`, `a!=b`, are among the eighteen roots.
Their typed hits give actual common letters preceded by equal full
Parikh prefixes. Hence ordinary eventual coincidence of all letter pairs
also follows at this **family** scope; it does not require an additional
A1′ premise for this family.

This is not a uniform A1′ theorem for arbitrary ternary PIP substitutions.
Any use of the manuscript's further finite-BPA or published spectral
consumer must identify its hypotheses and proof scope separately. No new
end-to-end Lean spectral theorem is asserted here. The canonical BH
receipts that stop at integral zero remain credited only at that weaker
executed contract unless the stronger continuation is separately replayed.

## 8. Evidence and scope of formalization

The written proof above separates the following mathematical obligations:

- actual finite-count forcing on growing literal image intervals;
- legal central RUN indices and the full integral recurrence;
- boundedness, exact periodic classification and explicit cycle exits;
- occurrence ancestry, prefix telescoping and stopping at the first hit;
- complete finite source coverage for the six small parameter pairs.

Native replay, an independent literal-word oracle, symbolic identities,
finite exceptional graphs and Lean endpoints must be reported at their
own exact scopes. A tested bounded search is not the all-source finite-count
argument; a finite sample of recurrences is not their periodic
classification; and a Lean theorem with supplied coverage or hitting
premises does not discharge those premises. Acceptance receipts are
recorded separately with the implementation. No governed claim status
is changed by this note alone.
