# Minus Class A: constant-cycle entry for `d>=5, n>=d+1`

Date: November 14, 2026. Starting source: draft PR #578 at
`34ff471c24960729527ae5f090e96c7c16ae4584`.

**Status: a complete written proof at the stated family scope; exact-source
executable and formal acceptance are recorded separately, and independent
human review remains pending.** The full theorem is not end-to-end Lean
formalized. This note does not change a governed claim status by itself.

**Formal follow-on:** [literal Lean specialization](class-a-minus-literal-lean-2026-11-14.md)
now connects the actual incidence cubic, its dominant root, positive length
scaling, half-unit exclusion, actual central RUN recurrence, constant-height
descent and complete nested original-prefix assembly. The remaining
all-strict-source entry interface is the actual common-interval block
decomposition and center assignment. Its acceptance is recorded separately
from the historical #579 receipts below.

**Theorem (repository-proved).** Let `d,n` be integers with `d>=5` and `n>=d+1`, and use the
literal substitution

```text
sigma(x)=x y^(n+d) x,
sigma(c)=c y^n x,
sigma(y)=x y^(n-1) c.
```

Every strict integral overlap has a finite composable path of actual
ordered child occurrences to typed coincidence. If its full integral
offset is `w`, the retained original depth-`m` proper prefix occurrences
have Parikh vectors `P,Q` satisfying `M^m w=P-Q`.

The quantifier includes every formal strict integral source for this
literal family. Cyclicity, seed reachability, and membership in a supplied
finite carrier are not hypotheses. The depth can depend on the source and
on the parameters. The theorem includes the initially targeted residual
strip `d+1<=n<5d`, but its proof needs no upper bound on `n`.

The [pre-code source and hypothesis gate](bh-class-a-minus-constant-stop-go-2026-11-14.md)
records the four-source review and the decision to investigate this exact
mechanism. Here one-level literal word counts force entry into a central
`y/y` overlap. A legal nearest RUN rule gives a bounded integer recurrence
whose periodic tails are constant. Three actual RUN edges reduce every
nonzero constant height. The argument retains the full offset and every
original occurrence throughout.

## 1. Literal coordinates, roots and tile lengths

Use letters `(x,c,y)=(0,1,2)`. A state is `(a,b,p,q,r)`, with top and
bottom tile letters `a,b` and **bottom-minus-top** integral offset
`w=(p,q,r)` in coordinate order `(x,c,y)`. Write

```text
u=L_x*p+L_c*q+r.
```

The top tile is `[0,L_a]` and the bottom tile is `[u,u+L_b]`.
Strictness means that their common interval has positive length. Set
`R_x=n+d`, `R_c=n`, `R_y=n-1`. The incidence action and actual child rule
are

```text
M(p,q,r)=(2p+q+r, q+r, (n+d)*p+n*q+(n-1)*r),
w_child=M*w+prefix_b(j)-prefix_a(i).
```

The indices `i,j` are original zero-based positions in the literal
images. FIRST has index `0`; RUN has indices `1..R_a`; LAST has index
`R_a+1`. Every RUN child is `y`, and its proper prefix is
`e_(first(a))+(i-1)e_y`. In particular, for a `y/y` source and two RUN
indices the prefix difference is exactly `(0,0,j-i)`.

### 1.1 The exact parameter chamber and irreducibility

The parameter assumptions give `n>=6` and `5<=d<=n-1`. The characteristic
polynomial is

```text
chi(X)=X^3-(n+2)X^2+(n-d-1)X+2.
```

Its useful values are

```text
chi(0)=2,
chi(1)=-d,
chi(-1)=d-2n,
chi(2)=-2n-2d,
chi(-2)=2d-6n-12,
chi(n+1)=-(d+2)(n+1)+2,
chi(n+2)=(n-d-1)(n+2)+2.
```

Thus there is one root in each of `(-1,0)`, `(0,1)`, and `(n+1,n+2)`.
These are all three roots. The last root is the dominant root `beta`,
and its other two conjugates have modulus less than one. Every literal
two-level image contains all three letters, so the incidence matrix is
primitive. A rational root of this monic cubic would be one of
`1,-1,2,-2`; all four displayed evaluations are strictly negative.
Consequently the cubic is irreducible over `Q`, and `beta` has degree
three. Also `det M=-2`. No unimodularity or inverse-integrality premise
is introduced.

### 1.2 Exact normalized lengths and recurrence coefficients

Normalize `L_y=1` and put

```text
h=1/beta,
alpha=beta-(n+2),
delta=d/(beta-1),
L_c=1+h,
L_x=beta-n-h=L_c+delta.
```

The equality `L_x-L_c=delta` follows from the cubic:
`(beta-1)(beta-n-1-2/beta)=d`. Direct substitution gives all three
literal tile equations

```text
beta*L_x=2L_x+n+d,
beta*L_c=L_c+n+L_x,
beta=L_x+n-1+L_c.
```

Therefore inflating a source multiplies its physical displacement and
all interval lengths by `beta`, and the full integral child rule agrees
with its literal geometric displacement rule. The root bracket gives

```text
beta>n+1>=7,
0<h<1/7,
1<L_c<L_x<2,
alpha<0,
delta>0.
```

For the last length bound use `L_x=beta-n-h<2-h<2`.
The two scalar recurrence coefficients used below are

```text
A=2h, B=-alpha=n+2-beta, gamma=A+B=1-delta.
```

They satisfy `0<A<1/2`, `B>0`, and `0<gamma<1`. In particular
`0<delta<1`. These inequalities are specific to this parameter chamber;
the opposite sign of `alpha` in the preceding
[alternating-cycle theorem](class-a-central-entry-2026-11-14.md)
leads to a different periodic-state classification.

## 2. One-level word counts force a central `y/y` descendant

Call a `y/y` overlap **central** if `|u|<=1/2`. Its common interval then
has length at least `1/2`.

### 2.1 Uniform densities and their strict gap

Density here means a letter count divided by the word's physical length.
For every literal one-level image, the following simultaneous bounds hold:

```text
y density >= Y0=(n-1)/beta,
x density <= X0=2/(beta*L_x),
c density <= C0=1/beta.
```

For the `y` lower bound, the three ratios after removing the factor
`1/beta` are

```text
(n+d)/L_x=beta-2>n-1,
n/L_c=n/(1+h)>n-1,
n-1.
```

The middle inequality is equivalent to `(n-1)h<1`, which follows from
`beta>n+1`. For `x`, the three such ratios are `2/L_x,1/L_c,1`.
Their maximum is `2/L_x`, since `L_x<2` and `L_c>1`. For `c` the
ratios are `0,1/L_c,1`, with maximum one.

The quantity needed by the center-count argument is

```text
eta=Y0-2X0-2C0=(n-3-4/L_x)/beta.
```

It has the parameter-independent lower bound `eta>1/12`. Indeed
`beta-1<n+1` and `d>=5` give

```text
L_x=1+h+delta > 1+5/(n+1)=(n+6)/(n+1).
```

Since `n>=6`, the number `n^2-n-22` is positive. Hence

```text
eta > (n^2-n-22)/[(n+6)*beta]
    > (n^2-n-22)/[(n+6)(n+2)]
    >= 1/12.
```

For the last inequality, the difference after multiplication by the
positive denominator is

```text
12(n^2-n-22)-(n+6)(n+2)
  =11n^2-20n-276=(n-6)(11n+46)>=0.
```

These are finite counts in the actual three image words. No asymptotic
letter frequencies, unique ergodicity, Perron-vector convergence or
spectral theorem is used in the entry argument.

### 2.2 Boundary allowances on an actual growing common interval

Fix any strict source. Let `I` be the open interior of its common
interval, with `ell0=|I|>0`. At depth `m`, use the actual words
`sigma^m(a)` and `sigma^m(b)`, the latter translated by `beta^m u`.
Their common open interval is `I_m=beta^m I`, with length
`J=beta^m ell0`.

For `m>=1`, partition each track into its actual one-level image blocks.
The intersection with `I_m` consists of full blocks and at most two
partial boundary blocks. The largest block has at most

```text
W=n+d+2<=2n+1
```

letters and has physical length at most `beta*L_x<2(n+2)`.
Let `N_i(track,I_m)` count centers of letter-`i` tiles strictly inside
the open interval. Summing the full-block estimates gives

```text
N_y(bottom,I_m) >= Y0*J-2*beta*L_x,
N_x(top,I_m)    <= X0*J+2W,
N_c(top,I_m)    <= C0*J+2W.                         (D)
```

For the lower bound, full blocks cover at least `J-2 beta L_x` of
the interval, and `0<Y0<1`; if this length bound is negative, the
nonnegative count still gives the displayed inequality. For either
upper bound, each partial block contributes at most `W` centers and
full-block physical length is at most `J`. Thus (D) applies to the
actual interval even when its endpoints cut through image blocks.

### 2.3 The center-count contradiction

Suppose there were no central `y/y` pair among the depth-`m` actual
occurrences. A bottom `y` center in `I_m` cannot lie in a closed top
`y` tile: its distance from that unit tile's center would be at most
`1/2`, giving a central pair. It therefore lies in a top `x` or `c`
tile. If it lies on two non-`y` boundaries, assign it to either tile
once.

Bottom `y` centers are separated by at least one, since every tile
length is at least one. Each top non-`y` tile has length less than
two, so it contains at most two such centers. At most two top tiles
meet `I_m` while their own centers lie outside the open interval.
Consequently

```text
N_y(bottom,I_m) <= 2N_x(top,I_m)+2N_c(top,I_m)+4.
```

Combining this inequality with (D) gives

```text
eta*J <= 2*beta*L_x+8W+4
       < 4(n+2)+8(2n+1)+4
       = 20(n+1).                                  (E)
```

But `eta>1/12`, so (E) is impossible whenever

```text
m>=1 and beta^m*ell0 >= T=240(n+1).                 (F)
```

Every depth satisfying (F) therefore contains an actual central `y/y`
descendant. Such a depth exists because `beta>1` and `ell0>0`. The
threshold is a sufficient bound, not a shortest-depth assertion; the
required depth depends on the source's positive overlap length.

This construction also supplies an actual path. Decode the selected
top and bottom occurrences through their unique literal ancestors.
Their positive common final interval lies in both ancestor supertiles
at every earlier level. Rescaling that interval backwards proves
strictness at every generation. Thus the selected occurrences form a
composable path of strict child occurrences. No finite graph or
realization of the source in a pair of infinite tilings was assumed.

## 3. A legal central selector and its full integer recurrence

At a central source `(y,y,p,q,r)`, choose the nearest integer `e` to
`beta*u`, choosing the smaller integer in a tie. Set

```text
i=1+max(e,0), j=1+max(-e,0).
```

These are actual RUN positions in `sigma(y)`. Indeed

```text
|beta*u|<=beta/2<(n+2)/2<=n-2,
```

where the last inequality uses `n>=6`. The nearest integer has
`|e|<=n-2`, so `1<=i,j<=n-1`. The prefix difference is
`(0,0,-e)`, and the new physical shift is `u'=beta*u-e`.
It satisfies `|u'|<=1/2`. Thus this deterministic selector remains
inside genuine central strict `y/y` overlaps indefinitely.

Write `S=p+q+r`. The full child coordinates are

```text
p'=p+S,
q'=S-p,
r'=(n+d)*p+n*q+(n-1)*r-e.
```

### 3.1 Scalar recurrence with full-state reconstruction

Let `z_j` be the first integral coordinate of the `j`th selected
central state. Initially `z_0=p` and `z_1=p+S`. For an adjacent pair
`a=z_j,b=z_(j+1)`, writing `c=z_(j+2)` gives the complete next state
and its physical shift:

```text
(y,y, b, b-2a, c-3b+2a),
u_child=c+alpha*b-2h*a.
```

For the coordinate formula, use `q'=p'-2p=b-2a` and the next
sum `S'=c-b`. For the physical formula, substitute
`L_x+L_c-3=alpha` and `1-L_c=-h`. The selector is therefore exactly
the integer recurrence

```text
c=nearest_integer(A*a+B*b),
|c-(A*a+B*b)|<=1/2,                                 (R)
```

where `A=2h`, `B=-alpha`, and the larger integer is chosen in a tie.
Subtracting the nearest gap `e` from an integer reverses its tie
convention. Both descriptions choose the same actual child; Section
3.3 also shows that actual integral states never encounter a tie.

In particular the full state after the first step is a deterministic
function of the preceding integer pair. A repeated pair therefore
gives repeated full typed integral states. There is no splice between
different occurrences sharing only a projected coordinate.

### 3.2 Boundedness and a finite periodic tail

For `H=max(|a|,|b|)`, (R) and positivity of the coefficients give

```text
|c| <= (A+B)*H+1/2=(1-delta)*H+1/2.
```

Take the explicit integer

```text
C=max(|z_0|,|z_1|,n+2).
```

It is at least `1/(2delta)`, because

```text
1/(2delta)=(beta-1)/(2d)<(n+1)/10<n+2.
```

If `|a|,|b|<=C`, the same inequality gives `|c|<=C`. Induction
bounds the entire recurrence. Its deterministic integer pairs occupy
at most `N=(2C+1)^2` states; among the first `N+1` pairs some pair
repeats, giving an eventually periodic tail. Allowing one edge for the
full-state reconstruction, a periodic full overlap is reached within
`N+1` selected edges. This argument establishes periodicity, not zero
hitting: nonzero constant cycles can occur and need separate exits.

### 3.3 Half-unit exclusion and the Lean specialization boundary

The preceding written proof allowed the weak error `<=1/2`. Actual
integral states have strict error `<1/2`. The exact lengths give

```text
beta*u=p*beta^2+(q+r-n*p)*beta+(q-p).                (H)
```

If `beta*u=j+1/2` for an integer `j`, multiplication by two gives a
rational polynomial of degree at most two vanishing at `beta`, whose
constant coefficient `2(q-p)-2j-1` is odd. It is a nonzero polynomial,
contradicting the degree-three irreducibility proved in Section 1.1.
Thus nearest-gap rounding has no half-integer tie.

If `u=1/2` or `u=-1/2`, multiplication by `2 beta` instead gives
such a polynomial whose coefficient of `beta` is respectively
`2(q+r-n*p)-1` or `2(q+r-n*p)+1`. Again it is nonzero. Hence all
actual integral central states satisfy `|u|<1/2`; the recurrence error
is their child's physical shift and is also strict.

These facts justify the mathematical specialization of the strict
positive-coefficient recurrence in
[`ClassAMinusConstantRecurrence.lean`](../proof/PscVerif/PscVerif/ClassAMinusConstantRecurrence.lean).
They do not constitute an end-to-end Lean specialization. The abstract
recurrence takes its real coefficient conditions and recurrence as
hypotheses. The cubic irreducibility, exact Perron binding, all-source
density entrance, and complete nested-prefix construction here are
written mathematical arguments unless separately formalized and audited
at their own exact source. In particular a recurrence audit alone does
not discharge these family-specific interfaces.

For later use, (H) also proves injectivity of the integral physical
encoding. If `u=0`, degree-three independence forces `p=0`, then
`q-p=0`, then `q+r-n*p=0`, so `w=0`. This fact does not replace the
full integral path checks below.

## 4. Every periodic tail is a constant integral state

Consider any periodic integer sequence satisfying (R). If it has a
positive maximum `H>=1`, an occurrence of the output `H` must have
the immediately preceding entry `b=H`. To prove this, suppose
`b<=H-1`; its other input is also `a<=H`. Positivity of `A,B` gives

```text
A*a+B*b <= A*H+B*(H-1)
          =(1-delta)*H-B
          =H-[delta*(H-1)+1-A]
          <H-1/2,
```

because `delta>0`, `H>=1`, and `A<1/2`. This cannot round to `H`
under (R). Following predecessor entries backwards from a maximum now
forces the whole periodic sequence to equal `H`.

If there is no positive entry but the sequence is nonzero, negate it
and apply the same argument to its positive maximum. The absolute
error relation (R) is invariant under negation, so this forces a
constant negative sequence. The remaining sequence is identically
zero. Thus every periodic tail is constant.

Substituting `a=b=c=H` into the complete state reconstruction gives

```text
U_H=(y,y,H,-H,0), with shift delta*H.
```

Its centrality is exactly `2d|H|<=beta-1`. Since
`n<beta-1<n+1` and `2d|H|` is an integer, this is equivalent to

```text
2d|H|<=n.                                         (C)
```

In fact (C) gives strict centrality. This equivalence holds for every
integer height. Restricting to `n<5d` would leave only small heights,
but the next descent works for all heights permitted by (C).

## 5. Three actual RUN edges lower every nonzero height

Assume `H>=1` and `n>=2dH`. Define

```text
V_H=(y,y,H,-H,-1),
W_H=(y,y,H-1,-H-1,2).
```

The following three original index pairs give a complete height
decrement:

```text
U_H --(dH+2,1)--> V_H
    --(1,n+2-dH)--> W_H
    --(1+max(d(H-1)-2,0),1+max(2-d(H-1),0))--> U_(H-1).
```

### 5.1 Full affine identities

Both parent letters are `y` at every step, so the only prefix change
is `(0,0,j-i)`. The three incidence images are

```text
M(H,-H,0)=(H,-H,dH),
M(H,-H,-1)=(H-1,-H-1,dH-n+1),
M(H-1,-H-1,2)=(H-1,1-H,d(H-1)-2).
```

Their respective prefix differences add
`-dH-1`, `n+1-dH`, and `-d(H-1)+2` to the last coordinate.
This proves exactly the displayed full integral targets.

### 5.2 Every displayed index is an actual RUN index

All positions must lie in `1..n-1`, the RUN of `sigma(y)`.
For the first pair,

```text
n-1-(dH+2)=n-dH-3>=dH-3>=2.
```

For the second pair, the moving bottom index satisfies

```text
n+2-dH>=dH+2>=7,
n-1-(n+2-dH)=dH-3>=2.
```

For the third pair, if `H=1` its indices are `(1,3)`, legal since
`n>=2d>=10`. If `H>=2`, then `d(H-1)-2>=3`, so the pair is
`(d(H-1)-1,1)`. Its moving index is at least four and has upper
slack

```text
n-1-[d(H-1)-1]=n-d(H-1)>=d(H+1)>0.
```

Thus all three pairs are genuine RUN/RUN pairs on the full unbounded
domain. No LAST occurrence or small-height exception is hidden in
these formulas.

### 5.3 Strictness and termination of the height descent

The four physical shifts are

```text
shift(U_H)=delta*H,
shift(V_H)=delta*H-1,
shift(W_H)=delta*(H-1)-2h,
shift(U_(H-1))=delta*(H-1).
```

Since `0<delta H<1/2`, the first two are in `(0,1/2)` and
`(-1,-1/2)`. The third lies in `(-2h,1/2)` when `H>1` and
equals `-2h` when `H=1`; in either case it is in `(-1,1)`.
The fourth is in `[0,1/2)`. Each displayed `y/y` overlap is
therefore strict. The new height remains central, so repetition
reaches `U_0=(y,y,0,0,0)` in exactly `3H` such edges.

For a negative height apply genuine reversal: swap the two track
letters, negate all three integral coordinates, and exchange each
ordered index pair. The child rule and strictness are preserved.
This is reversal of the two overlap tracks, not reversal of the
substitution words. It gives a path of `3|H|` edges to `U_0` from
every negative constant cycle as well.

## 6. Composition, original prefixes and the two stopping policies

Start with any strict integral source. Section 2 supplies an actual
strict path to a central `y/y` state. Sections 3 and 4 supply a finite
legal RUN path into a constant cycle. If its height is zero, it is
already typed coincidence; otherwise Section 5 supplies a genuine
coincidence suffix. Concatenating these paths proves the theorem.

The central portion has the conservative source-dependent length bound

```text
(2C+1)^2+1+3*floor(n/(2d)),
C=max(|p|,|2p+q+r|,n+2)
```

for the coordinates of its first central state. This follows from the
pair bound and (C). It does not bound the coordinates of all formal
strict sources, nor assert a source-independent hitting depth.

The canonical native implementation uses the smaller valid choice
`C=max(|p|,|2p+q+r|,ceil((n+1)/(2d)))`. It satisfies the same invariant-box
premise, since `(beta-1)/(2d)<(n+1)/(2d)`. The displayed paper bound uses
`n+2` only as a simpler conservative reserve; the tighter native reserve
does not change the recurrence or its mathematical source scope.

For every actual edge retain the proper prefix words preceding its
two chosen child occurrences, with Parikh vectors `P_j,Q_j`.
Composability gives actual proper prefixes of the original depth-`m`
images, obtained by concatenating

```text
sigma^(m-1)(topPrefix_0), sigma^(m-2)(topPrefix_1), ..., topPrefix_(m-1)
```

and the analogous bottom words. Their Parikh vectors are therefore

```text
P=sum_(j=0)^(m-1) M^(m-1-j)*P_j,
Q=sum_(j=0)^(m-1) M^(m-1-j)*Q_j.
```

The full child equations telescope to

```text
w_m=M^m*w_0+Q-P.
```

At the constructed typed coincidence `w_m=0`, so `M^m w_0=P-Q`.
The source and each terminal letter belong to their actual original
addresses. This proves the requested full prefix identity through a
composable path, not merely the existence of two equal projected sums.

For the typed-coincidence conclusion, a mixed-letter state with
integral offset zero is not terminal. The density construction applies
to it as to every other strict source. Continue that transcript unless
an earlier typed coincidence has already occurred; in that event stop
there. From the central target onwards the construction stays `y/y`,
so every zero encountered in that portion is typed.

For a BH implementation whose contract terminalizes at every integral
zero, instead stop at the first integral-zero hit. This only shortens
the successful path and preserves its actual prefix identity at that
depth. A transcript executed under this weaker stopping policy is not
evidence that a subsequent typed continuation was executed. The two
canonical receipt scopes must remain distinct.

## 7. Seed-domain consequence and the boundary of the new theorem

### 7.1 The manuscript's swap seeds are included without another premise

The manuscript's `sec:overlap` in
[`PSC_balanced_pair_state_2026-09-13.tex`](../manuscripts/PSC_balanced_pair_state_2026-09-13.tex)
defines `O_sigma` by actual level-zero contacts of the aligned `ab/ba`
patches and their strict children, with typed coincidences terminal.
Its headline BH lemma B quantifies over cyclic vertices of that graph.
The present theorem covers every one of those sources and every strict
descendant in the stated chamber, including transient vertices.

For clarity, `L_x>L_c>L_y` here. For each pair with `L_a>L_b`, the
aligned patches top `ab` and bottom `ba` have exactly these three
strict contacts:

| Top/bottom types | Integral bottom-minus-top offset |
| --- | --- |
| `a,b` | `0` |
| `a,a` | `e_b` |
| `b,a` | `e_b-e_a` |

The fourth possible contact, `b,b` at `-e_a`, is not strict because
`L_a>L_b`. The three unordered pairs give nine roots; reversing the
two patches gives nine further roots. Thus the orientation-complete
`S18` root convention used in the preceding work applies unchanged.
The exact root derivation is also set out in
[the original nine-seed note](class-a-nine-swap-to-x-2026-10-31.md#correct-object-and-substitution-parameters).

Inflation and enumeration of all original ordered child occurrences
give the same literal child relation in this proof and in the
manuscript. The full-to-physical map is injective by (H). Conversely,
every actual strict contact at a deeper level has a strict pair of
ancestor tiles, since their common child interval has positive length.
This is the usual literal ancestor argument, not a finite-type
assumption. Terminalizing a typed coincidence removes no later
noncoincidence: its two identical inflated words agree at matching
positions, and interiors of different tiles of that common word are
disjoint.

It follows that every S18 seed-reachable strict vertex in this chamber
has a composable typed-coincidence path. No additional dictionary for
arbitrary overlaps of infinite tilings is needed for this seed-patch
statement. The theorem itself already starts from all formal strict
integral sources.

The same proof applied to the six aligned mixed-letter sources
`(a,b,0)`, `a!=b`, gives terminal equal letters with `P=Q`.
Thus aligned eventual letter-pair coincidence also holds at this
family scope. This is not a universal A1-prime theorem for arbitrary
ternary substitutions, and no spectral conclusion is asserted here.

### 7.2 Parameter assembly must retain the two seam lines

Writing the run parameters as `(p_run,q_run,r_run)=(n+d,n,n-1)`,
the minus-Class-A PIP domain is `n>=1, 1<=d<=2n-1`, as recorded in
[the Class-A run-index domain derivation](p1b-class-a-run-index-2026-10-21.md#exact-residual-families-and-seed-configurations).
The current theorem supplies exactly `d>=5, d<=n-1` within it.
The earlier alternating-cycle theorem uses

```text
n=k+t+3, d=k+2t+5, k,t>=0,
```

equivalently `n+2<=d<=2n-1`; for its six small parameters the earlier
result has the separately certified S18 scope, not an all-strict scope.
These two chambers do not include `d=n` or `d=n+1`.

Under `p_run=n+d`, `q_run=n`, those seams are respectively the
previously recorded Class-A lines `p_run=2q_run` and
`p_run=2q_run+1`. The cited run-index note records the earlier
certified lines `p_run=2q_run+k`, `k=0,1,2,3`, for both signs.
They are separate dependencies for any full minus-Class-A assembly;
the present proof does not infer their certificates from an endpoint
limit of either open chamber. In particular, the Class-B leading
theorems of the similarly named symbolic-line and symbolic-cone notes
must not be substituted for a Class-A seam certificate.

The regions `d<=4` likewise retain their separate earlier proofs:
[the minus `d=1` line](class-a-minus-line-2026-10-22.md),
[the residue rays for minus `d=2,3`](class-a-residue-rays-2026-10-22.md),
and [the `d=4` rays](class-a-d4-rays-2026-10-23.md).
The older [gap theorem](class-a-gap-theorem-2026-10-23.md) covers
`d>=5,n>=5d` at its stated seed-graph scope. The present argument
overlaps that region and also supplies the former residual strip
`d+1<=n<5d`, with the stronger all-strict-source quantifier throughout
the new chamber.

The exact inherited coverage is summarized below. A residue-floor vector
is ordered by `r=0,...,d-1`; its finite part consists of every admissible
smaller `n` in that residue, checked by complete graphs.

| Minus parameter region | Mathematical source scope and coverage | Source contract |
| --- | --- | --- |
| `d=1, n>=1` | Every canonical swap-seed vertex; uniform carrier/descent for `n>=8`, complete `n=1..7` | [Minus-line Theorems A, B and Corollary C'](class-a-minus-line-2026-10-22.md) |
| `d=2, n>=2` | Every canonical swap-seed vertex; residue floors `(14,15)` and all smaller admissible members | [Residue-ray Theorem R and Corollary L](class-a-residue-rays-2026-10-22.md) |
| `d=3, n>=2` | Every canonical swap-seed vertex; residue floors `(15,19,20)` and all smaller admissible members | [Residue-ray Theorem R and Corollary L](class-a-residue-rays-2026-10-22.md) |
| `d=4, n>=3` | Every canonical swap-seed vertex; residue floors `(24,25,22,23)` and all smaller admissible members | [Gap-four theorem](class-a-d4-rays-2026-10-23.md), [current ray registry](../kernel/psc/class_a_ray_tables.mojo) |
| `d>=5, d<=n-1` | Every formal strict integral source | Sections 1–6 of this note |
| `d=n` within the PIP domain | Every canonical swap-seed vertex; symbolic tail `n>=39`, complete `n=1..38` | Class-A `k=0` row of [Theorem L″](p1b-boundary-hitting-progress-2026-10-08.md), [current pin file](../kernel/symbolic_line_pins.txt) |
| `d=n+1` within the PIP domain | Every canonical swap-seed vertex; symbolic tail `n>=87`, complete `n=2..86`; `n=1` is non-PIP and `n=0` outside | Class-A `k=1` row of [Theorem L″](p1b-boundary-hitting-progress-2026-10-08.md), [current pin file](../kernel/symbolic_line_pins.txt) |
| `n+2<=d<=2n-1` | All strict sources when `n>=6`; the six `n<6` cases have complete S18 seed scope | [Alternating-cycle theorem and small-case adapter](class-a-central-entry-2026-11-14.md), [its exact-source packet](../evidence/class-a-central-entry-2026-11-14/README.md) |

The two seam rows in the current canonical pin file are exactly

```text
line A 2 0 1 0 1 -1 39 281 38 0 1
line A 2 1 1 0 1 -1 87 365 85 1 1
```

The fields after the affine word parameters are the symbolic floor,
symbolic vertex count, and the PIP/non-PIP/outside counts below that
floor. The pins record the expected verdicts; they are not inputs to
the mathematical certificate. The current
[`certify` implementation](../kernel/symbolic_line_certificate.mojo)
requires every symbolic vertex to reach full offset zero and runs
the exact complete graph on every admissible PIP parameter below
the floor. The underlying graph stores the full polynomial Parikh
offset and certifies the legal original segment/run differences.
The 2026-10-30 fit-first correction in the Theorem L″ note records
the native recertification returning these rows to their original
floors.

These source contracts **complete the mathematical parameter cover for
minus-Class-A boundary hitting on the canonical swap-seed domain**:
`n>=1, 1<=d<=2n-1`. Reversing an actual track pair supplies the second
orientation when an inherited graph uses one orientation of each swap
seed. No all-strict-source conclusion on the small gaps, seam lines,
or six small upper-chamber members is inferred from their seed-domain
certificates.

Inherited validation remains an explicit dependency. The earlier
[gap-four integration packet](../evidence/issue139-ac-integration-2026-10-23/README.md)
replays the default and alternative tables separately. The later
[independent-audit packet](../evidence/class-a-gap-independent-audit-2026-10-23/README.md)
records successful native replay of all 25 tabulated residue rays,
including every minus low-gap ray; its
[manifest](../evidence/class-a-gap-independent-audit-2026-10-23/SHA256SUMS),
[source digest list](../evidence/class-a-gap-independent-audit-2026-10-23/source-sha256.txt)
and [exit record](../evidence/class-a-gap-independent-audit-2026-10-23/exits.json)
retain their exact historical scopes. Several shared source files changed
after the original low-gap packets, so their older hashes cannot be
relabeled as current-head receipts. The relevant inherited carrier,
descent, line, symbolic engine and pin files are unchanged from the
starting source `34ff471c` in this increment. This source comparison
does not claim a new execution of the old certificates.

The documented hosted class-D rebind of the shared fit-first engine is
not itself a hosted replay of the two Class-A seam lines. Accordingly
the assembled mathematical coverage, inherited acceptance records,
new exact-source checks and a fresh combined hosted acceptance must
be reported separately. No governed claim promotion is performed
here. Universal BH, plus-Class-A, arbitrary-ternary A1-prime, C4, G1,
PDS, PSC and arbitrary alphabets remain outside this assembled
boundary-hitting statement. The nonunit full integral path equality
has been proved without importing a unit-only spectral theorem.

## 8. Evidence obligations and formal scope

The written proof has supplied the unbounded hypotheses needed for
the three mechanisms: the one-level density gap and its boundary
constants; legality and boundedness of every selected central RUN
step; and classification and actual exits for every periodic height.
A finite family of sampled paths cannot replace any of these
quantifiers.

The accompanying canonical implementation must bind the literal words,
the exact Perron field, the physical length normalization, and the
parameter chamber before applying this selector. The old `k,t>=0`
upper-chamber validator rejects these parameters by design; it must
not be bypassed by allowing negative old coordinates or accepting a
foreign field. A checked general `(n,d)` binding is required.

Independent replay must retain every original occurrence ordinal and
all three offset coordinates, compose the actual original prefixes,
and distinguish first-integral-zero from first-typed-coincidence
stopping. Controls must reject an altered literal image, incompatible
field, out-of-domain parameter, noncentral selector source, illegal
RUN index, altered full vector, nonzero constant cycle mistaken for
zero, and a search cap mistaken for a proof of coverage or hitting.
Long heights and reversed paths matter: no `H<=2` restriction occurs
in the mathematical theorem.

The abstract Lean recurrence and literal affine/ordinal lemmas, exact
native certificates, and independent literal-word oracle have their
own acceptance boundaries. The full written theorem also uses the
Perron identification, one-level center-count entrance, actual strict
ancestry and original-prefix composition. Report the precise audited
endpoints and source revisions rather than describing a successful
subtheorem audit as an end-to-end Lean proof of this family theorem.

The [pre-code gate](bh-class-a-minus-constant-stop-go-2026-11-14.md)
also records the relevant literature boundaries: eventual periodicity
of a rounded contraction does not establish zero hitting, a finite
overlap-type graph does not supply a source-uniform depth by itself,
and a nonunit spectral consumer needs its own actual hypotheses.
Exact-head hosted acceptance and independent human review remain
distinct from the mathematical proof given here.

### 8.1 Implemented verification and its observed limits

The canonical [central constructor](../kernel/psc/class_a_minus_constant_entry.mojo)
binds the literal ordered words, cubic coefficients, positive scaling and
every cached original prefix before applying the nearest RUN or height
descent. The [entry constructor](../kernel/psc/class_a_minus_entry_search.mojo)
enumerates actual strict children in original order and retains full
integral ancestry. Its two public stopping policies implement precisely
the distinction in Section 6. The independent
[literal-word oracle](../oracles/python/class_a_minus_constant_entry.py)
rebuilds selected incidence and prefix counts, checks every returned
occurrence, and composes the complete original-prefix equality. The
[symbolic oracle](../oracles/python/class_a_minus_constant_symbolic.py)
checks the two exhaustive height chambers and the root/density identities.

The independent Lean audit checks these exact endpoints:

| Endpoint | Formal conclusion |
| --- | --- |
| `forward_integer_bound` | Every forward strict nearest recurrence under the displayed coefficient inequalities is bounded. |
| `bounded_two_sided_classification` | Every bounded two-sided recurrence is a signed constant. |
| `periodic_cycle_classification` | A supplied positive period implies a constant sequence and its amplitude inequality. |
| `eventual_constant_tail` | Every forward recurrence has a constant tail; boundedness and periodicity are derived. |
| `constant_nearest_iff` | The exact signed constant-amplitude criterion. |
| `three_run_decrement` | Three original indexed RUN steps with the complete intermediate integral packets. |
| `constant_composable_path` | Every signed height with `2d|H|<=n` has a strict composable path to typed zero, under explicit positive lengths and exact substitution scaling. |

The last endpoint derives source strictness backwards from the final
coincidence; it does not assume either an interior source or a supplied
hitting path. It still does not supply central entry for an arbitrary
overlap, the family Perron specialization, or the final nested-prefix
assembly for arbitrary starting sources.

The [evidence packet](../evidence/class-a-minus-constant-entry-2026-11-14/README.md)
records passing canonical checks, 39 targeted independent tests and the
cached development audit of 75 owned declarations, including 68 theorem
declarations, seven exact endpoint types and 21 rejection controls.
The separately launched fresh-source gate bound 127 source/configuration
files and verified freshly cloned dependency pins, then stopped at the
fixed upstream Mathlib cache: every download returned HTTP 403. It did
not compile the new local theorem in that fresh workspace. This failed
receipt is retained, and source-isolated acceptance remains pending.
The dedicated workflow and the repository-wide Lean workflow must be
assessed at their actual producing head; cached development acceptance
and parent receipts do not stand in for those outcomes.
