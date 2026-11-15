# Plus Class A: actual constant-cycle entry for `n>=6, 5<=d<=n+4`

Date: November 14, 2026 (America/New_York). Starting source: draft PR #579
at `110e7e9ef8243bc24adf80d6e8a375add586d850`.

**Status: a complete written proof at the stated all-source family scope;
executable and formal acceptance are separate, and independent human review
remains pending.** This full theorem is not an end-to-end Lean theorem.
Section 7 combines it with the five complete small-member certificates and
authenticated inherited results to establish mathematical swap-seed coverage
for `n>=0,1<=d<=n+4`. No governed claim status changes solely because of
this note.

**Theorem (repository-proved).** Let `n,d` be integers with `n>=6` and
`5<=d<=n+4`, and use the literal ordered substitution

```text
sigma(x)=x y^(n+d) x,
sigma(c)=c y^n x,
sigma(y)=x y^(n+1) c.
```

Every strict integral overlap has a finite composable path of actual ordered
child occurrences to typed coincidence. If the source's bottom-minus-top
integral offset is `w`, the retained original depth-`m` proper prefix
occurrences have Parikh vectors `P,Q` satisfying `M^m w=P-Q`.

The quantifier includes every formal strict integral source for these
literal words. Cyclicity, seed reachability and membership in a previously
constructed carrier are not hypotheses. The depth may depend on the source
and both parameters. The full plus-Class-A PIP domain is larger:
`n>=0,1<=d<=2n+11`. In particular the upper region `d>=n+5` is not covered
by this all-source theorem.

The [pre-code source and hypothesis gate](bh-class-a-plus-constant-stop-go-2026-11-14.md)
records the primary-source review and the narrowed decision. Literal word
counts force a central `y/y` descendant. A nearest RUN rule gives a bounded
integer recurrence with a negative first coefficient; every periodic tail
is constant. Three actual RUN edges lower any nonzero constant height.
Every original occurrence and all three integral coordinates are retained.

## 1. Literal coordinates, the cubic and positive tile lengths

Use `(x,c,y)=(0,1,2)`. A state `(a,b,p,q,r)` has top and bottom letters
`a,b`, full integral offset `w=(p,q,r)` in that coordinate order, and
physical bottom-minus-top displacement

```text
u=L_x*p+L_c*q+r.
```

The top and bottom intervals are `[0,L_a]` and `[u,u+L_b]`. They are
strictly overlapping when their intersection has positive length. Put
`R_x=n+d`, `R_c=n`, `R_y=n+1`. The incidence and literal child equations
are

```text
M(p,q,r)=(2p+q+r, q+r, (n+d)*p+n*q+(n+1)*r),
w_child=M*w+prefix_b(j)-prefix_a(i).
```

Each index is an original zero-based position in its actual image. FIRST
has index `0`, RUN has indices `1..R_a`, and LAST has index `R_a+1`.
The proper prefix of a RUN occurrence is
`e_(first(a))+(i-1)e_y`. For a `y/y` source with two RUN positions the
prefix difference is consequently exactly `(0,0,j-i)`.

### 1.1 Root isolation, irreducibility and the Pisot property

The characteristic polynomial and determinant are

```text
chi(X)=X^3-(n+4)*X^2+(n-d+5)*X-2,
det M=2.
```

The following exact evaluations suffice:

```text
chi(1)=-d,
chi(-1)=d-2n-12,
chi(2)=-2(n+d),
chi(-2)=2d-6n-36,
chi(n+3)=(2-d)(n+3)-2,
chi(n+4)=(n-d+5)(n+4)-2.
```

The last two have opposite signs on the stated parameter domain. Thus
there is a positive root `beta` with

```text
n+3<beta<n+4.
```

The first four values are strictly negative. A reducible monic cubic with
constant term `-2` would have an integer root among `1,-1,2,-2`. Therefore
`chi` is irreducible over `Q` and `beta` has degree three.

To check all conjugates, define `A=2/beta` and `B=n+4-beta`. Division at
the root gives

```text
chi(X)=(X-beta)*(X^2-B*X+A),
0<A<2/9<1,
0<B<1.
```

If the other two roots are real, their positive product and positive sum
make both positive, and each is strictly below their sum `B<1`. If they
are nonreal, they are a conjugate pair of modulus `sqrt(A)<1`. In either
case `beta` is dominant and the cubic is Pisot. This argument does not
assume that all three roots are real. Every two-level image contains all
three letters, so `M` is primitive. In particular these are genuine
primitive irreducible Pisot substitutions of determinant plus two; no
unimodularity or inverse-integrality hypothesis is introduced.

### 1.2 Normalized lengths and the signed recurrence coefficients

Normalize `L_y=1` and set

```text
h=1/beta,
alpha=beta-(n+4),
delta=d/(beta-1),
L_c=1-h,
L_x=beta-n-2+h=L_c+delta.
```

The equality between the two formulas for `L_x` follows from
`(beta-1)(beta-n-3+2/beta)=d`, which is the cubic identity divided by
`beta`. Direct substitution gives all literal eigenlength equations:

```text
beta*L_x=2L_x+n+d,
beta*L_c=L_c+n+L_x,
beta=L_x+n+1+L_c.
```

Therefore literal inflation scales all intervals and displacements by
`beta`, and the integral child equation agrees with the geometric child
equation. The root bracket implies

```text
beta>n+3>=9,
0<h<1/9,
0<L_c<1<L_x<2+h<3,
alpha<0,
delta>0.
```

For the scalar recurrence put

```text
A=2h,
B=-alpha=n+4-beta,
gamma=A+B=1+4h-delta.
```

Here `0<A<1/2`, `B>0`, and `0<gamma<1`. For the last inequality,
`delta=d/(beta-1)>d/beta>=5h`, so

```text
1-gamma=delta-4h>h>0.                              (G)
```

Also `1+A-B=delta`. The first coefficient of the nearest recurrence is
`-A`, not `A`; the plus proof below uses an absolute maximum for precisely
this reason. The earlier minus-family constructor and its parameter guard
are not a substitute for this literal plus-family binding.

## 2. Literal center counts force a central `y/y` descendant

A `y/y` overlap is **central** when `|u|<=1/2`; its common interval then
has length at least `1/2`.

### 2.1 One-level density bounds

Density here is a letter count divided by the physical length of one
literal image word. Every one-level image satisfies

```text
y density >= Y0=n/(beta*L_c),
x density <= X0=max(2/L_x,1/L_c)/beta,
c density <= C0=1/(beta*L_c).                      (D0)
```

For the first bound, the three ratios with the common factor `1/beta`
removed are `(n+d)/L_x`, `n/L_c`, and `n+1`. The eigenlength equations
give

```text
(n+d)/L_x=beta-2,
n/L_c=beta-1-L_x/L_c<beta-2,
(n+1)*L_c-n=1-(n+1)/beta>0.
```

Thus the middle ratio is the least. The corresponding `x` ratios are
`2/L_x,1/L_c,1`, and the `c` ratios are `0,1/L_c,1`; since `L_c<1`,
their maxima are exactly those in (D0). Also `0<Y0<1`, because
`beta*L_c=beta-1>n+2>n`.

Let `K=ceil(L_x)`, so `2<=K<=3`. A half-open interval of length `L_x`
contains at most `K` points separated by at least one. The elementary
bound `K<=2L_x` for `L_x>1` gives

```text
K*max(2L_c/L_x,1)<=4,
K*X0<=4/(beta*L_c).
```

Consequently the density deficit relevant to central entry is

```text
eta=Y0-K*X0-C0
   >=(n-5)/(beta*L_c)
   >(n-5)/(n+3)
   >=1/9.                                         (D1)
```

The final inequality is `9(n-5)-(n+3)=8(n-6)>=0`. It is the strict
root bound in the preceding inequality that makes `eta>1/9` even at
`n=6`. These are actual finite letter counts, not limiting frequencies
or an application of unique ergodicity.

### 2.2 Partial blocks on the original growing common interval

Fix an arbitrary strict source, and let its common open interval have
length `ell0>0`. At depth `m`, use the actual words `sigma^m(a)` and
`sigma^m(b)` at their actual translated positions. Their common open
interval `I_m` has length `J=beta^m*ell0`.

For `m>=1`, partition each track into its genuine one-level image blocks.
Inside `I_m` there are full blocks and at most two partial boundary
blocks. Every block has at most

```text
W=n+d+2<=2n+6
```

letters and physical length at most `beta*L_x<3(n+4)`. If `N_i` counts
centers of letter-`i` tiles strictly inside `I_m`, (D0) gives

```text
N_y(bottom,I_m)>=Y0*J-2*beta*L_x,
N_x(top,I_m)<=X0*J+2W,
N_c(top,I_m)<=C0*J+2W.                            (D2)
```

For the lower bound, full blocks have total length at least
`J-2 beta L_x`, and `Y0<1`; if this length bound is negative the
nonnegative count still satisfies the displayed estimate. For the upper
bounds, full blocks have total length at most `J`, while each partial
block contains at most `W` tile centers. These estimates therefore
apply even when the endpoints cut through image blocks or individual
tiles.

### 2.3 The center-count contradiction and actual ancestry

Suppose no depth-`m` actual occurrence pair is a central `y/y` overlap.
A bottom `y` center in `I_m` cannot belong to a closed top `y` tile:
the two unit-tile centers would be at distance at most `1/2`, giving
the forbidden central overlap. Thus each such center belongs to a top
`x` or `c` tile. Assign a center on a boundary of two non-`y` tiles to
the half-open tile on its right, so it is counted exactly once.

Any two bottom `y` centers are separated by at least one. This holds
even though `L_c<1`: the two unit `y` tiles themselves contribute a
half-unit at each end, and intervening tiles have positive lengths.
A top `x` tile therefore contains at most `K` assigned centers, and a
top `c` tile at most one. At most two top tiles intersect `I_m` while
their own centers lie outside its open interior. Their combined extra
allowance is at most `2K`. Hence

```text
N_y(bottom,I_m)<=K*N_x(top,I_m)+N_c(top,I_m)+2K.
```

Together with (D2), this implies

```text
eta*J<=2*beta*L_x+2(K+1)*W+2K
     <6(n+4)+8(2n+6)+6
     =22n+78
     <40(n+3).                                    (D3)
```

Since `eta>1/9`, (D3) is impossible whenever

```text
m>=1 and beta^m*ell0>=360(n+3).                    (D4)
```

Such a depth exists because `beta>1`. The constant in (D4) is a
sufficient bound, not a shortest-depth assertion.

The selected deep top and bottom occurrences have unique literal
ancestors in the original substituted words. Their positive common
final interval lies inside both ancestor supertiles at each earlier
generation. Rescaling that interval backwards proves strict overlap
at every stage. Decoding the two actual addresses therefore gives a
composable path of strict child occurrences to the selected central
pair. No graph finiteness or embedding of the source into two infinite
tilings is needed.

## 3. The legal nearest RUN rule and full recurrence

At a central integral state `(y,y,p,q,r)`, choose the nearest integer
`e` to `beta*u`, taking the smaller integer in a tie, and set

```text
i=1+max(e,0),
j=1+max(-e,0).
```

The choices are genuine RUN positions of `sigma(y)`, whose RUN is
`1..n+1`. Indeed

```text
|beta*u|<=beta/2<(n+4)/2<=n-1
```

for `n>=6`. A nearest integer consequently has `|e|<=n-1`, so in
fact `1<=i,j<=n`. The physical child shift is `u'=beta*u-e`, with
`|u'|<=1/2`, and the exact integral prefix difference is `(0,0,-e)`.
The rule preserves strict central `y/y` overlaps indefinitely.

Write `S=p+q+r`. The full next state satisfies

```text
p'=p+S,
q'=S-p,
r'=(n+d)*p+n*q+(n+1)*r-e.
```

### 3.1 Scalar recurrence and reconstruction of the whole state

Let `z_j` be the first integral coordinate of the `j`th selected
state. Initially `z_0=p`, `z_1=2p+q+r`. For adjacent inputs
`a=z_j,b=z_(j+1)` and output `c=z_(j+2)`, the entire next state is

```text
(y,y,b,b-2a,c-3b+2a).
```

This follows from `q'=p'-2p` and the next coordinate sum `c-b`.
Using `L_x+L_c-3=alpha` and `1-L_c=h`, its physical shift is

```text
u_child=c+alpha*b+2h*a.
```

Thus the selected scalar recurrence is exactly

```text
c=nearest_integer(-A*a+B*b),
|c-(-A*a+B*b)|<=1/2,                               (R)
```

with the larger-integer tie convention when stated this way. Subtracting
the chosen gap from an integer reverses the tie convention. Section 3.3
shows that actual integral states encounter no ties, so the two formulas
have exactly the same unique selected child.

In particular a repeated adjacent integer pair gives a repeated full
typed state after the next edge. Reconstruction uses both input
coordinates and the actual selected edge; it does not splice unrelated
literal contexts with equal projected labels.

### 3.2 A finite integer-pair bound and eventual periodicity

For `H=max(|a|,|b|)`, the triangle inequality in (R) gives

```text
|c|<=(A+B)*H+1/2=gamma*H+1/2.
```

Take the explicit integer

```text
C=max(|z_0|,|z_1|,n+4).
```

By (G),

```text
1/[2(1-gamma)]<beta/2<(n+4)/2<=C.
```

Therefore `|a|,|b|<=C` implies `|c|<=C`, and induction bounds
the whole recurrence. Its deterministic adjacent pairs occupy at
most `N=(2C+1)^2` values. Among the first `N+1` pairs a pair repeats,
and the forward sequence is eventually periodic. Allowing one step
for full-state reconstruction, a periodic full overlap is reached
within `N+1` selected edges.

This proves eventual periodicity, not a zero hit. Nonzero constant
cycles are actual nearest-selector fixed points and require the
alternative occurrence paths constructed below.

### 3.3 No half-unit ties; injectivity of the full integral encoding

The exact lengths give, for every integral offset,

```text
beta*u=p*beta^2+(q+r-(n+2)*p)*beta+(p-q).           (H)
```

If `beta*u=j+1/2` for an integer `j`, multiplying by two gives a
rational polynomial of degree at most two vanishing at `beta`, with
odd constant coefficient `2(p-q)-2j-1`. It is nonzero, contradicting
degree-three irreducibility. Therefore nearest-gap selection never
has a half-integer tie.

Likewise `u=1/2` or `u=-1/2` would give a nonzero degree-at-most-two
polynomial after multiplication by `2 beta`: its coefficient of
`beta` is respectively `2(q+r-(n+2)p)-1` or
`2(q+r-(n+2)p)+1`, which is odd. Consequently every actual integral
central state satisfies `|u|<1/2`, and the recurrence error is strict.

Finally, `u=0` in (H) forces `p=0`, then `q=0`, then `r=0` by
the same rational independence. The physical encoding is injective
on the full integral offsets. This does not excuse omitting integral
coordinates or prefix identities from a path certificate.

## 4. Every periodic tail is a constant integral state

Consider a periodic integer sequence satisfying the absolute error
relation (R). Let `H` be its maximum absolute value. If `H=0` it is
zero. Otherwise negate the entire sequence if necessary so that some
entry attains the positive value `H>=1`; negation preserves (R).

For an output `c=H`, the immediately preceding input must be `b=H`.
Indeed, if `b<=H-1`, then `a>=-H`, and positivity of `A,B` gives

```text
-A*a+B*b<=A*H+B*(H-1)
          =gamma*H-B
          =H-[(1-gamma)*(H-1)+1-A]
          <H-1/2.
```

Here `1-gamma>0`, `H>=1` and `A<1/2`. This is incompatible with
an output `H` satisfying (R). Repeating the predecessor argument
around the period forces every entry to equal `H`. Undoing the
possible negation proves that every periodic tail is a signed constant.
The use of a maximum **absolute** value is essential for the negative
coefficient of `a`.

Substituting `a=b=c=H` into the full reconstruction gives

```text
U_H=(y,y,H,-H,0),
shift(U_H)=delta*H.
```

Its centrality is `2d|H|<=beta-1`. Because
`n+2<beta-1<n+3` and the left side is integral, this is equivalent to

```text
2d|H|<=n+2.                                       (C)
```

Every height satisfying (C) is strictly central. The identity
`1+A-B=delta` shows directly that (C) also makes `H` the unique
nearest integer to `-A*H+B*H`. A nonzero such packet is therefore
an actual fixed point of the nearest selector, not a zero return.

## 5. Three original RUN edges lower every nonzero height

Let `H>=1` satisfy `2dH<=n+2`, so `n>=2dH-2>=8`. Define

```text
V_H=(y,y,H,-H,-1),
W_H=(y,y,H-1,-H-1,2).
```

The following three original index pairs give the height decrement:

```text
U_H --(dH+2,1)--> V_H
    --(1,n+4-dH)--> W_H
    --(d(H-1)+3,1)--> U_(H-1).
```

### 5.1 Full integral affine identities

All parent and child letters are `y`. The incidence images are

```text
M(H,-H,0)=(H,-H,dH),
M(H,-H,-1)=(H-1,-H-1,dH-n-1),
M(H-1,-H-1,2)=(H-1,1-H,d(H-1)+2).
```

The three proper-prefix differences add respectively
`-dH-1`, `n+3-dH`, and `-d(H-1)-2` to the last coordinate.
Thus the displayed targets hold in all three integral coordinates.

### 5.2 Every position is a genuine RUN occurrence

All displayed positions must lie in `1..n+1`. For the first pair,

```text
n+1-(dH+2)=n-dH-1>=dH-3>=2.
```

For the second pair,

```text
n+4-dH>=dH+2>=7,
n+1-(n+4-dH)=dH-3>=2.
```

For the third pair, its moving index is at least three, and

```text
n+1-[d(H-1)+3]=n-dH+d-2
                       >=dH+d-4>=6.
```

Hence every selected occurrence is RUN, including `H=1`. There is
no implicit LAST substitution, missing small-height branch or restriction
to a sampled height range.

### 5.3 Strictness and repeated decrement

The four physical shifts are

```text
shift(U_H)=delta*H,
shift(V_H)=delta*H-1,
shift(W_H)=delta*(H-1)+2h,
shift(U_(H-1))=delta*(H-1).
```

The first lies in `(0,1/2)` and the second in `(-1,-1/2)`.
For the third use `delta>5h>2h`:

```text
0<delta*(H-1)+2h<delta*H<1/2.
```

The fourth lies in `[0,1/2)`. Every displayed unit `y/y` pair is
therefore a strict overlap. The lowered height remains central and
satisfies (C). Repeating the three-edge construction reaches
`U_0=(y,y,0,0,0)` in exactly `3H` edges.

For negative `H`, swap the two overlap tracks, negate the full offset,
and exchange each original ordered index pair. The exact child equation
and strictness are preserved. This is reversal of the overlap tracks,
not reversal of the substitution words. It supplies a `3|H|`-edge
typed-coincidence path from every negative constant packet as well.

## 6. Composition, original prefixes and stopping policies

Starting from any strict integral source, Section 2 supplies an actual
strict path to a central `y/y` state. Sections 3 and 4 supply a finite
legal RUN path into a constant packet. If its height is nonzero,
Section 5 supplies a typed-coincidence suffix; height zero is already
typed coincidence. Concatenation proves the theorem.

For the first central state's coordinates `(p,q,r)`, one conservative
bound on the central portion is

```text
(2C+1)^2+1+3*floor((n+2)/(2d)),
C=max(|p|,|2p+q+r|,n+4).
```

The bound depends on the source coordinates and parameters. It is not
a uniform coordinate bound for all strict sources, nor a
parameter-independent hitting-depth bound.

For each actual edge retain the two proper prefix words, with Parikh
vectors `P_j,Q_j`. Composability makes

```text
sigma^(m-1)(topPrefix_0) ... sigma(topPrefix_(m-2)) topPrefix_(m-1)
```

an actual proper prefix of the original `sigma^m(a)` ending immediately
before its selected terminal occurrence. The analogous concatenation
is an actual proper prefix of `sigma^m(b)`. Their vectors are

```text
P=sum_(j=0)^(m-1) M^(m-1-j)*P_j,
Q=sum_(j=0)^(m-1) M^(m-1-j)*Q_j.
```

Iterating the full child equation gives

```text
w_m=M^m*w_0+Q-P.
```

The constructed typed endpoint has `w_m=0`, so `M^m w_0=P-Q`.
The prefix vectors are attached to the original actual ordered
occurrences throughout. Equal projected sums alone were never used
to justify composability.

For typed coincidence, a mixed-letter state at integral offset zero
is not terminal. Apply the entry argument to it like any other strict
source, unless a typed coincidence has already appeared, in which
case stop at that first typed coincidence. From the central target
onwards all constructed states have type `y/y`.

For BH, which permits unequal terminal letters at integral offset
zero, instead stop at the first such zero. This only shortens the
successful actual path and gives its original-prefix equality at
that earlier depth. A first-zero receipt does not claim that an
additional typed continuation was executed. Source zero has a
depth-zero BH hit even if typed continuation still requires work.

## 7. Canonical swap seeds and the precise parameter assembly

### 7.1 The actual seed sources are covered

The manuscript's `sec:overlap` in
[`PSC_balanced_pair_state_2026-09-13.tex`](../manuscripts/PSC_balanced_pair_state_2026-09-13.tex)
defines the seed graph from aligned `ab/ba` patches and all their
strict actual child occurrences. The present all-source theorem
includes every one of those sources and every transient or cyclic
strict descendant in its chamber.

The length ordering here is `L_x>L_y>L_c`, unlike the preceding
minus chambers. For each pair written with `L_a>L_b`, the aligned
patches top `ab`, bottom `ba` have exactly three strict contacts:

| Top/bottom types | Integral bottom-minus-top offset |
| --- | --- |
| `a,b` | `0` |
| `a,a` | `e_b` |
| `b,a` | `e_b-e_a` |

The fourth candidate `b,b` at offset `-e_a` is not strict. The three
unordered letter pairs give nine roots; reversing the two tracks
gives the other nine orientations. This is the orientation-complete
`S18` convention. Correct plus lengths, not a minus-specific ordering,
must be used to enumerate it.

The full integral-to-physical map is injective by (H). Every actual
deeper strict contact has strict ancestors, because its positive
common interval lies in the ancestor tiles. Thus the literal
occurrence relation in this proof agrees with the seed-patch
relation. Terminalizing typed coincidence loses no later
noncoincidence: identical inflated words agree at matching positions,
and interiors of different tiles in that word are disjoint.

The all-source theorem therefore supplies every required S18
seed-reachable hit in the new chamber, including transient vertices.
It also applies to every aligned mixed-letter source `(a,b,0)`.
For such a source the terminal prefixes satisfy `P=Q`, giving aligned
eventual letter coincidence at this family scope. No universal A1-prime
or spectral conclusion follows from that scoped consequence.

### 7.2 Existing coverage and the five small members

The full plus-Class-A determinant-two PIP domain is
`n>=0,1<=d<=2n+11`, from
[the run-index domain proof](p1b-class-a-run-index-2026-10-21.md#exact-residual-families-and-seed-configurations).
The new all-source theorem handles all `n>=6,5<=d<=n+4`.
Existing low-gap and four seam certificates retain their complete
canonical swap-seed scope:

| Parameter region | Mathematical source scope and exact coverage | Source |
| --- | --- | --- |
| `d=1` | Every canonical swap-seed vertex; tail `n>=8`, complete `n=4..7`; complete `n=1..3` from the run-index survey; `n=0` is the `d=n+1` seam | [Carrier/descent Corollary C](class-a-carrier-closure-2026-10-22.md), [small complete receipts](../evidence/class-a-run-index-2026-10-21/survey.log) |
| `d=2` | Every canonical swap-seed vertex; residue floors `(14,13)` and all admissible smaller members, including `n=0` in the later full replay | [Plus gap-two theorem](class-a-d2-plus-rays-2026-10-22.md), [25-ray replay](../evidence/class-a-gap-independent-audit-2026-10-23/residue-rays.log) |
| `d=3` | Every canonical swap-seed vertex; residue floors `(18,16,17)` and all admissible smaller members, including `n=0` in the later full replay | [Residue-ray Theorem R and Corollary L](class-a-residue-rays-2026-10-22.md), [25-ray replay](../evidence/class-a-gap-independent-audit-2026-10-23/residue-rays.log) |
| `d=4` | Every canonical swap-seed vertex for `n>=0`; residue floors `(24,21,22,15)` with complete lower prefixes | [Gap-four theorem](class-a-d4-rays-2026-10-23.md), [current registry](../kernel/psc/class_a_ray_tables.mojo) |
| `n>=6,5<=d<=n+4` | Every strict integral source | Sections 1–6 of this note |
| `d=n` within the PIP domain | Every canonical swap-seed vertex; tail `n>=20`, complete `n=1..19`; `n=0` is outside `d>=1` | Class-A `k=0` row of [Theorem L″](p1b-boundary-hitting-progress-2026-10-08.md), [current pins](../kernel/symbolic_line_pins.txt) |
| `d=n+1` | Every canonical swap-seed vertex; tail `n>=19`, complete `n=0..18` | Class-A `k=1` row of Theorem L″ |
| `d=n+2` | Every canonical swap-seed vertex; tail `n>=52`, complete `n=0..51` | Class-A `k=2` row of Theorem L″ |
| `d=n+3` | Every canonical swap-seed vertex; tail `n>=14`, complete `n=0..13` | Class-A `k=3` row of Theorem L″ |
| `d=n+4,n=1..5` | Every vertex in each of five complete finite S18 graphs reaches typed full integral zero; no all-strict claim is inferred | Complete certificates below |

The current four seam rows are exactly

```text
line A 2 0 1 0 1 1 20 210 19 0 1
line A 2 1 1 0 1 1 19 194 19 0 0
line A 2 2 1 0 1 1 52 230 52 0 0
line A 2 3 1 0 1 1 14 260 14 0 0
```

These are the restored October 30 fit-first pins, not the intermediate
October 26/27 thresholds. The pin values are expected verdicts, not
premises consumed by the certificate. The actual line checker proves
the symbolic tail, includes all strict original occurrence children,
requires every vertex to hit full integral zero, and checks the
complete graph for every admissible member below the tail floor.
The similarly named Class-B cone proof must not be substituted for
these Class-A rows.

The canonical
[`class_a_plus_small_certificate.mojo`](../kernel/psc/class_a_plus_small_certificate.mojo)
and its
[complete finite test](../kernel/tests/test_class_a_plus_small_entry.mojo)
now supply the five missing members. Each starts with all 18 actual
oriented swap-patch contacts, enumerates every original ordered child
of every nonterminal vertex, checks that every such child is present
in the resulting finite graph, and
requires a full-integral-zero typed target to be reachable from every
vertex. Only equal-letter full-zero states are terminal. The canonical
Cartesian occurrence-pair check and the separately written
[literal-word oracle](../oracles/python/class_a_plus_small_certificate.py)
both passed, with these exact results:

| `n,d` | Complete vertices | Original ordered edges | Cartesian pairs checked | Maximum shortest typed depth | Selected path edges over all vertices |
| --- | ---: | ---: | ---: | ---: | ---: |
| `1,5` | 306 | 1,466 | 9,084 | 4 | 764 |
| `2,6` | 288 | 1,744 | 13,396 | 4 | 680 |
| `3,7` | 280 | 2,008 | 18,366 | 4 | 642 |
| `4,8` | 278 | 2,338 | 24,828 | 4 | 636 |
| `5,9` | 276 | 2,676 | 32,134 | 4 | 630 |
| Total | 1,428 | 10,232 | 97,808 | 4 | 3,352 |

All 1,428 vertex paths retain the actual original prefixes and satisfy
`M^m w=P-Q` under independent replay. The enumeration uses a
6,000-state cap and a 20,000,000-pair cap; exhaustion refuses without
a hitting verdict. Twelve canonical refusal controls are recorded.
These five finite graphs cover their entire stated finite domains;
their maximum depth four is not extrapolated to other parameters or
to arbitrary strict sources.

These are complete graphs stopped at typed coincidence: terminal rows
are empty, so the edge and Cartesian-pair totals concern nonterminal
rows. Any strict descendant of a typed coincidence is again a typed
coincidence, because the two identical literal subdivisions have the
same boundaries and only matching intervals overlap strictly. Thus
continuing beyond the stopped vertices adds only typed-zero states;
it cannot introduce an unverified noncoincident descendant.

The resulting parameter partition is exhaustive. At `n=0`,
`d=n+4` is already the low-gap member `d=4`. For `1<=n<=5`,
every other point with `d>=5,d<=n+4` lies on one of the four
authenticated seams. For `n>=6`, every point with `5<=d<=n+4`
is in the all-source theorem. Together with the low gaps this proves
**complete mathematical boundary-hitting coverage for the canonical
plus-Class-A swap-seed domain `n>=0,1<=d<=n+4`**. An inherited
single-orientation swap graph supplies its opposite orientation by
actual track reversal. The all-strict quantifier is asserted only
for the new `n>=6,5<=d<=n+4` chamber, not for inherited low gaps,
seams or the five finite exceptions.

The earlier [high-gap theorem](class-a-gap-theorem-2026-10-23.md)
already proves seed-domain hitting for `d>=5,n>=5d`. That region is
inside the present new all-source chamber. Seven existing plus
exceptional residue rays also have their complete lower-prefix
certificates in the 25-ray replay. They need not be recomputed to
prove the present chamber. Their individual small upper-chamber
members, like the gap-five finite pilot, do not give a uniform result
on the remaining strip `n+5<=d<=2n+11`.

Inherited receipts retain their original source and acceptance
scope. The [gap-four integration](issue139-ac-integration-2026-10-23.md)
preserves standard and alternative rank tables separately; their
different floors and occurrences are not interchangeable rows. The
[independent high-gap audit](class-a-gap-independent-audit-2026-10-23.md)
corrected generic box-arithmetic overflow and supplies the 25-ray
replay used above. Several shared sources changed after older
packets. A historical receipt is not a fresh run at the new PR head.
Mathematical assembly, source comparison, exact replay, hosted
acceptance and independent human review remain distinct records.

## 8. Verification and formal boundaries

The unbounded mathematical steps are the density deficit with its
finite boundary errors, legality of the nearest selector for every
central source, the bounded periodic-tail classification, and the
three genuine RUN edges at every admissible height. A finite path
sample supplies none of those missing quantifiers by itself.

The canonical implementation must bind the plus literal ordered
words, exact cubic/Perron field, positive eigenlengths and every
cached original prefix before applying the formulas. It must refuse
foreign or minus fields, rearranged words, illegal RUN positions,
out-of-domain or nonintegral inputs, altered full targets, and
exhausted step/state/pair or checked-arithmetic budgets. A capped
search gives no mathematical verdict. A nonzero fixed nearest
packet must not be credited as a successful zero endpoint.

Independent replay must count the prefixes from the actual words,
check every strict edge and all integral coordinates, compose the
original depth-prefix equality, and distinguish first integral-zero
BH from first typed-coincidence stopping. Negative heights must
reverse the actual occurrence order, not just the offset label.

Formal verification of an abstract recurrence or the three-edge
suffix does not by itself formalize Perron identification, the
one-level count argument, all-source literal ancestry or the full
family assembly. Exact endpoint types and their audited axioms
must be reported at the producing source. The fresh-source Lean
policy remains unchanged; cached development evidence, fresh
isolated acceptance and hosted exact-head gates must not be
interchanged.

### 8.1 The compiled formal subset

[`ClassAPlusConstantRecurrence.lean`](../proof/PscVerif/PscVerif/ClassAPlusConstantRecurrence.lean)
contains the signed recurrence and the literal occurrence suffix.
Its separate
[`ClassAPlusConstantRecurrenceAudit.lean`](../proof/PscVerif/ClassAPlusConstantRecurrenceAudit.lean)
checks these seven exact endpoint types:

| Endpoint | Formal conclusion |
| --- | --- |
| `forward_integer_bound` | Every forward strict recurrence with `0<=A<1/2`, `B>0`, `A+B<1` is bounded in the integers. |
| `bounded_two_sided_classification` | Every bounded two-sided recurrence is a signed constant, with its exact amplitude inequality. |
| `periodic_cycle_classification` | A recurrence with a supplied positive period is constant. |
| `eventual_constant_tail` | A forward recurrence has a constant tail; boundedness and positive eventual period are derived, not supplied as premises. |
| `constant_nearest_iff` | A signed constant `H` is a nearest fixed point exactly when `|(1+A-B)H|<1/2`. |
| `three_run_decrement` | The three displayed original RUN occurrence pairs give the full integral intermediate states and lower the positive height. |
| `constant_composable_path` | Every signed height with `d>=5` and `2d|H|<=n+2` has a strict composable path to typed zero, under explicit positive lengths, positive scale and literal substitution scaling. |

The final endpoint derives source strictness backwards from the common
final interval. It takes neither a supplied source-interior premise
nor a supplied hitting path. The literal packet constructor negates
`(p,q,r)` to bind this note's bottom-minus-top convention to Lean's
top-minus-bottom displacement; the original indices themselves are
unchanged.

The cached development compile and audit completed successfully on
November 14 at 19:12 EST. They checked 68 owned declarations, including
63 theorem declarations, all seven exact endpoints and 21 rejection
controls. Transitive axiom checking admitted only `propext`,
`Classical.choice` and `Quot.sound`. Source hashes were unchanged
across the run. This is cached development evidence, not fresh-source
acceptance or a full-library audit.

The family cubic/Perron identification, strict half-tie exclusion,
specialization of the recurrence to every actual central source,
one-level density entry, and arbitrary-source original-prefix
assembly remain written proofs here. Compilation of the abstract
recurrence and the literal constant suffix does not formalize those
interfaces.

### 8.2 Canonical and independent occurrence replay

The [canonical central constructor](../kernel/psc/class_a_plus_constant_entry.mojo)
checks literal words, field, eigenlengths, complete prefix caches,
original RUN ordinals and every full integral edge. The
[actual-entry constructor](../kernel/psc/class_a_plus_entry_search.mojo)
retains original indexed ancestry and has distinct first-integral-zero
and first-typed-coincidence policies. The
[independent oracle](../oracles/python/class_a_plus_constant_entry.py)
counts actual word prefixes and replays the entire original transcript,
including the full depth-prefix equality.

The [source-scoped evidence packet](../evidence/class-a-plus-constant-entry-2026-11-14/README.md)
records the following passing canonical paths and full independent
original-prefix replays:

| Path scope | Paths | Actual checked path edges | Maximum returned depth |
| --- | ---: | ---: | ---: |
| Central nearest paths and signed constant exits, 25 members | 1,007: 875 central plus 132 constant | 8,214 | 37 |
| Arbitrary-source entry, first integral-zero stopping, the same 25 members | 475 | 1,162 | 5 |
| Aligned mixed-letter typed continuations, the same 25 members | 150 | 410 | 4 |
| Every vertex of the five complete small S18 graphs | 1,428 | 3,352 | 4 |
| Total | 3,060 | 13,138 | 37 |

The first three rows together are 1,632 paths and 9,786 edges. Their
independent replay completed on November 14 at 19:17:57 EST, with
exit zero and unchanged source hashes. It also checked 300 exact
one-level density comparisons on the 25 members. The complete
small-graph replay separately checks all 10,232 original graph edges
and all 97,808 Cartesian occurrence pairs, in addition to the 3,352
selected path edges counted in the table. These are finite validation
counts, not the quantifier source of the written infinite theorem.

The [symbolic oracle](../oracles/python/class_a_plus_constant_symbolic.py)
independently checks the two exhaustive positive-height cases `H=1`
and `H>=2`, each in both track orientations: four symbolic paths,
12 full integral edges and 24 genuine RUN occurrences, with composed
original-prefix identities. It also checks the root, eigenlength,
density and signed recurrence identities, with eight mutation
controls. The symbolic parameter inequalities cover `d=5,...,9`
with `n=6+v`, and `d=10+u,n=6+u+v`, where `u,v>=0`; these six
chambers exhaust `n>=6,5<=d<=n+4`.

The cached formal audit remains the scoped acceptance described
in Section 8.1. The local plus source-isolated gate has not been
run in this packet, so fresh-source plus acceptance remains pending.
No failed plus gate is inferred from the earlier minus gate's
historical upstream-cache refusal. Dedicated and full-library hosted
workflows require their own actual producing-head receipts;
neither cached artifacts nor parent receipts supply those outcomes.
Independent human review remains pending.

The [source/hypothesis gate](bh-class-a-plus-constant-stop-go-2026-11-14.md)
records the literature boundaries. A rounded contraction's periodicity
does not prove zero hitting; original prefix occurrence choices
remain necessary. The determinant-two argument introduces no
unit-only spectral implication. Universal BH, arbitrary-ternary
A1-prime, C4, G1, PDS, PSC and the all-alphabet extension receive no
promotion from this scoped family theorem.
