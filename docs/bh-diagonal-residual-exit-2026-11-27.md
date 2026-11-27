# Uniform selectable exit in the diagonal determinant band

**Formal continuation, 27 November:** the [complete three-band Lean assembly](bh-diagonal-closure-2026-11-27.md) now discharges the actual entry, diagonal classification, signed progress and termination obligations. The dated component scope below is retained as the record of the earlier contribution. The [spectral transfer](bh-three-band-spectral-transfer-2026-11-27.md) states the resulting family conclusion and its verification boundaries.

**Status: written proof, with separately scoped Lean components and exact replay.**
The argument below closes the residual *written* exit obligation for the
literal family `sigma=(1,0 1^r 2,0^r 1)`, `r>=12`. It does not assert that the
entire argument is already a compiled Lean theorem. The existing third-level
entry construction is also a written dependency. The exact formal and
executable acceptance boundaries are recorded in the evidence section.

The [targeted source decision](bh-diagonal-residual-stop-go-2026-11-27.md)
reviews the shift-radix, discretized-rotation and literal overlap literature.
The [24 November note](bh-diagonal-run-reduction-2026-11-24.md) supplies the
coefficient identities, literal run realization and outer energy descent used
here. Its sufficient small box is retained; the new argument exits the
residual region outside that box.

## Statement and full packet convention

Let `r>=12` be an integer and let beta be the root in `(r,r+1)` of

\[
 \beta^3-r\beta^2-2\beta-r=0.
\]

Put

\[
 A=\beta-r,\quad B=r/\beta,\quad d=1-B=A/\beta,
 \quad\theta=(r-1)/\beta,\quad\delta=1-\theta=(1+A)/\beta.
\]

The ordered integral packet is `(1,1;x,y,z)` and its geometric displacement
is

\[
 D=x+\beta y+(1+B)z.
\]

A run-window packet satisfies `|D|<=r-1`. For its last two coordinates use
the ordered pair `(z,y)`. An admissible digit `t` satisfies

\[
 |t+Ay+Bz|\le\theta.
\]

It realizes the **full** strict child

\[
 (1,1;x,y,z)\longmapsto(1,1;y+rz,t,y).                 \tag{1}
\]

Indeed, set `h=t-(x+ry+z)`. Since `h=t+Ay+Bz-D`,
`|h|<=theta+r-1<r`. The original image positions are
`(1+max(h,0),1+max(-h,0))`. Both are genuine type-1 run positions.
The next displacement is `beta*(t+Ay+Bz)`, so the next packet remains in
the run window. Thus every pair calculation below retains actual original
ordinals and the complete integral first coordinate.

**Written exit theorem.** Every run-window packet has an actual finite
literal path to equal-letter integral zero. Combined with the
[third-level entry construction](bh-third-level-windows-2026-11-24.md), this
gives a written all-source labelled exit for this literal diagonal family.
It is a family-specific statement, not universal BH or PSC.

## Coefficients and the existing outer reduction

The cubic and the interval for beta give

\[
 \beta A=2+B,\qquad A^2=d(2+B),\qquad
 Ar=B(2+B),\qquad dr=AB,
\]

and

\[
 12/13<B<1,\quad 0<A<1/4,\quad
 0<\delta<A<\theta,\quad 1/2<\theta<1.
\]

We will also use `d<1/49`, from `B>=48/49` in the earlier note. The strict
inequality follows directly from `beta=r+A<r+1/4`, hence
`B>r/(r+1/4)>=48/49`.

Define

\[
 Q(z,y)=Bz^2+Azy+y^2.
\]

The earlier outer descent says that a run-window packet with
`Q(z,y)>eta^2`, where

\[
 \eta=\frac{1-\theta}{1-\sqrt B},
\]

has an admissible one-step child of strictly smaller energy. Its written
coefficient estimate also proves

\[
 Q(z,y)\le\eta^2\quad\Longrightarrow\quad z^2+y^2<r^2. \tag{2}
\]

The remaining proof uses only the weaker disk hypothesis on the right of
(2). It supplies strict energy descent in blocks of at most three run edges,
except at the signed unit axis, which has an explicit labelled exit.
Intermediate states of a block need not satisfy the disk hypothesis; every
edge does satisfy the run window. The block endpoint has smaller energy.
When the block starts below `eta^2`, (2) therefore applies again at its end.

## Why a failed one-step descent has only two nonaxis shapes

### The toward-zero choice

Write `w=Ay+Bz`. The exact unrounded identity is

\[
 Q(y,-w)=B Q(z,y).
\]

For a nonzero pair the other endpoint also has smaller energy:

\[
 Q(z,y)-Q(y,0)
 =B\left(z+\frac{A}{2B}y\right)^2
  +\left(d-\frac{A^2}{4B}\right)y^2>0.
\]

The second coefficient is positive because
`A^2=d(2+B)` and `B>2/3`. Convexity in the new coordinate shows that every
real value between `0` and `-w` has energy strictly below `Q(z,y)`.
Consequently the integer obtained by truncating `-w` toward zero gives
strict energy descent whenever it is admissible.

The recurrence, admissibility and energy are invariant under simultaneous
negation of `(z,y,t)`. We may therefore assume `w>0`; `w=0` has the
admissible choice `t=0` and strictly decreases energy. If toward-zero
truncation is inadmissible, write

\[
 n=\lceil w\rceil=z+m\ge1,\qquad
 t=-n,\qquad
 \varepsilon=n-w=m-Ay+dz.
\]

Then

\[
 0<\varepsilon<\delta.
\]

This away-from-zero digit is admissible, since `delta<theta`. It is the only
admissible integer in this case. We now classify when its energy fails to
decrease.

### Exact integer reduction

Put

\[
 s=1/A>4,\quad K=s+1,\quad c=A+1/\beta<1/3.
\]

The coefficient identities give

\[
 r=3s-c.
\]

Let

\[
 q=3y-mr\in\mathbb Z,\qquad k=\varepsilon/d.
\]

Since `delta/d=K`, direct substitution gives

\[
 0<k<K,\qquad k=z+m+y/\beta-qs.                     \tag{3}
\]

The exact energy change is

\[
 \frac{Q(y,-z-m)-Q(z,y)}d
 =k(2z+m)-z(z+m)-y^2
 =k^2+\frac{m^2}{4}-y^2-
   \left(z+\frac m2-k\right)^2.                    \tag{4}
\]

In particular, nondecrease implies

\[
 y^2\le K^2+m^2/4.                                  \tag{5}
\]

The disk hypothesis bounds the auxiliary integer `m`. Cauchy--Schwarz and
the coefficient identities give

\[
 (Ay-dz)^2\le(A^2+d^2)(y^2+z^2)
 <(A^2+d^2)r^2=3B^2(2+B)<9.
\]

Thus `|Ay-dz|<3`. As `m=Ay-dz+epsilon` and `0<epsilon<delta<1`,
`-2<=m<=3`, in particular `|m|<=3`.
Moreover,

\[
 \varepsilon/A<\delta/A
 =\frac{1+A}{2+B}<1/2,\qquad |z|/\beta<1,
\]

so

\[
 |y|>|m|s-3/2.                                      \tag{6}
\]

If `|m|>=2`, (6) contradicts (5):

\[
 (2s-3/2)^2-((s+1)^2+9/4)
 =3s^2-8s-1>0\quad(s>4).
\]

If `m=0`, the positivity `n=z>=1` and
`y=z/beta-epsilon/A` place the integer `y` in `(-1/2,1)`, hence `y=0`.
Therefore every nonaxis failure has `m=1` or `m=-1`.

### The congruence integer must vanish

Substituting (3) into the square in (4) gives

\[
 z+m/2-k=qs-m/2-y/\beta.
\]

Since `0<k<K`, the exact energy change divided by `d` is strictly less
than

\[
 F=K^2+1/4-y^2-(qs-m/2-y/\beta)^2.                  \tag{7}
\]

Simultaneously replacing `(m,q,y)` by `(-m,-q,-y)` leaves (7) unchanged,
and leaves `3y-mr=q` unchanged in form. The signed lower bound follows directly from
`y=m*s+z/beta-epsilon/A`: for `m=1` or `m=-1`,
`m*y>s-3/2>0`, using `|z|/beta<1` and `epsilon/A<1/2`.
It therefore suffices to evaluate (7) with
`m=1`, `y=s+(q-c)/3` and `y>s-3/2>0`.

If `q>=1`, then `y>s`. Also

\[
 \frac{s+1/3}{\beta}
 =\frac1{2+B}+\frac1{3\beta}
 <\frac{13}{38}+\frac1{36}<\frac38.
\]

Consequently

\[
 v=qs-1/2-y/\beta
 =q(s-1/(3\beta))-1/2-s/\beta+c/(3\beta)
 >s-7/8>0.
\]

Equation (7) is strictly negative because

\[
 s^2+(s-7/8)^2-((s+1)^2+1/4)
 =s^2-15s/4-31/64>0\quad(s>4).
\]

If `q<=-1`, then `v<-s-1/2` and `y>s-3/2`. Again (7) is negative, since

\[
 (s-3/2)^2+(s+1/2)^2-((s+1)^2+1/4)
 =s^2-4s+5/4>0\quad(s>4).
\]

Thus (7) is negative whenever `q!=0`, contradicting nondecrease in (4).
Nondecrease forces `q=0`.

### The two remaining full integer pairs

Now `r=3N` for an integer `N>=4`, and `y=mN`. Put `C=1+B/3`, so
`1<C<4/3`. Also `s=N+c/3`.

For `m=1`, (3) gives `k=z+C`. The conditions `n=z+1>=1` and `0<k<K`
force `0<=z<=N-1` (use `c<B`). Formula (4) becomes

\[
 z^2+2Cz+C-N^2.
\]

It is increasing for `z>=0` and is strictly negative at `z=N-2`:

\[
 (2C-4)N+4-3C<0.
\]

Thus nondecrease requires `(z,y)=(N-1,N)`.

For `m=-1`, (3) gives `k=z-C`, hence `2<=z<=N+2`.
Formula (4) becomes

\[
 z^2-2Cz+C-N^2.
\]

It is increasing for `z>=2` and at `z=N+1` equals
`-(C-1)(2N+1)<0`. Thus nondecrease requires `(z,y)=(N+2,-N)`.
Restoring the initial simultaneous negation gives exactly four possible
nonaxis failures:

\[
 \pm(N-1,N),\qquad\pm(N+2,-N),\qquad r=3N.
\]

This is an all-parameter classification under the disk hypothesis. The
first-coordinate packet condition has not been discarded: (1) realizes
every selected pair step from every full packet in the run window.

## Two-edge exits from the resonant pairs

The useful identity here is

\[
 AN=1-dC,\qquad dN=AB/3<1/12.
\]

For `(N-1,N)`, choose

\[
 (N-1,N)\longmapsto(N,-N)\longmapsto(-N,1-N).
\]

The digits are `-N` and `1-N`; their errors are
`-d(N+B/3)` and `d(C-N)`, both of absolute value less than `1/2<theta`.
The total change is

\[
 Q(-N,1-N)-Q(N-1,N)=-d(2N-1)<0.
\]

For `(N+2,-N)`, choose

\[
 (N+2,-N)\longmapsto(-N,-N-1)
 \longmapsto(-N-1,N+1).
\]

The digits are `-N-1` and `N+1`; their errors are
`d(C-N-2)` and `d(N+C)-A`. Both have absolute value less than `1/2`;
for example the latter is bounded by
`dN+dC+A<1/12+4/(3*49)+1/4<1/2`.
The total change is

\[
 Q(-N-1,N+1)-Q(N+2,-N)=d(2N+3)-2-A<0.
\]

Simultaneous negation gives the other two exits: exchange the top and bottom
tracks and negate the full displacement `(x,y,z)`. No word reversal is used.

## Axis descent and the literal unit exit

The only axis left by the classification is `y=0`. By simultaneous
negation assume `z>=1`. The residual disk gives `z<r`.

If `z>=K`, then `dz>=delta` and `dz<dr=AB<1/4`. The toward-zero digit
`t=1-z` has error `1-dz<=theta`; the earlier truncation argument strictly
lowers the energy.

If `1<=z<K`, use the three-edge block

\[
 (z,0)\longmapsto(0,-z)\longmapsto(-z,1)
 \longmapsto(1,z-1).                                \tag{8}
\]

Its digits are `-z,1,z-1` and its errors are

\[
 -dz,\qquad 1-Az,\qquad A+dz-1.
\]

They are admissible: `dz<delta<theta`, `A<=Az<1+A`, `delta<A<theta`,
and `A+dz<A+delta<1`. For `z>=2`, the total energy change is

\[
 Q(1,z-1)-Q(z,0)=dz^2+Az-2z+2-d-A<0.
\]

Indeed, `dz^2<dr*z=ABz<Az`, so the right-hand side is less than
`(2A-2)z+2-d-A`, which is negative for `z>=2` and `A<1/4`.

For `z=1`, block (8) returns to the unit pair, but removes dependence on
the original first coordinate: its last full packet is
`(1,1;1-r,0,1)`. Choose `t=0` once more, with run difference `r-2`.
The new packet is `(1,1;r,0,0)`. This one edge leaves the run window but
is still strict because `r<beta`. The original image positions `(1,r+1)`
then give `(1,2;0,0,0)`, and positions `(0,0)` give `(0,0;0,0,0)`.
Thus the signed unit cases have a genuine labelled exit. Mixed type zero
is an intermediate state, not the endpoint.

Finally, if `z=y=0`, the single run choice `t=0` clears the remaining
first coordinate, by (1).

## Termination and composition with entry

The matrix of `Q` is positive definite: `B>0` and
`4B-A^2>0`. Hence every energy sublevel contains finitely many integer
pairs. Starting from any run-window packet:

1. Above `eta^2`, take the existing one-edge outer descent.
2. At or below `eta^2`, apply the nonaxis classification and two-edge
   resonant exits, or the axis block.
3. Stop at zero or a signed unit pair and use the literal endpoint above.

Every nonterminal block strictly lowers `Q`, and all its intermediate
edges remain in the run window. A strictly decreasing sequence inside a
finite set of pair energies is finite. This proves the run-window exit.
The argument is existential with an explicit finite choice rule; no
parameter-independent numerical bound on path length is asserted.

The previously written third-level construction provides a type `1/1`
packet with `|D|<=3 beta/4<r-1` from every strict source in this diagonal
family. Concatenating its original occurrences with the run-window exit
therefore supplies the stated written all-source labelled path. The full
integral displacement and actual letter labels are retained throughout.

## Evidence, controls, and formal boundary

The mathematical argument above is separate from any bounded replay.
The existing native diagonal replay retains the four-step nonzero nearest
orbit and its alternative literal exit; a fixed nearest selector still
fails. Its failure is not a counterexample to the selectable exit theorem.

The new Lean modules and native replay must be read at the scopes reported
in their own audit receipts. In particular, compiled polynomial identities,
compiled macro admissibility, a certificate-to-packet bridge, and a bounded
residual replay do not by themselves establish that the full classification
in this note or the third-level geometric entry has been formalized. Until
those complete endpoints are compiled, this all-source composition remains
a written theorem with partial formal support.

Negative controls remain: reject an out-of-run ordinal, a modified first
coordinate, endpoint-only overlap, a projected zero substituted for full
zero, and a mixed-letter zero reported as labelled coincidence. Reaching a
replay cap gives no mathematical verdict. General BH, A1-prime, C4 and PSC
are not promoted by this family result. Independent human review remains
pending.
