# Literal return paths in the diagonal determinant band

**Status.** Written sufficient region and a reduction of the remaining
diagonal band. The exact replay checks the stated literal choices.
[Source review](bh-third-level-and-diagonal-stop-go-2026-11-24.md)

Let \(r=k\ge12\) and \(\sigma=(1,01^r2,0^r1)\). Use the root
\(\beta\in(r,r+1)\) and put
\[
 A=\beta-r,\quad B=r/\beta,\quad d=1-B=A/\beta,\quad
 \theta=(r-1)/\beta,\quad R=\lfloor (r-2)/3\rfloor .
\]
The tile lengths are \((1,\beta,1+B)\). The identities
\(\beta A=2+B\) and \(B>12/13>2/3\) follow from the defining cubic
and interval. They also give
\(A<1/4\), \(1-\theta=(1+A)/\beta<A\), and \(1/2<\theta<1\).

For a packet \(p=(1,1;x,y,z)\) write \(D=x+\beta y+(1+B)z\).
Call the condition \(|D|\le r-1\) the run window. A packet in the
window with \(\max(|z|,|y|)\le R\) has a literal path to equal-letter
zero. This is an unbounded parameter statement with a coordinate
hypothesis on the source.

## Literal rounding

Let \(w=Ay+Bz\). Setting the next second coordinate to \(t\) uses
a difference \(h=t-(x+ry+z)=t+w-D\) of run ordinals. If
\(|t+w|\le\theta\) and the source is in the window, then
\(|h|<r\). The ordinals \(\max(h,0)\) and \(\max(-h,0)\) inside
the two runs give the actual child
\[
 (1,1;y+rz,t,y),\qquad D_{\rm child}=\beta(t+w).
\]
The original image ordinals are one greater. Thus the child is strict
and inside the window. The same affine child formula also applies
outside that window whenever the two displayed run ordinals are
in range and the resulting overlap is strict.

For \(\max(|z|,|y|)\le R\), one can always take \(t=-z\).
Its error is \(e=A(y-z/\beta)\), with
\[
 \beta|e|\le(2+B)R(1+1/\beta)
 \le (r-2)(1+1/\beta)<r-1 .
\]
It rotates the pair \((z,y)\) to \((y,-z)\) without changing the
absolute coordinates. If \(z,y\) have opposite nonzero signs, then
\(e\) has sign opposite to \(z\) and \(|e|\ge A>1-\theta\).
Taking \(t=-z+\operatorname{sgn}(z)\) is therefore admissible
and reduces \(|z|+|y|\) by one. If their signs agree, rotate once
before applying this decrease.

On an axis with \(|z|+|y|=m\ge1\), first rotate to \((0,-m)\)
in at most three steps. Taking \(t=1\) is admissible since
\(A m\le\theta\) and \(A m>1-\theta\). This gives
\((-m,1)\). If \(m\ge2\), the opposite-sign choice gives
\((1,m-1)\), a rotation gives \((m-1,-1)\), and another
opposite-sign choice decreases the sum to \(m-1\). The maximum
absolute coordinate stays at most \(R\) throughout.

For \(m=1\) the injection \(t=1\) gives the full packet
\((1,1;-1,1,-1)\). The opposite-sign choice yields
\((1,1;1-r,0,1)\). Choose \(t=0\) once more. Its run difference
is \(r-2\), so it is a literal run child, and the new full packet
is \((1,1;r,0,0)\). It is strict since \(r<\beta\).
On the next edge choose the first run \(1\) on top and final \(2\)
on bottom, at original indices \((1,r+1)\). The prefix correction
\((0,-r,0)\) cancels the incidence image \((0,r,0)\).
This gives \(1/2\) at integral zero. The two original first
letters, both \(0\), give labelled zero. Finally, if the last
two initial coordinates are both zero, \(t=0\) already clears
the first coordinate inside the window.

The decreasing integer sum and the literal unit-axis exit prove
the stated sufficient region. If the initial sum is \(m\), the
argument gives a path of length at most \(7m+8\).

## Reduction of the full diagonal problem

The third-level geometry supplies \(1/1\) with \(|D|\le3\beta/4<r-1\)
from any strict source, including this diagonal band. It therefore
enters the same run window.

For \(E=Q(z,y)=Bz^2+Azy+y^2\), put
\(\eta=(1-\theta)/(1-\sqrt B)\).
Any window packet with \(\sqrt E>\eta\) admits a literal next
window packet of strictly smaller energy. To see this, truncate toward
zero for \(w\) and take its negative as \(t\). The corresponding
\(t\) lies between \(0\) and \(-w\).
The exact unrounded value gives \(Q(y,-w)=BE\), and
\[
 E-Q(y,0)
 =B\left(z+\frac{A}{2B}y\right)^2+
 \left(d-\frac{A^2}{4B}\right)y^2>0 .
\]
Here \(A^2/d=2+B<4B\). Convexity therefore gives strict descent
when the truncation is in range. Otherwise the other integer has
error \(|t+w|<1-\theta\). Using
\((Ay+2Bz)^2\le4BE\) gives
\[
 Q(y,t)\le(\sqrt{BE}+|t+w|)^2<E .
\]
Both choices are realized by literal run indices. Each energy
sublevel on the integer pair is finite since \(Q\) is positive
definite. Iteration therefore reaches energy at most \(\eta^2\).

The threshold also limits the residual pair to \(z^2+y^2<r^2\).
In fact \(B\ge48/49>39/40\) because \(A<1/4\) and \(r\ge12\).
Thus
\[
 \frac{\eta}{r}=\frac{(1+A)(1+\sqrt B)}{(2+B)B}
 <\frac{4000}{4641}<\frac9{10},\qquad
 Q(z,y)\ge (B-A/2)(z^2+y^2)>\tfrac{81}{100}(z^2+y^2)
\]
for a nonzero pair. The exact native outer calibration uses the
simpler stopping bound \(Q\le r^2\).

It remains to give a uniform exit from the run-window packets with
\[
 Q(z,y)\le\eta^2,\qquad
 \max(|z|,|y|)>\lfloor(r-2)/3\rfloor .
\]
The first coordinate is still the full integral coordinate of each
packet. No partition of these residual packets by rounded values
alone is asserted.

## A nearest-rounding refusal control

At the packets \((1,1;z-ry,y,z)\) with
\((z,y)=(1,0),(0,-1),(-1,0),(0,1)\), the error of \(t=-z\)
is less than \(1/2\). This unique nearest choice therefore follows
the quarter turns. The identity \(x'=z'-ry'\) is preserved, so
this is a closed four-step walk of full integral nonzero packets,
with actual strict children at every step. The selectable rounding
above gives a literal exit from this walk. This calibrates the
difference between a failed deterministic policy and a failed
coincidence theorem.

## Replay

At each \(r\in\{12,13,16,20,32\}\), the checker visits every
integer pair in the stated box. For each pair it tests the
central first coordinate \(z-ry\) and both extreme first
coordinates allowed by the run window. It replays all the
ordered choices, keeps the exact labelled endpoint, checks the
full four-step nonzero cycle, and separately tests descent
outside \(Q\le r^2\). The sufficient-region check covers 2,367
source packets. The longest chosen return path has 51 edges.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_bh_diagonal_run_reduction.mojo)
```
