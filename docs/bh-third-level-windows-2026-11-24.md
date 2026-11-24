# Three-window entry on the original occurrence tracks

**Status.** Written deterministic construction and exact literal
replay. The Lean work is recorded at its separate verification scope.
[Source review](bh-third-level-and-diagonal-stop-go-2026-11-24.md)

Use the lengths \((1,\beta,1+r/\beta)\) for \((1,01^k2,0^r1)\).
The proof only uses \(\beta>12\), \(r<\beta\), the positive
length-scaling identity on the three literal images, and \(k>0\).
It applies to both off-diagonal bands in the earlier proof and
also to \(k=r\), \(r\ge12\). The contraction or descent after entry
is a separate argument.

## Choose a window using the actual parent blocks

Start with a packet whose strict shared interval has width at
least \(1/2\). The general half-width lemma supplies such a packet
from any strict source. At the third level let the top image have
left end zero and the bottom image have left end \(S\), the
inflated bottom-minus-top shift. Let \(L=\max(0,S)\). Both
third-level image words cover \([L,L+18\beta]\), with room
at the right, since the shared width is at least
\(\beta^3/2>18\beta\).

Consider the three windows
\[
  [L+7i\beta,\ L+(7i+4)\beta],\qquad i=0,1,2.
\]
The only long obstructions to finding nearby marks of type \(1\)
come from whole third-level parent blocks of type \(2\).
Each such block has length \(\beta(1+r/\beta)<2\beta\).

The starts of distinct such blocks in either track differ by at
least \(\beta^3\). A type \(2\) in the second-level word must
be the final letter of the image of an original type \(1\)
in the first-level word. The literal prefix at that final
position is always \(01^k\). Distinct second-level marks of
type \(2\) have distinct first-level parent positions. The
first-level starts of those parents differ by at least the
length \(\beta\) of a type \(1\). Inflation to the second level
multiplies that separation by \(\beta\). The equal proper
prefix lengths cancel. One more inflation gives the claimed
third-level spacing. This derivation also applies to
twice-substituting a longer literal word.

Use a conservative obstruction interval of length \(2\beta\)
at each of those starts. Any start whose obstruction meets the
interior of a window lies between \(L-2\beta\) and \(L+18\beta\).
That range is shorter than \(\beta^3\), so each track has at
most one relevant obstruction interval. Such an interval
cannot meet two windows because their gap is \(3\beta\).
Thus at most two slots are excluded by the two tracks, and
one of the three windows is clean on both.

## Select two original unit marks

Let \(a\) be the left end of the chosen window.
For a point \(x\) in this window with \(x+3\) still in the
window, there is a type \(1\) mark with start \(c\le x+3\)
and \(x\le c+\beta\) in either track.

To prove this, inspect the original third-level parent block
containing \(x\) in the half-open convention. The parent is
not \(2\) because its entire type-2 block would intersect the
clean window. In the image of \(0\) the point is already in
a type \(1\). In the image of \(1\) it lies either in the long
run, in its first short \(0\), or in its final short \(2\).
In the first short tile the next \(1\) starts within one unit.
In the last short tile, the next parent exists because there
is room for \(x+3\) inside the word. It begins less than
two units to the right of \(x\), so it must also be \(0\) or
\(1\). Its first type \(1\) starts no more than one further
unit to the right. Endpoints are allowed in this locator
bound. The final overlap has positive width.

Apply the locator to the top at \(x=a+3\beta/2\). This puts
its selected mark at some \(c\) with \(c\ge a+\beta/2\)
and \(c\le a+3\beta/2+3\). The midpoint \(c+\beta/2\) and
that midpoint plus \(3\) lie in the window. Apply the locator
on the bottom at that midpoint. Its mark starts at \(d\)
with \(c+\beta/2-\beta\le d\le c+\beta/2+3\). Hence the
common interval of the two type-1 marks has width at least
\(\beta/2-3>\beta/4\).

Both marks are selected by positions in the actual words.
Reading their three original image ordinals back through
the two substitution partitions gives the literal path.
An interior point of the terminal overlap remains strictly
inside both scaled ancestors, so every previous step is
strict. Their full displacement is the original incidence
image plus the actual two prefix columns. In particular the
two marks meet inside the run window with physical offset
of absolute value at most \(3\beta/4\). This is less than
\(k-1\) in all three bands considered here.

The earlier quadratic descent completes the two off-diagonal
cases. The diagonal proof uses the small-coordinate exit and
the outer energy reduction in its own scope. The remaining
diagonal region has energy at most the stated outer threshold
and lies outside the small-coordinate exit.

## Exact checks and formal boundary

The native replay checks all nine parameter pairs with
\(r\in\{12,16,20\}\) and \(k-r\in\{0,1,2\}\).
It locates and replays the two original digit triples for 6,069
strict packets of half-width or more. Three extra cases at
interior anchors force the selector to use the third window.
Endpoint-only contact and forged digit positions are refused.

The pinned Lean compiler checked `Psc.BHWindowChoice.exists_clean_slot`,
the finite two-track selection, with only the standard axioms.
The full dependency load for the
literal spacing, locator and ordered assembly stalled. The remaining
source drafts are outside the checked patch. The prior two-band
central descent keeps its compiled scope.

Run the exact replay with the pinned native compiler.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_bh_third_level_windows.mojo)
```
