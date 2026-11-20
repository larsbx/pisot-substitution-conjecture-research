# A two-parameter family excluded by bilateral newborn seams

**Status:** repository-proved family exclusion and conditional seam criterion; independent human review pending.

Continuation of [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
See the [pre-code source review](c4-phase-one-newborn-stop-go-2026-11-14.md).
The initial phase-one check extends the earlier
[local seam argument](c4-seam-birth-orbits-2026-11-04.md).
The family proof below excludes every finite strict component, including
those with mixed child orientations.

## Necessary newborn seams

Suppose a finite nonempty set of irreducible noncoincident balanced
pairs is fully child-closed under a nonerasing primitive ternary substitution
with nonsingular incidence $M$ and expanding Perron scale. Pass to a
closed strongly connected component modulo swapping tracks. Its
words on each track are legal, by
[whole-factor enclosure](c4-overlap-carrier-enclosure-2026-11-04.md):
each state occurs inside a single-letter inflated tile on each track
after following a child path from an enclosed factor. Its complete
one-step rows consequently have legal bigrams on both sides of
every seam. The legal bigram set is the closure of the internal
image bigrams under $(a,b)\mapsto (\operatorname{last}\sigma(a),
\operatorname{first}\sigma(b))$.

Use a witnessed left good edge and an independently witnessed right
good edge. Their complementary letters occur exactly once in every
ordered first and terminal pair, respectively. To see this, any
represented occurrence of the good edge would inflate to a literal
diagonal, while equal endpoint letters already produce a diagonal.
The same restriction holds through every iterate of the two endpoint
maps.

There must be a one-step newborn seam in some state's full row.
Otherwise each state would have exactly one child and physical
length would grow indefinitely through states of bounded length.
Every interior cut of an irreducible parent's image is newborn.
At a newborn, record the source letters $a,b$ of the two tiles
just to its right and their proper image-prefix digit addresses
$i,j$. If $i=j=0$, the equality of the inflated prefix Parikh
vectors gives equality of the original prefix Parikh vectors by
nonsingularity. The cut would have been inherited. Thus at least
one address is internal. The two local prefix columns $p,q$
must satisfy $p-q\in M\mathbb Z^3$, since their difference is
cancelled by the inflated original prefix difference.

If $p=q$, the two source letters must be an admissible parent
first pair. The reasoning is the same equality at ancestral
prefixes and the source positions must both be first. If the two
remaining image suffixes from the addressed positions have the
same Parikh column, both source positions must be last, by applying
the argument to the suffixes after their parent tiles. They must
then be an admissible parent terminal pair. The checker with no
phase hypothesis allows both parent orders in these tests. The
phase-one version requires the opposite parental hub sides from
the child seam. The common relative orientation of the two hubs
within a phase-one carrier follows from the
[period theorem](c4-strict-component-period-2026-11-14.md).

Accordingly, an empty candidate set for both orders of the terminal
hub rules out a strict component. A successful local candidate
certifies only the simultaneous local word and arithmetic
conditions. It can lack a compatible whole parent state.

## The unbounded family

**Theorem (two-parameter newborn exclusion).** Among
$$
\sigma_{k,r}=(1,\;0 1^k2,\;0^r1), \qquad r\ge 2,\quad k\ge 1,
$$
the primitive irreducible Pisot members are exactly those with $k\ge r$
and the exceptional member $(k,r)=(1,2)$. None admits a nonempty finite
fully strict child-closed balanced-pair system.

The incidence matrix and characteristic polynomial are
$$
M=\begin{pmatrix}0&1&r\\ 1&k&1\\ 0&1&0\end{pmatrix},
\qquad f(X)=X^3-kX^2-2X-r.
$$
Here $M^2$ is positive and $\det M=r$. There is exactly one positive
root $\beta$, because its equation $x=k+2/x+r/x^2$ has an increasing
left side and a strictly decreasing right side. For $k\ge r$,
$f(k)=-2k-r<0$ and $f(k+1)=k^2-1-r>0$, so $\beta$ lies strictly
between consecutive integers. For the exception $(1,2)$, the
corresponding signs are $f(2)=-2$ and $f(3)=10$. There is no nonpositive
real root, since for $t\ge0$,
$$
f(-t)=-t^3-kt^2+2t-r\le 1/k-r<0.
$$
Thus there are no integer roots and hence no rational roots. The
two remaining roots are complex conjugates of squared modulus $r/\beta<1$.
If $r\ge3$ and $k<r$, then $f$r$=r[r(r-k)-3]\ge0$, so $\beta\le r$.
The other two roots have modulus product $r/\beta\ge1$ and cannot both
be strictly contracting. This accounts for every $r\ge2,\ k\ge1$.

### Two genuinely witnessed good edges

On the left the pair $\{1,2\}$ is good at depth one, with common first
letter 0. The left hub is 0. For the right edge use word reversal
$\tau=(1,\;2 1^k0,\;1 0^r)$ and set $A=1$, $B=2 1^k0$, $C=1 0^r$.
Define the third-level words $U=\tau^3(0)=CB^kA$ and
$V=\tau^3(1)=BA^rU^kB$.

- If $k>r$, the prefixes $CB2 1^r$ of $U$ and $BA^rC2$ of $V$ have
  mass $(r+1,k+r+1,2)$ at cut $k+2r+4$. Both are followed by 1, since
  $k>r$ on the first track and the second track is at the start of the
  first $B$ inside $U$.
- If $k=r$, then $\tau^4(0)=V$ and $\tau^4(1)=UB^rV^kU$. Their
  respective prefixes $BA^kCB^{k-1}2$ and $CB^kA2 1^{k-1}$ are
  followed by 1. Both have mass $(2k,k^2+k+1,k+1)$ at cut
  $k^2+4k+2$.
- For $(k,r)=(1,2)$ the depth-five prefixes at cut 20 are
  10021012102102101110 and 21011100210121010021. Both have mass
  $(7,9,4)$ and are followed by 0.

Thus the right good edge is $\{0,1\}$ and its hub is 2. The pair
$\{0,2\}$ is also right good, since both images end in 1. Every
represented terminal pair must therefore be $\{1,2\}$. The only
possible first pairs are $\{0,1\}$ and $\{0,2\}$.

### All possible newborns fail

For all these parameters the two legal track bigrams must come
from the exact set $\{00,01,10,11,12,20,21\}$. Its internal
generators are 00, 01 and 12, with 11 also internal when $k\ge2$.
Inheritance supplies 10, 20 and 21, and also 11 when $k=1$.
The resulting set is closed. Orient a proposed seam so that its
right factor starts with 0 on top. A terminal pair and first
pair are written in top, bottom order.

| Terminal pair | First pair | Top and bottom bigrams | Obstruction |
| --- | --- | --- | --- |
| 12 | 01 | 10,21 | Both bigrams can occur only across image boundaries. |
| 12 | 02 | 10,22 | 22 is illegal. |
| 21 | 01 | 20,11 | 20 forces a top image boundary. Any internal 11 on the bottom has residue 1. |
| 21 | 02 | 20,12 | 20 forces a top image boundary. The internal 12 on the bottom has residue 1. |

Here every internal 11 or 12 lies in $0 1^k 2$, with
proper prefix $0 1^j$ for some $j\ge1$. Its Parikh column
is $(1,j,0)$. Every column of $M$ has zeroth and second
coordinates equal modulo $r$, so any vector in $M\mathbb Z^3$
has that equality. With a top image boundary the top local
prefix is zero, and the bottom internal prefix violates the
residue condition. A bottom image boundary instead would make
both local digits zero. This accounts for all ordered seams,
irrespective of the parent orientations. Hence there is no
possible newborn, contradicting finite strict closure.

## Verification and remaining scope

The canonical Mojo checker reuses the phase-zero seam construction.
The phase-one path checks the prior hub side when checking equal
local prefixes and suffixes. The phase-unrestricted path allows both
orders of every admissible parent pair. Both paths compute complete
legal bigrams and test exact lattice membership with Cramer's rule.
The independent Python replay uses rational row elimination. The
checks exercise 78 members of the family, including the exact
left and right witnesses, and enforce the 64-letter implementation
budget. The written family proof has no word-length cap.

The reducible, nonsingular source $\sigma=(1,012,101)$ has a real
three-state complete strict component with both hubs equal to 1,
on opposite tracks after orienting the first hub. Both genuine
complementary witnesses occur at depth one. The checker retains
all four actual newborn seams in the component rows.
The Pisot control $\sigma=(1,012,21)$ has characteristic polynomial
$x^3-2x^2-x+1$ with roots in $(-1,0)$, $(0,1)$ and $(2,3)$. It has a surviving phase-one
local candidate and its 01/10 seed has a diagonal at depth
three. This calibrates the difference between local admissibility
and literal closure.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_phase_one_seams.mojo)
python -m pytest tests/test_c4_phase_one_seams_oracle.py
python tools/make_proof_bank.py --check
```

The theorem excludes finite strict systems for the whole family.
It yields no bound on arbitrary descendant factor sets.
The prior $r=2$ seed termination and spectral work uses its own
finite carrier. The next question for new $r>2$ members is whether
such a carrier or a uniform common-boundary estimate can be proved.
General C4, G1, BH, A1′ and PSC remain open.
