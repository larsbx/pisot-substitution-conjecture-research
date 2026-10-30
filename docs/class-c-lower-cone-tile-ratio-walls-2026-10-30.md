# Class C lower cone: exact Perron tile-ratio chambers (2026-10-30)

**Status:** repository-derived, hand-proved exact algebraic inequalities at the stated scoped PIP domain; independent human review pending. No boundary hitting (BH), pure discrete spectrum, G1, or general PSC conclusion is deduced here.

This is a new geometric refinement of the exact Perron-root walls in
[class-c-lower-cone-root-walls-2026-10-30.md](class-c-lower-cone-root-walls-2026-10-30.md)
(PR #403). It uses Theorem P_C's proved exact Pisot-domain characterization
(PR #397). No part of the symbolic cone engine is assumed in this result.

## Work shown

### Assumptions and hypotheses

For integer \(d\ge7\), \(\varepsilon\in\{+1,-1\}\), let

    p=n+d,  r=n-d+eps,
    sigma(x)=x y^p x, sigma(c)=c y^n x, sigma(y)=c y^r c.

Restrict to the *remaining* Class-C lower cone:

    plus: 2d-5 <= n < 3d;
    minus: 2d+1 <= n < 3d.

Put \(c=n-(2d-5)\) for plus, \(c=n-(2d+1)\) for minus.
Thus \(c\) is an integer, with \(0\le c\le d+4\) for plus and
\(0\le c\le d-2\) for minus. Theorem P_C independently establishes
primitivity, irreducibility and Pisot throughout these regions. Write
\(\beta>2\) for the Perron root, with its two other conjugates inside
the open unit disc. Normalize left Perron lengths by \(\ell_y=1\);
the eigenvector equation gives

    L_x := ell_x/ell_y = p/(beta-2).

### Derivation / reduction

**Theorem R_C (exact tile-ratio chambers; repository-proved, hand proof below, independent human review pending).** Every Class-C member in the
lower cone above has the following *strict* normalized tile-ratio bound:

| sign | integer parameter chamber | proved ratio interval |
| --- | --- | --- |
| plus | \(n=2d-5\) | \(3<L_x<4\) |
| plus | \(2d-4\le n\le3d-4\) | \(2<L_x<3\) |
| plus | \(3d-3\le n<3d\) | \(1<L_x<2\) |
| minus | \(2d+1\le n<3d\) | \(2<L_x<3\) |

The transition at \(\,n=3d-3\,\) on plus is one integer line below the
previous \(\beta-(r+3)\) sign transition. These are exact chamber walls,
not numerical approximations or assertions about a constant graph.

**Proof.** The characteristic polynomial, independently derived from
the incidence matrix, is

    chi(t)=(t-r)(t-1)(t-2)-2*n*(t-2)-2*p.

Let \(m\in\{1,2,3,4\}\) and \(T_m=2+p/m>2\). Because the two
non-Perron roots lie in the open unit disc, their quadratic factor is
strictly positive at \(T_m\). Thus

    sign chi(T_m)=sign(T_m-beta),
    L_x<m iff chi(T_m)<0,
    L_x>m iff chi(T_m)>0.

No rational-root equality is possible because \(\chi\) is irreducible,
although the strict evaluations below already exclude equality.

A direct *integer polynomial* computation, with no division in its
certificate, gives the following identities:

    m^3 * chi(2+p/m) = p * G1                  (m=1),
    m^3 * chi(2+p/m) = -p * F_m                (m=2,3,4).

On plus (\(n=2d-5+c\)):

    G1 = (2d-1)c + 6d^2-9d+4
    F2 = c^2+2cd-2c-3d^2-2d-3
    F3 = 2c^2+6cd+c-3d-10
    F4 = 3c^2+10cd+10c+3d^2+6d-13.

For \(d\ge7,c\ge0\), both \(G1>0\) and \(F4>0\). The polynomial
\(F3\) strictly increases in integer \(c\):
\(F3(0)=-3d-10<0\), \(F3(1)=3d-7>0\).
Similarly \(F2\) increases and

    F2(d+1)=-4<0,       F2(d+2)=4d-3>0.

Consequently, at \(c=0\) the signs give \(3<L_x<4\);
at \(1\le c\le d+1\) they give \(2<L_x<3\);
at \(d+2\le c\le d+4\) they give \(1<L_x<2\).
The latter split translates into the displayed \(n\)-intervals.

On minus (\(n=2d+1+c\)):

    G1 = (2d+1)c + 6d^2+9d+2
    F2 = c^2+2cd+6c-3d^2-2d+9
    F3 = 2c^2+6cd+19c+15d+44.

Here \(G1>0\), \(F3>0\). The polynomial \(F2\) increases in
integer \(c\), but at the greatest allowed \(c=d-2\) it is
\(1-4d<0\). Therefore \(F2<0\) throughout the minus lower cone.
These signs give \(2<L_x<3\), as claimed. QED.

**Exact second-length consequence (no additional assumptions).**
The same left eigenvector equations give

    ell_c=(beta-r)/2,
    ell_x-ell_c=d/(beta-1)>0.

Thus the *three* normalized physical tile lengths are strictly ordered
\(\ell_x>\ell_c>\ell_y=1\) throughout the lower cone. Combining the exact
root intervals of PR #403 with the current x-ratio chamber theorem yields

| sign | c region | exact c-tile interval |
|---|---|---|
| plus | \(c=0\) | \(2<\ell_c<5/2\) |
| plus | \(1\le c\le d\) | \(3/2<\ell_c<2\) |
| plus | \(d+1\le c\le d+4\) | \(1<\ell_c<3/2\) |
| minus | \(0\le c\le d-2\) | \(3/2<\ell_c<2\) |

This exact length ordering supplies additional guards for run-window
and carrier-type analyses. It is not itself a reachability statement.

**Exact adjacent-tile gap threshold.** Write
\(\Delta=\ell_x-\ell_c=d/(\beta-1)>0\). Since
\(\operatorname{sign}\chi(d+1)=\operatorname{sign}(d+1-\beta)\),
direct integral substitution gives

    chi(d+1) = -d*((d+1)*c-d-3)            (plus)
    chi(d+1) = -d*((d+1)*c+3*d+5)          (minus).

On plus, the first expression is positive for \(c=0,1\)
and negative for every integer \(c\ge2\), \(d\ge7\).
On minus it is always negative. The previous root walls also give
\(\beta>d\) on plus \(c=0,1\); hence \(\Delta<2\) there.
Consequently the exact, sharp integer gap partition is

| region | normalized x/c tile-start gap |
|---|---|
| plus \(n=2d-5\) or \(n=2d-4\) | \(1<\Delta<2\) |
| plus \(2d-3\le n<3d\) | \(0<\Delta<1\) |
| minus \(2d+1\le n<3d\) | \(0<\Delta<1\) |

This is an additional *algebraic* wall distinct from the \(\ell_x\)
integer chambers. It changes the exact integer-aligned y-run index
windows in a prospective overlap carrier and should not be hidden
inside a uniform approximate tile-length estimate.

**Complete swap-seed geometry, independent of the closure.**
The proven strict order \(\ell_x>\ell_c>\ell_y=1\) implies that for
each ordered alphabet pair \(a<b\) in \(x,c,y\), exactly the following
three *states with interior overlap* arise from the two-letter swap
superposition \((ab,ba)\):

    (a,b,0),   (a,a,ell_b),   (b,a,ell_b-ell_a).

Indeed, the fourth occurrence pair is \((b,b,-\ell_a)\); it
cannot overlap because the bottom interval ends strictly before the
top interval starts (\(-\ell_a+\ell_b<0\)).
The other three each satisfy the strict interval test using only
\(\ell_a>\ell_b>0\).
Thus the complete initial canonical swap-seed *set* has precisely
**nine** states: three per unordered letter pair. No graph-closure
algorithm or Pisot sampling is needed for this finite seed classification.

This does *not* imply a nine-state closed graph: inflation produces
additional overlaps, whose number grows near the PIP boundary. It
provides a fixed, reproducible starting interface for a future
variable-index carrier, and forbids an argument that silently omits
one seed type.

### Evidence and replay

The *hand proof* above supplies the quantified result. The independent
standard-library Python checker
\`oracles/python/check_class_c_tile_ratio_walls.py\` directly evaluates
the original characteristic polynomial on rational arguments using
\`fractions.Fraction\` and independently compares the resulting numerator
with all seven polynomial forms. It tests integer corners and all
\((d,c)\) in its declared finite grid and refuses altered wall signs.

The separate Mojo driver
\`kernel/class_c_tile_ratio_walls.mojo\` checks the same identities
by cross-multiplying integral polynomials and verifies the strict
integer regions, without invoking \`psc.symbolic_cone\`.

From repository root:

    python3 oracles/python/check_class_c_tile_ratio_walls.py

From \`kernel/\`:

    pixi run --locked mojo run -I . class_c_tile_ratio_walls.mojo

The Class-C lower-cone root-wall workflow triggers on these files and
runs both checks before accepting the exact algebraic extension.
The Python integer identities were independently cross-checked locally.
Native Mojo / hosted CI acceptance is **not claimed until successful jobs**.

### Negative controls

The wall crossings are sharp, with *strictly opposite signs*:

- Plus \(c=0\): \(F3=-3d-10\); plus \(c=1\): \(F3=3d-7\).
- Plus \(c=d+1\): \(F2=-4\); plus \(c=d+2\): \(F2=4d-3\).
- Minus \(c=d-2\): \(F2=1-4d\), still negative; do **not**
  extrapolate the minus chamber beyond the stated lower cone.
- Any proof treating the whole plus lower cone as \(2<L_x<3\)
  contradicts the first and third chambers.

These are algebraic negative controls on *tile-ratio inequalities*,
not counterexamples to BH.

### Non-claims / remaining gaps

The ratios \(L_x\) locate exact integer threshold crossings in the
physical tile geometry and narrow the number of candidate integer run
windows for an overlap carrier. They do **not** classify complete
seed-reachable graphs, provide a certified forward-closed carrier, or
establish BH in the lower cone.

The pending \(k=n-3d=-1,-2\) ray certificates of PR #403 must be assessed
separately from these algebraic chambers. Engine soundness and
all-overlap realization remain independently reviewable obligations.
