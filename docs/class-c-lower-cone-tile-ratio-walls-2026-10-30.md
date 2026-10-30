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
