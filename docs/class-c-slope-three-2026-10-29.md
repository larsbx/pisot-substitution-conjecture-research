# Class C: joining the middle cone to the tail (2026-10-29)

**Historical experiment, superseded 2026-11-01.** PR #392 is closed; this
record is retained for provenance and replay. The accepted mainline T_C and
T_C2 union covers d>=6, n>=3d and replaces every use of this weaker upper
bound in #394. The original derivation and budgets below describe that
historical experiment. Its workflow is archived, not an active acceptance
gate. See [the reconciliation](class-c-below-three-integration-2026-11-01.md).

Continuation of merged #390; mathematical scope is canonical swap-seed
boundary hitting (BH), with integral offsets bottom minus top. Source audit,
exact PIP-domain lemma, target convention and implementation trust are inherited
unchanged from [the lower-strip note](class-c-lower-strip-2026-10-29.md).
The [stop/go](class-c-slope-three-stopgo-2026-10-29.md) records the unchanged
primary-source hypotheses and the new coverage target before implementation.
No PDS, G1, all-overlap realization or PSC statement is asserted.

## Target and cover

**Slope-three BH result (local certificate, hosted replay pending).** For
every integer d>=6, the canonical swap-seed graph has an offset-zero
descendant from every vertex if n>=3d+4 on plus or n>=3d+6 on minus.
The statement uses the trusted, unchanged cone engine; independent human
review remains pending. It is not a full residual-strip conclusion.

The certified interior cones use A=4 plus and A=8 minus, B=16 on both:
3d+A<=n<=4d-B. Each is exactly parametrized by nonnegative integers u,v:

    d=A+B+u+v,     n=4A+3B+4u+3v,
    u=n-3d-A,     v=4d-B-n.

The minus lower lines n=3d+6 and n=3d+7 are certified separately for d>=24.
They complete the desired intercept 6 without requiring the refused unsplit
(6,16) cone. The exact line substitution has d=s1, n=3s1+c; the second
parameter does not occur. PIP, closure, hitting and constant integer labels
are certified afresh, followed by a finite label-set comparison at d=25.

The determinant is -1; the inverse is integral. No lattice residue is lost.
PIP, complete symbolic closure, all-vertex offset-zero hitting and constant
integer offsets are checked in that order, by the unchanged imported kernel.
No graph table is an input to the closure.

For every d>=24, n above the stated target, split at these exact endpoints:

1. On minus, n=3d+6 or n=3d+7 is a lower-line certificate. Every other target member with n<=4d-16 is in its sign’s middle cone, by the inverse above.
2. 4d-15<=n<=4d-5 (plus) or <=4d-1 (minus) is in a new diagonal.
3. 4d-4<=n<=4d-1 (plus), or 4d<=n<=4d+3 (minus), is in #390's four top layers.
4. n>=4d (plus) or >=4d+4 (minus) is in T_C (#384).

There is no integer between adjacent pieces. For 6<=d<=23, enumerate all
members from 3d+4 (plus) or 3d+6 (minus) through the integer below T_C; larger n are in T_C.
Every such finite graph is complete under the existing fail-closed cap,
with every vertex reaching offset zero. No common label set is imposed
between pieces or between small-gap members.

This elementary partition is the universal coverage argument. The separate
Mojo coverage audit checks every d=6..64,n=0..400 as a finite error detector;
it is not presented as a proof by bounded enumeration. It validates the
middle inverse and every classification endpoint, and refuses oversized
inputs before machine-integer arithmetic. Tests explicitly show a target
member lost if the bridging diagonals were omitted.

## Diagonal results

All 26 new diagonal families certify for every d>=24. The changed-label layers are:

| sign | n-4d | labels |
|---|---:|---:|
| plus | -9 | 282 |
| plus | -8 | 282 |
| plus | -7 | 276 |
| plus | -6 | 278 |
| plus | -5 | 196 |
| minus | -3 | 248 |
| minus | -2 | 252 |
| minus | -1 | 226 |

The other diagonals are plus c=-15..-10 (280 labels) and minus c=-15..-4 (250 labels). Each set is computed separately, and each vertex has an offset-zero
descendant. Equality of counts is insufficient: the two 282-label plus
sets are different. The independent exact oracle pins that negative control.
At minus d=40,n=3d+5=125 the graph has 252 labels, so the proposed 250-label
middle graph cannot extend even one line downward merely by changing its
lower inequality. This does not refute BH on that line.

## Trust, replay and remaining obligations

The canonical driver is kernel/class_c_slope_three.mojo. The existing
kernel/class_c_lower_strip.mojo driver produced the initial cone/diagonal
runs; both call the same unmodified certifiers and print the same results.
All source hashes are recorded, including both drivers. The oracle constructs
literal-word intersections using separate exact Fraction field arithmetic.
It checks complete native label sets and finite-member hitting depths, not
merely counts. These finite checks do not replace uniform cone certification.

The exact native finite end computation contains 189 plus and 225 minus
members (414 complete graphs). A second successful plus (8,16) cone is
preserved as an exploratory receipt; the final bound uses the stronger
(4,16) result. Five of the eight proposed corners refused on a beta-sign
comparison. No failure is hidden or recast as a non-BH member.

Independent replay passes 547 complete graph checks and ten separate exact
sign reads: 104 diagonal samples, eight interior-cone samples, eight lower-line
samples, all 414 finite ends, three label-set controls and ten graphs at the
refusal-sign members. Every native finite label set and hitting depth agrees.

The packet records all successful and refused candidate runs, the finite
member blocks, an independent oracle receipt, code hashes and checksums.
Finite logs are gzip-compressed losslessly with zero timestamp; decompression
recovers the exact native stdout. A reader can inspect the full label rows.
A readable summary lists every finite member and its graph size/depth.

The graph cap is 20,000. Undecided signs, a fit that cannot be certified,
a growing child range, non-PIP members, non-hitting vertices, nonconstant
export offsets or sample mismatches refuse, without being called mathematical
counterexamples. Shifted sign budget k<=24 is inherited; the actual exponent
is printed by each cone run. Exact arithmetic and the symbolic engine remain
trusted and independently human unreviewed.

#390's hosted certificate jobs were queued at this session's initial check.
Its merge is not interpreted as a hosted replay pass. The continuation has
its own dedicated exact-head workflow; hosted acceptance remains separate
from the local certificates and the mathematical partition above.
No governed claim status or historic evidence packet is modified.


## Exact obstruction to unsplit sign paths

A native Sturm–Tarski checker and an independent Fraction interval oracle
both certify opposite signs of the actual refused comparison polynomials:

| cone (eps,A,B) | first (u,v), sign | second (u,v), sign |
|---|---|---|
| (+1,4,10) | (0,0), + | (0,20), - |
| (+1,8,10) | (0,0), + | (0,20), - |
| (-1,6,4) | (0,0), - | (20,0), + |
| (-1,8,4) | (0,0), - | (0,20), + |
| (-1,6,16) | (0,0), - | (20,0), + |

For example, the final minus refusal has

    G(beta) = (88+4v+6u) + (-44-2v-5u) beta + u beta^2.

At u=v=0 this is negative; at (u,v)=(20,0) it is positive, with exact
isolating-root counts and Tarski queries in the native receipt. The two
members are (d,n)=(22,72) and (42,152). Their graphs both have 250 labels.
Thus even constant label sets do not make every clipping comparison uniform.
The explicit lower-line split preserves both the theorem and this obstruction;
it does not claim the unsplit cone itself lacks BH.

## Residual after this continuation

Combining with the exact domain lemma and #390's entire gap-6 strip, the
remaining class-C members have d>=7 and

- plus: 2d-5<=n<=3d+3;
- minus: 2d+1<=n<=3d+5.

This removes the separate upper residual band and lowers the previous
middle onset. The bounds are sufficient, not asserted minimal. The growing
lower-edge graphs and universal BH, realization/non-unit transfers and PSC
remain open. No governed claim or historical completion snapshot is promoted.
