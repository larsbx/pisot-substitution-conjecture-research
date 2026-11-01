# Class C below slope three (2026-10-29)

Current mathematical dependencies: [T_C](class-c-tail-theorem-2026-10-28.md)
and [T_C2](class-c-strip-theorem-2026-10-29.md), accepted on main through
PR #384 (`40823631`) and PR #399 (`242c831a`), respectively. Their union gives
BH for every d>=6, n>=3d, on both signs. PR #392 is superseded and is not a
premise. Its original revision `82dc6955faf68df5ee31292b9c2dd503b325a123`
remains a historical source locator in the immutable packet.
See the [integration audit](class-c-below-three-integration-2026-11-01.md).
The [stop/go](class-c-below-three-stopgo-2026-10-29.md) records the reviewed
primary-source hypotheses, exact experiment budgets and subsequent finite
partition refinements. No existing engine, vendored package, old packet or
governed status is edited. Hosted replay and independent human review remain
separate from local exact certificates.

## Locally certified result

For every integer d>=6, canonical swap-seed BH holds on:

| sign | sufficient bound | selected sector | sector labels |
|---|---|---|---:|
| plus | 2n>=5d+8 | 2n>=5d+8, n<=3d-16 | 400 |
| minus | 2n>=5d+16 | 2n>=5d+16, n<=3d-8 | 384 |

The successful cone runs use only direct shifted coefficient signs (Pólya
exponent zero). The eight planned sector proposals produced four successes
and four undecided-sign refusals. These are sufficient bounds, not claimed
optimal. The uniform conclusion combines the new sectors and line pieces
with T_C and T_C2; no single label set is assumed for that union.

## Object and assumptions

The class-C substitution is x->xy^(n+d)x, c->cy^n x,
y->cy^(n-d+eps)c, eps=+-1. The object is the complete canonical swap-seed
overlap graph, with integral bottom-minus-top offsets and offset zero as the
target. It is not asserted to be the full legal-overlap graph. No spectral,
G1, non-unit realization or PSC consequence is imported.

PIP is certified on each symbolic family before graph closure. The exact
PIP-domain lemma and root-identification audit of #390 are inherited: for
d>=6 the starts are n>=2d-5 plus and n>=2d+1 minus. In particular
2n>=5d+A, A>=8, lies inside both domains. This is checked by the family
screen rather than supplied as a presumed verdict.

## Sector and integral inverse

For A,B in {8,16}, use nonnegative integer coordinates u,v:

    d=A+2B+u+2v,     n=3A+5B+3u+5v.

The exact inverse is

    u=2n-5d-A,     v=3d-n-B.

The parameter matrix [[1,2],[3,5]] has determinant -1. Thus the orthant is
exactly the integer sector 2n>=5d+A, n<=3d-B, with no parity omission.
The three runs n+d,n,n-d+eps are integral affine polynomials. The native
test compares the inverse and run identities as exact parameter polynomials,
not only at sampled members.

The existing fixed-point bracket proposals and symbolic sign/closure engine
are reused unchanged. The driver checks PIP, complete closure and all-vertex
offset-zero hitting before imposing constant integer offsets for lossless
row export. No label table or expected count is an input. A capped graph,
undecided sign/fit, failed PIP test, non-hitting vertex, nonconstant export
offset or exact-member mismatch refuses.

## Lines and the actual frontier hypothesis

For a fixed integer c, n=3d+c is an affine line on the same engine.
The initial budget tried all c=-15..3 plus and -15..5 minus from d>=32.
A line's intersection with the proposed frontier is exactly

    2n-5d=d+2c>=A, equivalently d>=A-2c.

Therefore the required lower gap is max(32,A-2c). Requiring a uniform
label table below that gap would be an unnecessary stronger problem.
The targeted replays retain the original floor-32 failures and certify
the needed part separately.

Four minus lines c=-15,-14,-13,-12 refuse at floor 32. The first three
also refuse at their A=8 intersection floors 38,36,34. Their attempted
comparison polynomials are retained exactly in the raw logs. No such
refusal is called a non-BH member. All four certify at d>=48, with 384 labels each. Exact prefixes are checked
individually: c=-15 at d=38..47, c=-14 at d=36..47, c=-13 at d=34..47 and
c=-12 at d=32..47 (52 members). No common-label assumption is imposed
between a symbolic tail and its finite prefix. These four lines are additional
progress; the selected minus sector with B=8 already bypasses their role in
the final half-plane cover, whose required minus bridge is c=-7..5.

For every such split the packet lists the certified floor, the original
required floor and every exceptional member. The independent oracle checks
set equality against the *entire* exceptional integer interval. A missing
integer is a failed coverage check, not a weakened theorem statement.

## Universal coverage argument

Use (A,B)=(8,16) on plus and (16,8) on minus. Given an integer
d>=6 and 2n>=5d+A:

1. If n>=3d, T_C2 applies below 4d (plus) or 4d+4 (minus), and T_C
   applies at and above that onset. Their domains meet without a missing
   integer, and their graph, sign and target conventions agree with this note.
2. Otherwise n<3d. If d>=32 and n<=3d-B, the exact inverse u,v above
   puts the member in the selected sector.
3. If d>=32 and 3d-B<n<3d, the integer c=n-3d is in -15..-1
   (plus) or -7..-1 (minus). Each required line certifies from d=32.
   For any required line with d<A-2c, the frontier inequality is false,
   so that line contributes no target member there. The three plus
   target-line replays also certify, but are not needed beyond the
   already certified floor-32 lines. No required minus line is among
   the four floor-48 tails.
4. If 6<=d<=31 and n<3d, the exact finite-end records contain every
   member from ceil((5d+A)/2) through 3d-1. They were recorded through
   3d+3 (plus) or 3d+5 (minus), so their extra upper records can be
   retained without reliance on the superseded theorem. Minus uses
   finite A=8, a superset of its selected A=16 region. The domain
   clipping does not remove any required member: for d>=6,
   (5d+A)/2 exceeds the plus 2d-5 and minus 2d+1 PIP starts.

Thus every use of the former upper-region result is replaced by the
strictly larger upper region n>=3d. The old bridge lines at c>=0,
minus c=-15..-8, the four minus tails and their 52 prefixes, and the
finite records with n>=3d remain useful historical or additional
certificates but are unnecessary for this selected half-plane cover.
Nothing requires the label sets on separate pieces to agree.

This is the universal coverage argument. The bounded grid audit is a
separate arithmetic error detector over d=6..64,n=0..400. It checks the
integer inverse, ceiling and case endpoints and is not promoted to a proof
beyond that finite grid.

## Exact controls and observed regimes

The finite profile used d=24,40,60 at an explicit list of offsets. It selected
sector candidates but was not treated as a universal label-set certificate.
The following stronger extrapolations are refuted by complete native graphs:

- Plus (A,B)=(8,8) contains (d,n)=(24,64) and (44,114). The first graph
  has 478 labels and the second 400; both have BH.
- Plus (16,8) contains (32,88) and (52,138), likewise 478 versus 400.
- Minus at d=40 the members n=112=3d-8 and n=116=3d-4 have 384 and
  400 labels. This refutes extending the same 384-label table upward;
  it is not a counterexample to the B=8 sector, since the second member
  is outside it.

All control graphs export complete exact label rows and hit depths.
The independent literal-word/Fraction oracle compares those rows, not merely
counts. Old 282-count/different-label and 250/252 adjacent-line controls
remain in the dependency packets.

## Remaining region

Together with #390's complete gap-6 strip, all still-uncovered class-C
members are contained in the following envelope for d>=7:

- plus: 2d-5<=n and 2n<=5d+7;
- minus: 2d+1<=n and 2n<=5d+15.

This is a conservative envelope, not a claim that every member inside it
is untreated. Extra standalone lines and finite-end certificates cover some
members there. The packet inventories those exact scopes. The lower edge
near 2d, universal BH, realization/non-unit transfers and PSC remain open.

## Trust, evidence and non-claims

The canonical implementation is kernel/psc/class_c_below_three.mojo and its
driver kernel/class_c_below_three.mojo. The Python layer is an independent
finite oracle. Full successful and refused outputs, compressed finite logs,
readable member inventories, exact source hashes and replay commands are in
the packet. The compiler, exact arithmetic, sign and closure implementation
remain explicit trust inputs; this session does not constitute independent
human review or a full Lean formalization.

No result is inferred from sample agreement, an exhausted budget or a merged
PR. The historical #392 receipts remain archived evidence, not a live
mathematical or CI dependency. Mainline acceptance does not imply a fresh
hosted replay of this PR. Exact-head hosted acceptance remains required;
independent human review remains separately pending. No entire lower Pisot-edge strip or PSC conclusion
is claimed. The final accepted parameter pieces and remaining region are
listed with the completed receipts.


## Completed independent replay

All 746 complete native/oracle graph comparisons pass: eight sector samples,
160 line samples, all 520 small-gap end members, all 52 exceptional members,
and six label-change controls. Every finite label set and hitting depth agrees.
The successful native regression checks the exact parameter identities,
ceilings, target intersections and oversized-input refusals. The source/packet
hashes, workflow syntax and targeted governance/generator checks are recorded
separately. These local passes do not infer a hosted or human-review result.
