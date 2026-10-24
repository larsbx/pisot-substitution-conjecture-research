# Class B top-layer label rays

## Target and literature stop/go

This continues the exact label-set experiment explicitly authorized by the
[existing stop/go](class-b-top-layer-stopgo-2026-10-23.md), rather than proposing
a new universal invariant. Reuse its BBJS, Minervino–Thuswaldner and
Akiyama–Gähler–Lee hypothesis exclusions, the primary-source annotations
in [the issue-84 collection](../sources/issue-84/README.md) (AL11, CS01, MT14),
and the [Theorem C method](p1b-symbolic-cone-2026-10-08.md).
The overlap update is established prior art; multiplicities and actual ordered
prefix occurrences must survive any later certificate. Non-unit geometry and
seed-relative reachability remain separate obligations. Decision: proceed with
finite exact label comparisons only. Count fits are a negative control, never
a label equality criterion. A failed finite fit rejects the stated carrier
model and floor, not every possible eventual affine representation.

## Representation

Labels are `(top,bottom,k,c,y)` with bottom-minus-top integral Parikh offset.
Graph enumeration order has no mathematical meaning. Exports sort full labels
lexicographically and retain the exact first-hit depth alongside each label.
A graph cap, failed integrality conversion or missing target descendant refuses
an export. The existing archive has count/depth summaries, not complete label
files; regenerate graphs and compare their summaries before fitting carriers.

No universal boundary-hitting, G1, or PSC claim is changed.

## Typed coordinates and occurrence transformations

Use the unimodular coordinate change `s=3k+c+y`, `d=c−3k`; the inverse is
`c=3k+d`, `y=s−6k−d`. A typed carrier interval is
`(top,bottom,s,d; A*l+B <= k <= C*l+D)`. Holes are retained as separate
maximal intervals. No convex hull or cardinality-only comparison is used.
The direction along each interval is exactly `(1,3,−6)`.

Let `eps=+1` on plus and `−1` on minus, and `q=g*l+r`.
For a legal occurrence pair let `Δ=P_bottom−P_top` be the difference of
proper-prefix Parikh vectors. Direct multiplication by the incidence matrix
gives the integer identities

```
k' = s − k + Δx
 d' = −2s + Δc − 3Δx
s' = (q+4+eps)s − g*k − eps*d + 3Δx + Δc + Δy.
```

These identities hold for each integer offset; real overlap and seed
reachability are separate conditions. They do not assert that arbitrary
chosen prefix indices describe a legal child.

Each image has FIRST, RUN and LAST segments. FIRST has prefix zero. At RUN
index `j+1` (0<=j<m), and LAST index `m+1`, the prefix is `(1,0,j)` for
parent x and `(0,1,j)` for parent c or y, with `j=m` at LAST. Here
`m=p,q,q+eps` respectively. Thus fixing the two segments fixes `Δx,Δc`.
For a target type `(s',d')`, the required run-index difference is

```
j_bottom − j_top = s' − (q+4+eps)s + g*k + eps*d − 3Δx − Δc.
```

Intersect this equation with the actual two segment ranges, including empty
RUN cases. Solving for k produces ceil/floor bounds divided by g, and for a
fixed residue r their parameter parts are affine in l. These are candidate
occurrence-compatible transformations, not certified all-child closure.
Every future chosen edge must also check its child letters, integer shift,
strict overlap and complete legal index ranges.

A natural rank synthesis class is a nonnegative integer potential
`X_row(l,k)=a_row*l+b_row*k+c_row`, with additional interval pieces if
needed. Require X=0 at offset-zero targets and, for each non-target,
one **actual** indexed child with `X_child < X_parent`. First-hit depth
itself need not fit this class. Finite depth fits alone cannot validate its
infinite-tail endpoint slopes. No rank candidate is accepted without those
inequalities and all-child closure.

## Counter-calibrations and rank stop/go

The actual plus g=2 graphs at q=9,11,13 have 1461,1573,1685 vertices.
Nevertheless type `(top,bottom,s,d)=(0,2,−1,−3)` has k-sets respectively
`[−6,0]`, `[−7,−3] ∪ [−1,0]`, `[−8,−4] ∪ [−1,0]`.
The label `(0,2,−2,−9,14)` is present at q=9 and absent at q=11.
Thus +112 counts do not prevent an internal hole from appearing. This
rejects starting this fixed maximal-interval model at q=9; it does not
refute a different representation or eventual affine structure.

The rank prototype is deliberately **synthesis only**. On plus g=1, fit
`depth <= floor((a*l+b*k+c)/2) <= depth+slack` per maximal interval using
q=9..26, with integer a,b in [−4,4], slack in [0,2], and nonnegative eventual
endpoint slopes. Of 389 intervals, 290 admit candidates and 99 refuse this
bounded search. The 290 envelopes survive q=27..42. This does not turn them
into ranks. Native exports reconstruct 5626 actual legal shortest-descent
occurrences on q=9,10. An independent integer prefix replay validates all
5626, but 4868 touch an interval without a candidate and **202** of the
remaining selected edges fail strict decrease in X.

For example at q=9 the chosen indices `(i,j)=(11,0)` send parent
`(y,x,1,3,−5)` to child `(x,x,0,−3,5)`, with `X_parent=X_child=10`.
Both states have their recorded decreasing *first-hit depths*, so an envelope
of those depths is insufficient for a strict potential. Other child choices
might decrease X; this example does not refute existential descent or every
affine potential.

**Decision:** go for the finite label model; redirect the coarse rank approach
to piecewise potentials and occurrence choices synthesized together. Stop
before promoting any infinite-ray certificate. Needed next: uniform strict
geometry, seed inclusion and all-child closure on the typed intervals,
legal parameter-dependent occurrence maps, and integer potential descent
on every chosen piece for every l above its floor. The exact finite prefixes
are present in the packet; the infinite tails remain conjectural carriers.

No top-layer infinite ray is certified here. The Python rank search is an
explicitly bounded prototype under the repository's prototyping policy,
not a second canonical certificate implementation.

## Finite results

All 289 complete pilot graphs through q=42 were exported, including the 177
distinct graphs summarized by the old archive and 112 additional exact graphs.
All 177 old count/depth summaries agree. Floors were fitted only within each
line's old parameter bound; all 112 later graphs are held out. All 21 residue
models pass every full label-set comparison on their observed tails.

Residues in each table cell are ordered r=0,1,...,g−1.

| Branch | g | Candidate q floors | Typed interval counts |
| --- | --- | --- | --- |
| plus | 1 | 9 | 389 |
| plus | 2 | 12, 11 | 303, 297 |
| plus | 3 | 12, 16, 14 | 263, 287, 273 |
| plus | 4 | 16, 17, 18, 15 | 265, 247, 251, 271 |
| plus | 5 | 20, 16, 17, 18, 19 | 261, 255, 243, 239, 235 |
| minus | 1 | 15 | 417 |
| minus | 2 | 18, 17 | 228, 218 |
| minus | 3 | 18, 16, 17 | 220, 236, 222 |

Every ray adds 112 labels per l-step. Both verifiers additionally check
that the proposed affine intervals remain nonempty and mutually separated
for every integer l at or above the fitted floor, using nonnegative endpoint
slopes. This certifies the *form of the candidate carrier*, not its equality
with every future graph. No geometric closure or universal descent follows.
The number of training points varies; in particular some larger-gap fits
have only three training members. Their holdouts are useful tests, not proof.

Replay commands, complete prefix label sets, exact coefficient tables,
rank candidates, legal finite witnesses, input digests and execution receipts
are in [the packet](../evidence/class-b-label-rays-2026-10-23/README.md).

Historical input digests identify the source used for the archived execution
at tree `1c4ce91a350981c40f4a6e889b26b04cc6fde418` (initial PR commit
`7c2d83fc8aa44db36662811d914ec146a161d269`). They do not prohibit future
edits to all kernel modules. The manifest regression validates its structure;
fresh native export comparison and independent checks validate later replays.
