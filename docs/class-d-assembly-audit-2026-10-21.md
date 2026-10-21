# Class-D boundary-hitting assembly audit — 2026-10-21

The exact component certificates support a **scoped class-D closure candidate**.
The refreshed native minus aggregate and plus b=0 boundary pass with Mojo
1.1.0.dev2026090805 (34562fa1). The plus positive-b aggregate from merged PR
#293 is reused at its exact immutable revision, with its complete local
import closure checked. Full acceptance of the combined implementation is
still a separate open gate. Independent human review is pending.

| Claim | Governed status |
| --- | --- |
| Combined integration acceptance | [OPEN] `ClassDIntegrationAcceptance`; current-head full locked Pixi/CI acceptance is pending |
| Plus b=0 boundary | Repository-proved: `PlusClassDBoundaryLine`; full native and independent oracle replay, human review pending |
| Plus positive-b residual | Conditional theorem: `PlusClassDPositiveBBoundaryHitting`; complete exact native receipt exists; combined integration gate retained |
| Entire plus class D | Conditional theorem: `PlusClassDBoundaryHitting`; positive-b residual, b=0 boundary and existing large-r theorem |
| Combined determinant-two class D | Conditional theorem: `ClassDBoundaryHitting`; plus and minus assembly, integration gate retained |
| Entire minus class D | Repository-proved: `MinusClassDBoundaryHitting`, at its recorded seed-graph scope; current native replay passes; full integration and human review remain validation debt |
| Universal strict-zipper hitting | Open: `UniversalBoundaryHitting`, Issue #139 |

## Assumptions and hypotheses

Scope is Theorem E's **determinant-two class-D normal form**, in letter order
(x,c,y): x -> x y^p c, c -> c y^q x, y -> c y^r c. Parameters are nonnegative
integers, the substitution is primitive irreducible Pisot (PIP), and
p-q=s in {-1,+1}. This is not every substitution whose endpoints happen to
look like class D with arbitrary determinant. The object is the repository's
canonical all-swap-seed overlap graph, with fixed parameters along a path.
Neither a complete realized-tiling overlap dictionary nor a non-unit spectrum
hypothesis is supplied by these certificates.

The signed displacement is **bottom start minus top start**, in the same
length basis (x,c,y). Child recurrence is M w + prefix(bottom) - prefix(top).
All three canonical unordered swap pairs and their four occurrence overlaps
are included. Reversing both rows negates displacement and reverses types;
it preserves hitting and absolute-sum assertions. Both implementations use
strict interior overlap, rejecting endpoint-only contact and undecided signs.
A genuine coincidence requires equal letters **and** zero displacement.
Boundary hitting requires zero displacement alone. Distinct-letter zero
vertices remain nonterminal and their children are included in the minus
closure proof. The new native regression checks this distinction explicitly.

## Targeted stop/go reuse

This contribution assembles existing contracts; it introduces no new hitting
mechanism, sign theorem or spectral import. The primary-source/hypothesis
checks in `class-d-minus-cycle-literature-gate-2026-10-19.md`,
`p1b-class-d-positive-b-wedge-2026-10-19.md`, and the Theorem L/W progress
record apply unchanged: Akiyama–Lee's overlap framework does not identify a
seed graph with all realized overlaps; Minervino–Thuswaldner's non-unit
representation hypotheses remain required; parametric-guard methods alone
do not give seed reachability or universal PSC. Proceed with this narrowed
case assembly, retaining the existing negative controls and review labels.

## Exact parameter cover

The established `ClassDWedgeBoundaryHitting` theorem covers r>=q-1, including
the interface. Otherwise d=q-r>=2. Put

$$
a=q-r-2,\qquad b=3r-2q+2s+2.
$$

The incidence matrix and characteristic polynomial are

$$
M=\begin{pmatrix}1&1&0\\1&1&2\\p&q&r\end{pmatrix},\qquad
\chi(t)=t(t-2)(t-r)-2q(t-1)-2p.
$$

For a PIP member, chi(-1)=2q-2s-3r-3=-b-1<0; integrality gives b>=0.
The inverse is exact:

| Branch | p | q | r |
| --- | --- | --- | --- |
| plus, s=+1 | 3+3a+b | 2+3a+b | 2a+b |
| minus, s=-1 | 5+3a+b | 6+3a+b | 4+2a+b |

The (q,r) direction matrix has determinant 3*1-1*2=1. There is no missing
congruence class. Canonical `verify_class_d_cover()` checks these polynomial
identities over exact rationals, without a finite parameter cutoff. The
PIP hypothesis is essential to the inequality; the inverse identities alone
do not prove it. The prior progress note gives the converse PIP screening
argument, including primitivity and irreducibility.

Minus residual coverage is the disjoint union b=0; a=0,b>=1; a=1,b>=1;
a>=2,b>=1. No CycleSum assertion is extended to the first three regions.
Plus coverage is b=0 and b>=1. For positive b put c=b-1>=0. The five low
sectors c<=5a use a=u+v, c=ku+(k+1)v (k=0..4), with integer inverse
u=(k+1)a-c, v=c-ka and determinant one. Boundary rays can occur twice in the
cover; that is harmless duplication, not disjointness. The origin is covered.
The six interfaces c=5a+j, j=1..6, and the high sector c=5a+7+v leave no gap.
No +1 shift is omitted at b=1.

## Symbolic tails and finite prefixes

| Component | Unbounded proof and required finite work |
| --- | --- |
| Minus b=0 | Symbolic tail a>=4, exact a=0..3; full directed support at a=4,8; 145 vertices, 781 edges, maximum boundary depth 4 |
| Minus a=0,b>=1 | n=b-1>=42 symbolic tail, 140 vertices; every n=0..41 PIP and hitting; exact vertex checks at n=42,47 |
| Minus a=1,b>=1 | n=b-1>=72 symbolic tail, 137 vertices; every n=0..71 PIP and hitting; exact vertex checks at n=72,77 |
| Minus a>=2,b>=1 | All-seed/all-child carrier, legal ranked occurrence descent and conditional target interiority; no parameter cap |
| Plus b=0 | Symbolic tail a>=7, exact a=0..6 including r=0 at a=0; full directed support at a=7,8; 718 vertices, 4,326 edges, maximum boundary depth 6 |
| Plus b>=1 | Six wedge cores, all 73 returned strips (69 distinct affine lines), all six interfaces, 952 finite-prefix PIP obligations; every line retains exact tail proof and graph checks |

Line `certify()` first proves PIP and symbolic all-vertex offset-zero
reachability on its tail. It then screens every parameter below the proved
threshold and exactly checks every PIP member. Its two concrete tail
comparisons check vertex sets; they are calibration, not a substitute for the
symbolic all-child argument. The minus strip wrapper additionally requires
zero skipped/non-PIP/outside members and prefix length equal to threshold.
All 114 prefix members are therefore accounted for. Wedge cores alone do
not cover the finite-width boundary strips: the assembly consumes the entire
plus aggregate, never the six cores alone. The 952 count is obligations,
not distinct parameter points. The plus maximum-vertices aggregate field
covers cores/interfaces only (164); line graphs reach 465.

## From minus seed closure to boundary hitting

For a>=2,b>=1 the normalized lengths are
(1+X/2-Y/10,1+X/2,1), with X=beta-r-2 and Y=10/beta. The exact eigenvector
binding, root box 0<X,Y<1, and characteristic identities imply
10X>7Y and 10-10X>3Y. They hold for each single fixed parameter pair; no
edge can choose new parameters. The finite candidate sum bound is derived
from child interiority, not assumed to equal one.

The closure checker accounts for all 12 seed candidates (9 included, 3
proved nonreal), 1,287 nonterminal source/segment pairs and 12,255 candidate
children: 1,218 included, 9,034 geometry exclusions and 2,003 occurrence-guard
exclusions. Exact Farkas witnesses refute strict systems by homogenization;
a zero margin never becomes an interior witness. Missing witnesses abort.
This proves seed-qualified carrier closure and hence CycleSum, rather than
using CycleSum to justify its own enumeration.

That induction is only the first step. The aggregate separately replays
`verify_minus_positive_b_spine()` and
`verify_minus_positive_b_conditional_geometry()`. All 145 common labels have
six offset-zero rank-zero targets, 129 direct, four alternative and six
special selected descents, maximum rank four. Each selected occurrence is
legal throughout its stated b=1 or b>=2 region, preserves the exact affine
child equation and strictly lowers rank. Conditional source realness proves
both target margins greater than 1/10. Thus iteration from a real seed state
reaches an offset-zero target; universal realness of every carrier label is
not assumed. Genuine terminal coincidences stop harmlessly. The historical
1,971-state conditional reduction is retained but is not needed to replace
this direct ranked argument.

## Assembly and provenance contract

`kernel/class_d_assembly.mojo` consumes the **complete** plus and minus native
receipts, checks exact cover identities, and replays the entire plus b=0
certificate. The inherited large-r theorem remains a named ledger dependency.
It emits `CLASS_D_ASSEMBLY_CANDIDATE`, explicitly saying integration is
pending and universal #139 is open. It never emits a spectrum, universal
hitting or independent-review receipt.

`tools/check_class_d_assembly_evidence.py` is provenance tooling, not a second
mathematical implementation. It requires the immutable plus aggregate at
53a4021c0e534958c8088ff82f136913d3f08df8, its exact log hash, successful exit,
unchanged lock and all 47 files in its local import closure. It also binds
fresh minus, seed-cover, plus-boundary and assembly receipts to source hashes
and zero process exits. A changed import, log, exit or missing component
refuses. The assembly's receipt checks do not authenticate arbitrary strings;
use the provenance wrapper first. No synthesized marker replaces native work.

## Validation and mergeability

PR #290 at 3b16b5447aa9b3ecdecfdabb5033a381580f230e conflicts with current
main. The reconciliation preserves #293's sign reader, ordered interval
sweep and justified pins, #290's typed/borrowed spine repairs, both append-only
side-note histories and the later estate-governance update. Generated proof
and ledger surfaces are regenerated from their source tables. No vendored
file or lock pin is changed. A regression fixes the actual CI oracle-import
failure by declaring both the repository root and reference directory in
pytest's pythonpath.

Historical CI run 39352929916, job 118401083796, **did** successfully complete
`pixi install --locked` on the older test merge d4806dc. Its subsequent full
verification failed at the old 21/18 pin and Python collection (`oracles`
unimportable). The pin repair is inherited from #293; the import repair is
in this contribution. That historical setup success is not current-head
CI acceptance. This session's full local installation fails fetching locked
`starlette` through the proxy; the lock-matched minimal runtime succeeds.
Archive hashes match the unchanged lock. No gate is waived or labelled green
from cancellation, queueing, a partial run, or a different revision.

Fresh native replay, independent calibrations, generated/governance checks,
TLA model outcomes and exact limitations are recorded in
`../evidence/class-d-assembly-audit-2026-10-21/README.md`. Human review is
nonblocking validation debt under AGENTS.md, not claimed as completed.

## Negative controls and remaining obligations

Retain both kinds of zero-offset state, endpoint exclusion, removed real
carrier target, coarse-box refusal, formal U/Ubar/V/Vbar exits and the
unbounded higher-sum formal two-cycle ray. Those formal cycles remain valid;
seed reachability is essential. The assembly refuses missing/duplicate or
changed component receipts and source hashes. The full plus campaign is
reused only with unchanged mathematical source and all original obligations.

The ledger keeps a separate **open integration gate**. Under that gate the
class-D assembly becomes available, while tests and a TLA model ensure it
still supplies neither universal aligned coincidence nor universal boundary
hitting, G1 or PSC. General class-A slope-one growing graphs and the remaining
class-A/C regions need uniform arguments; neither finite experiments nor
this class-D cover supplies them. Issue #139 stays open until its general,
uniform acceptance condition is met (or the documented standard obstruction
is addressed at that scope). No claim in this note closes #138/#84 either.
