# Issue #139: completing the minus residual boundary strips

**Status:** exact strip certificates completed with the lock-matched Mojo compiler; complete minus assembly and governance replay recorded below. Independent human review and CI integration pending; universal #139 and PSC open.

## Target and literature decision

PR #290's uniform carrier covers a>=2,b>=1. The exact residual parameter map
in the boundary-hitting progress note also includes a=0 and a=1. For either
fixed a, set n=b-1>=0. These are precisely the class-D lines

- a=0: (p,q,r)=(n+6,n+7,n+5);
- a=1: (p,q,r)=(n+9,n+10,n+7).

Use the existing Theorem L/L'' exact line certificate: symbolic all-child
seed graph on a proved tail, exact screened finite prefix, and concrete graph
agreement at the threshold and five parameters later. This is specialization
of the already-reviewed contract, not new theorem machinery. The literature
stop/go in `class-d-minus-cycle-literature-gate-2026-10-19.md` applies unchanged:
Akiyama–Lee supplies the inflation/overlap distinction, Minervino–Thuswaldner
preserves non-unit realization hypotheses, and the parametric-guard literature
does not supply a universal PSC theorem. No finite sample proves these lines.

**Proceed:** certify both entire lines, including every omitted finite-prefix
member. Then assemble the disjoint domains a=0, a=1 and a>=2 for b>=1. Retain
the separate merged b=0 certificate and the plus branch's execution work in
PR #293. Missing line receipts, caps and non-hitting vertices must refuse.
Invalid strip selectors and omission of either strip must not produce a
complete-quadrant receipt. This does not cover arbitrary substitutions or
settle the universal acceptance criterion of Issue #139.

## Exact strip results

| Fixed a | Line parameter | Symbolic tail | Symbolic vertices | Finite PIP members | Exact graph agreement |
| --- | --- | --- | ---: | ---: | --- |
| 0 | n=b-1 | n>=42, or b>=43 | 140 | every n=0..41 (42 members) | n=42,47 |
| 1 | n=b-1 | n>=72, or b>=73 | 137 | every n=0..71 (72 members) | n=72,77 |

`certify(ClassLine(...))` constructs the symbolic seed graph, verifies that
every vertex can reach offset zero, and proves the threshold. It screens and
checks every finite-prefix member and verifies the symbolic/concrete graph
agreement. The strip wrapper additionally rejects any non-PIP or inadmissible
prefix member, or any mismatch between prefix length and threshold. Thus no
parameter is silently skipped in the stated all-member result. Graph caps
and undecided signs remain fatal. Thresholds are proof cutoffs, not parameter
caps; the symbolic tail is unbounded.

Independent Python Q(beta) graphs at a=0,1 and b=1,2,73 test the concrete
boundary and tail, using a separate field implementation. They calibrate the
proof, but do not supply its universal quantifier. The existing line engine
and occurrence enumeration are unchanged by this contribution; none of the
unmerged #293 sign-reader or interval-sweep changes is required here.

## Complete minus assembly

The four regions below are disjoint and cover every integer a,b>=0:

| Region | Certificate |
| --- | --- |
| b=0, a>=0 | Existing merged minus boundary template: symbolic a>=4, exact a=0..3, full support agreement at a=4,8 |
| b>=1, a=0 | New first complete line |
| b>=1, a=1 | New second complete line |
| b>=1, a>=2 | PR #290 seed carrier, plus #287 exact ranked descent and #288 conditional target geometry |

The native `certify_minus_residual()` call executes all four. It prints
`CLASS_D_MINUS_RESIDUAL_BH_CERTIFIED` only after every component succeeds.
The core explicitly replays both the algebraic descent and the conditional
geometry against the same carrier size; a seed-cover receipt alone is not
substituted for a hitting proof. Distinct-letter zero offsets remain valid
boundary hits, and are not reclassified as tile coincidences.

The locked compiler exposed five inherited source-compatibility defects in
`class_d_positive_b_spine.mojo`: an implicit returned List copy, two untyped
index literals inferred as Arrays, and two implicit List borrows. The repair
uses one explicit copy, typed Lists and read-only references. No occurrence
index, rank or algebraic formula changes. The original failure and the
successful pinned spine regression are preserved.

| Claim | Governed status |
| --- | --- |
| Minus b=0 boundary | Repository-proved: `MinusClassDBoundaryLine`; existing theorem, now explicitly registered; human review pending |
| Minus a=0,1 strips | Repository-proved: `MinusClassDBoundaryStrips`; full tails and finite prefixes; human review pending |
| Entire minus residual | Repository-proved: `MinusClassDResidualBoundaryHitting`; all a,b>=0; human review pending |
| Entire minus class D | Repository-proved: `MinusClassDBoundaryHitting`; all PIP class-D members with p=q-1; human review pending |
| Universal boundary hitting | Open: `UniversalBoundaryHitting`, Issue #139 |

The last scoped row follows by the exact existing parameter cover, not a new
computation. For a PIP class-D member with p=q-1, either r>=q-1, already
covered by `ClassDWedgeBoundaryHitting`, or d=q-r>=2. In the latter case put

$$
 a=q-r-2,\qquad b=3r-2q.
$$

Pisot implies chi(-1)<0. Here chi(-1)=2q-3r-1, so integrality gives b>=0.
Also a>=0, and direct substitution recovers

$$
 (p,q,r)=(3a+5+b,\ 3a+6+b,\ 2a+4+b).
$$

The complete minus residual certificate therefore covers the other case.
This case split proves the entire **minus** PIP class-D branch. It does not
settle plus class D or arbitrary substitutions, and does not by itself supply
a uniform depth bound for the other catch-up-free classes A/C.

## Runtime and validation boundary

The compiler/runtime from the existing #293 work is available locally. Its
two archives match `kernel/pixi.lock` SHA-256 values. The installed compiler,
standard library and three shared runtime libraries were compared byte for
byte (via hashes) with the compiler archive. All new canonical execution uses
Mojo 1.1.0.dev2026090805 (34562fa1), with telemetry and crash reporting disabled.
PR #290's seed-carrier regression also passes under this compiler.

These are lock-matched minimal compiler/runtime executions. They are not a
successful full `pixi install --locked` or a GitHub Actions success. No lock or
vendored package was changed. Full CI and independent human review remain
validation work; the repository's convention permits continued research while
preserving those labels.

Evidence, source hashes, native component/aggregate logs, independent samples
and replay commands: `evidence/issue139-minus-strips-2026-10-20/README.md`.
The new CLI accepts either both strips or exactly one of 0,1. Invalid selectors
refuse. Cross-language receipt validation rejects an omitted or duplicated
strip and a missing native aggregate marker.

## What remains for Issue #139

PR #293 reports all six plus wedge cores, 73 strip obligations and six
interface lines completed under the same locked compiler version. Its full
integration/aggregate and inherited regression gates remain separate; this
minus contribution does not silently promote that result. Reconcile its
latest exact receipts and validation repairs, then assemble full class D only
when those obligations are met. After class D, the class-A slope-one growing
graphs and the remaining A/C regions still require uniform vertex-family or
all-child good-branch arguments. No additional cycle-only or quotient-only
sieve closes that gap. Universal #139/#84/G1/PSC stay open.

## Subsequent reconciliation (2026-10-21)

Merged #293 has the complete plus native aggregate; the assembly audit now
checks its immutable full local import closure and replays this entire minus
aggregate on reconciled main. See `class-d-assembly-audit-2026-10-21.md`. The
new combined class-D ledger node retains an explicit open integration gate.
Historical statements above about the plus aggregate describe the earlier
frontier; they do not override this later record. Universal #139 stays open.
