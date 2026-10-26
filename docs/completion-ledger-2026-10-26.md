# PSC weekly completion ledger — 2026-10-26

**Repository baseline:** `main@4eb0427d440e4c2cfe28ce7de934061f1c9bf3ad`
(2026-10-24), a fast-forward from the 2026-10-19 reconciliation head
`main@e062e330`.
**Purpose:** weekly completion/status snapshot. This file is not a proof
source. Claim status is governed by `claim_governance.toml`, the generated
ledger surfaces, `docs/claim-status-and-source-map-2026-09-13.md` (refreshed
2026-10-26), and the cited notes. The previous snapshot,
[`completion-ledger-2026-10-16.md`](completion-ledger-2026-10-16.md), is kept
as historical provenance.

## Executive status

General PSC remains **open**. The shortest route is the conditional
two-obstruction theorem (manuscript `thm:two-obstruction-completion`):

```text
primitive irreducible Pisot
=> bounded discrepancy G1b-1                                     [PROVED]
=> finite seed-patch overlap graph                               [PROVED]
=> A1' (one-sided residual hub-pair eventual coincidence)        [OPEN: #138]
 + BH  (occurrence-compatible offset-zero descent, every cyclic
        seed-reachable strict zipper)                             [OPEN: #139]
=> seedwise overlap productivity                                 [#84: closes exactly with #138 + #139]
=> coincidence density one => pure discrete spectrum             [PROVED / IMPORTED]
```

The route assumes no G1, seed legality, finite injectivity, unimodularity or
independent tile-length rationality. This cycle adds scoped results to BH and
one scoped G1 corollary. It closes no universal gate.

## Merged theorem and certificate advances (2026-10-19 .. 2026-10-24)

All items below are computer-assisted and **project-accepted at their recorded
scope** under `claim_governance.toml [review_policy]`; independent human
review is pending for each.

| Result | Scope | Source | PRs |
| --- | --- | --- | --- |
| Class-D boundary hitting (`ClassDBoundaryHitting`) | every PIP member of `x->xy^pc, c->cy^qx, y->cy^rc`, `p-q in {-1,1}`, every seed | `class-d-assembly-audit-2026-10-21.md`; tree `c325aa53` packet (64 required checks) | #277, #298 |
| Class-D finite BPA (`ClassDFiniteBPA`) | same scope; on `b=0`: `K_- <= 4`, `K_+ <= 6`, `H_-(a)=2(3a+8)^6`, `H_+(a)=2(3a+5)^8` | `class-d-g1-corollary-2026-10-22.md` | #324 |
| Class-A BH, gaps `d >= 5` | lines `(n+d,n,n±1)`, both signs, `n >= 5d` | `class-a-gap-theorem-2026-10-23.md` | #335, #340 |
| Class-A BH, gaps `d <= 4` | each line on its whole PIP domain | `class-a-residue-rays-2026-10-22.md`, `class-a-d4-rays-2026-10-23.md` | #326, #327 |
| Class-C BH, gaps `d <= 5` | class-C lines through gap five | `issue139-ac-gap4-2026-10-22.md`, `issue139-gap5-2026-10-23.md` | #326, #328 |

Class-D G1 is derived from all-seed hitting by the existing half-coincidence
implication (Proposition 4). Rational independence of the Perron lengths
follows from irreducibility and is not an added premise. Finite BPA alone is
not promoted to PDS.

## Corrections and negative controls

- **#340, verifier soundness.** The generic box-power conversion overflowed
  Int64 (`53^11` wraps at `(l0,d0)=(1,53)`) and gave the positive `h^11`
  coefficient a negative sign. Exact rational reciprocal powers replace it.
  The scoped low-degree margins of #335 are unchanged, but the original
  high-degree sign verifier was unsound. Source:
  `class-a-gap-independent-audit-2026-10-23.md`.
- **#331, SP/UD shortcut retired.** The PIP fixture `0->12, 1->01, 2->120`
  (det −1) has the reachable residual `0` and the equal-length nonidentity
  edge `0·12 = 01·2`. This refutes the v5-thread SP proof of UD and
  `UD => finite BPA`. UD stands by the defect theorem. Regression:
  `kernel/tests/test_sp_equal_length_negative.mojo`, with an independent
  oracle in `tests/test_sp_equal_length_negative.py` (added 2026-10-26).
- **Class-B coarse rank rejected** (#342). 202 selected shortest-child edges
  fail strict decrease. A count-only control also fails: plus `g=2`,
  `q=9,11,13` has +112 counts while a typed label set acquires an internal
  hole.
- **Uniform class-A depth refuted.** `n/10 < L_n <= n+2` on the recurrent
  family, so any rank must depend on the parameter.

## Exact computation, classified by logical role

| Computation | Role |
| --- | --- |
| 4,554-member corpus: no caps, max discrepancy 14, longest reachable state 48,020, 1,118,850 overlap vertices, no nonproductive overlap | finite evidence; no uniform bound |
| Class-B top layer (#342): 289 graphs, 112 holdouts, 21 residue models, 5,626 replayed occurrences | finite affine-label evidence only |
| Class-D integration tree `c325aa53`: Python 649 passed / 2 skipped, Lean/TLA, Mojo, 4,554 census with zero caps | exact-revision receipts for `ClassDIntegrationAcceptance` |

## Open claims

| Obligation | Status | Needed to discharge |
| --- | --- | --- |
| A1′ / #138 | open | residual hub-pair eventual coincidence; principally the non-crossing cells of family `F` |
| BH / #139 | open | class A `n < 5d`, class C `d >= 6`, class-B top layer, then outside Theorem E's classes |
| #84 | open | no independent target |
| C4 good-edge bridge | necessary-condition bridge proved | ordered interior/newborn hub-residual word theorem |
| Universal G1 / #44 | open | G1b-2, universal BH, or universal all-seed productivity |
| Concentration #43, wedge productivity #85 | open under G1 | eliminate the `K2=0` / `K2!=0` carrier branches |
| Realization/MEF | open | discharge G0–G6 |

Issue #9 stays closed as research-track/routing completion. Its closing
comment states that C4 itself is open.

## CI and governance state at the baseline

- Scheduled workflows did run on `main@4eb0427d`. Corpus growth (2026-10-24,
  25, 26) and box-automaton PDS evidence (2026-10-25) are green.
- **`Theorem E line and wedge certificates` (`class-b-lines-evidence.yml`) is
  red on `main@4eb0427d`** (scheduled run 40180359004, 2026-10-25). It has
  also been red on every pull-request run since run 31 (2026-10-20). Example:
  class B `(2n, n, n+1)` still reports every vertex hitting, with 76 symbolic
  vertices and all 30 members below the floor hitting. But its tail floor is
  `q0 = 31`, and `certified_lines()` in `kernel/symbolic_line_certificate.mojo`
  pins `q0 = 20`. The certified statement survives at the larger floor, so no
  theorem is refuted. The pins disagree with the current builder, though, and
  the cause has not been identified. This is open work: either root-cause the
  floor change, or re-pin with a recorded reason. Re-pinning without a reason
  is not acceptable.
- #331 merged with a failed `Show your work policy` run and without its
  side-notes entry. The entry was filed on 2026-10-26.
- Open: draft #341 (stronger high-degree Bernstein regression, green). #343
  (class-B affine basis) is largely subsumed by #342. #318/#319 (d=2
  corridors) have failed hosted checks and are not mainline evidence.
- Issue #139's scoped coverage table omitted class A `d >= 5, n >= 5d`; the
  issue body was updated on 2026-10-26 (coverage, PR index, open strips).
  Its universal-open conclusion is unchanged.

## Next obligations (ranked)

1. Class-A strips `n < 5d` and class-C gaps `d >= 6`, on #335's d-uniform engine.
2. An infinite class-B top-layer certificate: symbolic seed inclusion, real
   geometry, all-child closure and an occurrence-selected strict rank.
3. A1′ on the remaining family-`F` cells, with no inherited positional drift.
4. The C4 ordered-word bridge for a supplied finite strict child-closed component.
5. G1b-2 only through realizable labelled returns. No unimodularity, and no
   predecessor contraction.
6. Turn the Theorem E line gate green.

## Provenance boundary

Hosted CI and project acceptance are exact-revision receipts. They are not
independent validation. The PR heads cited above carry their own runs, and
`main@4eb0427d` carries only the scheduled runs listed here.
