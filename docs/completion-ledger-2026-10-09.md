# PSC weekly completion ledger — 2026-10-09

**Repository baseline:** `main@4caca9aef3ec87c2c8d18ade113517aab5b905ee`
(through merged PR #246).
**Purpose:** weekly completion/status snapshot. This file is not a proof
source. Claim status is governed by `claim_governance.toml`, the generated
ledger surfaces, `docs/claim-status-and-source-map-2026-09-13.md`, and the
cited manuscript/proof sources.

## Executive status

General PSC remains **open**. No immutable accepted-proof source on `main`
establishes PSC, seedwise overlap productivity, the universal aligned branch,
the universal strict-zipper branch, formal productivity, or G1. The shortest
PDS route still has exactly one open premise:

```text
primitive irreducible Pisot
=> bounded discrepancy                                  [PROVED]
=> finite seed-patch overlap graph                      [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN: #84]
=> coincidence density one / dense good set             [PROVED]
=> pure discrete spectrum                               [IMPORTED theorem]
```

This cycle advances exact finite-domain closure and structured infinite
families, not the universal conjecture:

- Theorem Ω gives a per-specimen box-automaton certificate. Its completed
  runs prove PDS on exactly the union of the 145,806 ternary PIP substitutions
  with images of length at most 4 or total image length at most 8.
- Theorems L, L′ and L″ prove the required boundary-hitting statement on 47
  one-parameter lines in the catch-up-free determinant-two classification.
- Theorem W proves it on two-parameter wedges of class D; Corollary W1 covers
  every PIP member of class D with `r >= q - 1`.

The family results are computer-assisted and unreviewed. They are theorem
statements only within their declared parameter regions and do not close
issues #84, #138 or #139, formal productivity, G1, or general PSC.

## What is proved on `main`

### Finite-domain PDS certificate

Theorem Ω of `docs/pds-certificate-from-the-box-automaton-2026-10-07.md`
proves, for a fixed PIP substitution, that formal productivity is equivalent
to every vertex of its finite box automaton reaching a coincidence. The
145,806 completed specimens therefore form an exact finite-domain PDS theorem,
not merely a sample. The sufficiency path uses the elementary cycle-in-box
lemma plus the explicitly imported overlap-coincidence and Meyer-property
theorems; it does not depend on Proposition V(2), Theorem B, the periodic-pair
fibre argument, or the converse `PDS => G1` chain.

The universal assertion that every PIP box is productive remains open.

### Structured determinant-two families

The catch-up-free determinant-two programme now contains two distinct kinds
of scoped closure:

1. the aligned/strong-coincidence classification recorded by Theorems E, K
   and the subsequent symbolic-cone results; and
2. boundary hitting on the 47 one-parameter lines of Theorems L, L′ and L″,
   together with the class-D wedges of Theorem W.

For each covered PIP member, the documented implications give strong
coincidence where stated, seed productivity, PDS, and a finite balanced-pair
automaton. These are computer-assisted, review-pending family theorems. Their
coverage is not a uniform theorem for the full catch-up-free determinant-two
class and cannot be promoted to general PSC.

### PDS consequences and ledger reconciliation

The manuscript and generated ledger retain the repository proofs that PDS
implies G1 and termination with coincidence from every swap seed. Both remain
human-review pending. The generated claim graph also records the box-automaton
certificate, formal-productivity routes, the leftmost-chain structure, and the
validated proof-bank dependencies. Those nodes do not make their open premises
true.

## Exact computation, classified by logical role

| Result | Classification | Exact scope | What it does not prove |
| --- | --- | --- | --- |
| Complete productive box automata | **Finite-domain theorem** | 145,806 ternary PIP substitutions: images length at most 4 or total image length at most 8 | PDS for substitutions outside the declared union |
| Two-sided strong coincidence | **Exact finite evidence** | 408,798 ternary PIP substitutions with total image length at most 10; zero failures | A uniform strong-coincidence theorem |
| Closed formal carriers | **Exact finite evidence** | 13,260 formal overlap carriers; zero closed survivors | Universal formal productivity |
| Theorems L/L′/L″ | **Computer-assisted family theorems; review pending** | 47 declared one-parameter lines | The remaining parameter space or #139 uniformly |
| Theorem W / Corollary W1 | **Computer-assisted family theorem; review pending** | Declared class-D wedges; in particular PIP class D with `r >= q - 1` | Class D below that boundary or other classes |

## Open claims and provenance gaps

| Claim | Status on `main` | Exact gap before closure |
| --- | --- | --- |
| General PSC | **Open** | No authoritative accepted proof on `main`; the one-seed productivity premise #84 remains open. |
| Seedwise overlap productivity (#84) | **Open; sole shortest-route premise** | Exclude every reachable bad closed SCC, either by closing both #138 and #139 or by a stronger uniform theorem. |
| Aligned branch (#138) | **Open universally** | Family results do not prove the remaining unbounded parameter regimes or a uniform fixed-letter theorem. |
| Strict-zipper branch (#139) | **Open universally** | The line and wedge certificates do not give a uniform, occurrence-compatible hitting/coverage theorem. |
| Formal productivity | **Open universally** | The 145,806 complete specimen certificates and 13,260 carrier exclusions have no independent all-PIP completeness theorem. |
| G1 | **Open universally** | It is necessary under the review-pending `PDS => G1` proof and follows conditionally from four routes, but none of their universal premises is closed. |
| `PDS => G1` package | **Repository-proved; human review pending** | Direct human review of Theorem R, Proposition F, Theorem B/Lemma C, and the primary Barge fibre/coincidence-rank source chain. |

Two open pull requests are deliberately excluded from the authoritative
baseline. PR #235 audits Theorem Ω and the PDS bridge; until merged, its
proposed repairs are review material rather than `main` provenance. PR #247
refactors shared parameter-polynomial algebra; it is an engineering change and
does not alter theorem status while open.

## Next obligations

The ordered strict-zipper work now has a sharper sequence:

1. cover the remainder of class D below `r = q - 1`, first on the second
   constant-graph cone and then on the Pisot-boundary fringe;
2. prove analogous two-parameter wedges in classes A and C;
3. handle the growing seed graphs on the class-A slope-one boundary with
   vertex families rather than a fixed graph; and
4. extract a uniform depth bound `K` for the catch-up-free determinant-two
   class, the first listed obligation that would meet #139's uniform
   acceptance criterion on that class.

In parallel, #138 still requires a uniform treatment of its remaining
unbounded family, and the `PDS => G1` source chain requires human review. A
larger fixed census is not a substitute for any of these obligations.

## Provenance boundary

This snapshot treats `main@4caca9a` as authoritative. PR merge metadata is
provenance for code and documents, not mathematical proof. The manuscript,
proof notes, exact certificate contracts, imported-source gates, and generated
claim dependency closure carry the mathematical assertions. Open branches,
open pull requests, issue descriptions, project plans, and computational
patterns may guide work but cannot promote a theorem.
