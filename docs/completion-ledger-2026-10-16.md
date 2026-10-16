# PSC weekly completion ledger — 2026-10-16

**Repository baseline:** `main@b378392f64f6d5d64c53a17c6d134315bb079416`.
**Purpose:** weekly completion/status snapshot. This file is not a proof
source. Claim status is governed by `claim_governance.toml`, the generated
ledger surfaces, `docs/claim-status-and-source-map-2026-09-13.md`, and the
cited manuscript/proof sources.

## Executive status

General PSC remains **open**. No immutable accepted-proof source on `main`
establishes PSC, seedwise overlap productivity, the universal aligned branch,
the universal strict-zipper branch, formal productivity, or G1. In particular,
the Nakaishi source audit does not provide acceptable general-proof
provenance: it exposes a first-entry measure error, a radius mismatch, and an
exact address-to-offset transport obstruction. The shortest PDS route still
has exactly one open premise:

```text
primitive irreducible Pisot
=> bounded discrepancy                                  [PROVED]
=> finite seed-patch overlap graph                      [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN: #84]
=> coincidence density one / dense good set             [PROVED]
=> pure discrete spectrum                               [IMPORTED theorem]
```

This cycle adds imported scope, sharp conditional reductions, and negative
controls. It does not close a universal gate.

## Merged theorem and certificate advances

### Flow-to-symbolic and Barge-class scope

The imported Sirvent–Solomyak transfer now makes the existing per-specimen box
certificate a symbolic `Z`-action PDS certificate as well as a tiling-flow
certificate. The finite-domain theorem therefore still covers exactly 145,806
ternary PIP substitutions, now explicitly for both actions.

The imported Barge class theorem, the repository's exact detector, and the
same transfer prove symbolic PDS for PIP substitutions whose power or maximal
common-prefix/suffix rotation lies in Barge's class or its mirror. The detector
finds such a witness for 1,248 of the 4,554 standing-corpus specimens. The
imported Brun-composite corollary gives another structured family statement.
These results retain their exact hypotheses and do not extend to arbitrary PIP
substitutions.

### Complete-box route to G1

The depth note now assembles a complete box offset-zero certificate directly
into all-seed G1, conditional on a uniform complete-box depth `K`, with the
integer bound `2 L^(K+2)`. This is a proved implication using Lemma Ω1 and the
half-coincidence route. The universal common-boundary premise remains open, so
neither G1 nor PSC is promoted.

### Residual determinant-two class D

The exact parameter algebra reduces the remaining PIP class-D region below
`r = q - 1` to two complete unimodular parameter quadrants `a,b >= 0`, with
changing-graph Pisot-boundary edges at `b = 0`. This is a reduction of the
next proof target, not a boundary-hitting theorem for either quadrant.

## Corrections and negative controls

| Finding | Logical role | Consequence |
| --- | --- | --- |
| Exact depth-9 aligned-prefix witness for `sigma=(001,22,220)` reaches radius 10 at cut 9,054 | Exact finite countercontrol | Retires the historical radius-8 plateau inference; supplies no uniform radius or closure theorem. |
| K2 spectral-radius result | Conditional theorem | If the reachable balanced-pair closure from a dominant length-two K2 source is finite, a recurrent SCC has spectral radius at least `beta*|beta_2|`; finiteness remains unproved and predecessor contraction stays retired. |
| Mercat–Akiyama audit | Prior-art gate | The interior-language criterion is unit/unimodular in the relevant form; a non-unit transfer still needs an occurrence-preserving state bridge and adelic extension. |
| Nakaishi audit | Source-transfer stop | The printed general-proof route cannot be imported: the first-entry identity has a missing intersection term, Theorem 3 has a radius mismatch, and source-diagonal cancellation does not supply the required forward integer-offset ancestry. |
| Projected box-walk audit | Exact semantics correction | Projected imbalance zero is not coincidence, and projected vector paths can splice incompatible occurrences; positive paths require occurrence replay/lifting. This audit is separate from Theorem Ω and does not change its certificate. |
| Ternary non-unit family `a -> a^k b c^h, b -> ab, c -> a` | Local exact calibration | One reachable state has an indefinitely repeatable nonzero loop but also legal exits reaching zero/coincidence in one/two steps. The whole family is already PDS by the imported mirror-Barge route, so it is not a new family-level advance or counterexample target. |

These controls consistently show that one recurrent path, a projected path, a
bounded plateau, or a project-management premise is not a theorem about an
entire child-closed nonproductive SCC.

## Exact computation, classified by logical role

| Result | Classification | Exact scope | What it does not prove |
| --- | --- | --- | --- |
| Complete productive box automata | **Finite-domain theorem** | 145,806 ternary PIP substitutions: images length at most 4 or total image length at most 8 | PDS outside the declared union |
| Barge-class detector | **Exact finite classification feeding an imported theorem** | 1,248 of the 4,554 standing-corpus specimens have a power/rotation/mirror witness | Barge-class membership or PDS for arbitrary PIP substitutions |
| Two-sided strong coincidence | **Exact finite evidence** | 408,798 ternary PIP substitutions with total image length at most 10; zero failures | A uniform strong-coincidence theorem |
| Closed formal carriers | **Exact finite evidence** | 13,260 formal overlap carriers; zero closed survivors | Universal formal productivity |
| Theorems L/L'/L'' and W | **Computer-assisted family theorems; review pending** | 47 declared lines and the declared class-D wedges, including PIP class D with `r >= q - 1` | The two residual class-D quadrants or #139 uniformly |

## Open claims and exact provenance gaps

| Claim | Status on `main` | Gap before closure |
| --- | --- | --- |
| General PSC | **Open** | No authoritative accepted proof on `main`; #84 remains open, and the audited Nakaishi preprint cannot fill this provenance gap. |
| Seedwise overlap productivity (#84) | **Open; sole shortest-route premise** | Exclude every reachable child-closed nonproductive SCC, either through #138/#139 or a stronger uniform theorem. |
| Aligned branch (#138) | **Open universally** | Existing family theorems do not cover the remaining unbounded regimes or prove the needed uniform fixed-letter statement. |
| Strict-zipper branch (#139) | **Open universally** | Need an occurrence-compatible, non-unit-safe common-boundary theorem for every realized closed obstruction; current line/wedge results and source audits are partial. |
| Formal productivity | **Open universally** | Completed finite domains and carrier exclusions have no all-PIP completeness theorem. |
| G1 | **Open universally** | Complete-box, productivity, strict-zipper, and G1b-2 routes remain conditional on open universal premises. |
| `PDS => G1` package | **Repository-proved; human review pending** | Independent review remains validation debt; it is not an extra mathematical premise and does not promote PDS or G1 universally. |

## Open pull requests and issues

Open PRs are evidence or candidate work, not part of this baseline. In
particular, #263 and #266 propose class-D boundary certificates, #273 proposes
occurrence-path replay and matched-target certificates, and #235 audits the
Theorem Ω PDS bridge. None may be used to promote a claim until merged and
reconciled with the proof sources and generated ledger. The performance PRs
#252, #257, and #267 are claim-neutral.

The governing mathematical issues remain open: #84 (seedwise overlap
productivity), #138 (aligned branch), #139 (strict zipper), #44 (G1b-2), #43
(concentration), #85 (wedge productivity), and #151 (Tier 2).

## Next obligations

1. Prove a universal good-branch mechanism excluding child-closed
   nonproductive realized components; individual periodic paths are
   insufficient.
2. Require exact occurrence-aware replay for every projected matched-target
   path, and prove the projection-lifting/closure statement rather than
   inferring it from vector reachability.
3. Prove boundary hitting on both residual class-D quadrants, including their
   changing-graph `b = 0` edges, then combine with Corollary W1.
4. Pursue extremal-radius or K2 arguments only with their precise statistic,
   stopping theorem, and finite-closure premise exposed.
5. Keep independent human review as non-blocking validation debt until a
   complete closure candidate exists, without mislabelling it as completed.

## Provenance boundary

This snapshot treats `main@b378392f64f6d5d64c53a17c6d134315bb079416`
as authoritative. PR metadata, issue descriptions, planning premises, and
computational patterns are not mathematical proofs. The manuscript, proof
notes, exact certificate contracts, imported-source gates, and generated claim
dependency closure carry the mathematical assertions. No accepted general PSC
proof with immutable, traceable provenance is present on `main`.
