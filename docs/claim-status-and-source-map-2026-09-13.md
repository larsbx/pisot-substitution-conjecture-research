# Claim status and source map

**Status date:** 2026-09-14  
**Repository baseline audited for this update:** `main@383a5e8b550c1538d0a9c32bec23df8d2cc9f70a` (through merged PR #86).

This is the short authoritative index for deciding whether a mathematical statement is proved, imported, computationally certified on a finite domain, conditional, or open. It supplements the full exposition in `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`, the dependency structure in `docs/proof-ladder.md`, and the current architecture in `docs/current-proof-architecture-2026-09-14.md`.

The absence of a historical file and the absence of a proof are different conditions. A result can cease to be source-pending because it has been independently reconstructed, or because audit shows that it is an open conjectural obligation rather than a theorem awaiting recovery.

## Status vocabulary

| Tag | Meaning | Permitted use |
| --- | --- | --- |
| **Repository-proved** | A self-contained proof is present on `main`, with hypotheses exposed and review history preserved. | May be used on the no-assumption proof path under its stated hypotheses. |
| **Imported theorem** | An external or historical theorem is present with an exact statement and source. | May be used only with the imported theorem's hypotheses and scope. |
| **Historical restricted theorem** | Exact historical proof material is preserved, but proves only a special case. | May be cited for that case; it may not be generalized to a carrier theorem. |
| **Finite-domain theorem** | An exact, reproducible, fail-closed computation exhausts a stated finite domain. | May be asserted only for that domain. |
| **Conditional theorem** | The implication is proved once explicitly named open premises are assumed. | May not discharge its premises. |
| **Open conjectural gate** | The statement is a live mathematical obligation. No missing source is expected to close it automatically. | Must remain unavailable to the no-assumption proof path. |
| **Open bridge** | A proposed equivalence or transfer has named unproved interface obligations. | May organize research, but its endpoints may not be substituted for each other. |
| **Empirical evidence** | A bounded experiment has no independent completeness theorem. | Supports prioritization only. |
| **Retired claim** | The argument is false, incomplete, or superseded. | Must not be used. |
| **Historical source missing** | A reported document was not found in reachable history. | Metadata only unless a current proof still depends on it. |

## Live claim map

| Claim | Current status | Exact source | Scope and firewall |
| --- | --- | --- | --- |
| Full incidence rank from `det M_sigma != 0` | **Repository-proved** | State-of-program manuscript, standing algebraic setup | Does not assume unimodularity. |
| Unique decodability of substitution images and powers | **Repository-proved** | Manuscript Theorem 3.1 and power corollary | Derived from full incidence rank; not a standing hypothesis. |
| G1b-1 bounded discrepancy | **Repository-proved by reconstruction** | `docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md`; manuscript Theorem 4.4; PR #69 | Bounds the prefix-difference walk, not state length; does not imply G1. |
| G1b-2 renewal finiteness | **Open conjectural gate** | Manuscript Level-2 open problem; issue #44 | Equivalent to G1 after G1b-1; must be non-unimodular-safe; **not required by Theorem 5.38**. |
| Finite BPA, G1 | **Open conjectural gate** | Manuscript Proposition 4.11 and open-problem list | Stronger structural theorem; no longer a premise of the shortest PDS route. |
| Sink-SCC reduction under G1 | **Conditional theorem** | `docs/sink-scc-reduction.md`; manuscript finite-carrier section | Requires finite BPA to extract a finite recurrent obstruction. |
| Degree-two carrier span / wedge dichotomy | **Repository-proved by reconstruction** | Manuscript Proposition 5.20; `docs/galois-aux-b-source-resolution-2026-09-13.md`; PR #68 | Nonzero `K2` gives full rational wedge span; this does not prove productivity. |
| Historical degree-three dominant capture | **Historical restricted theorem** | `archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md`, §§8–10 | Applies only to the explicitly certified seeds; SCC transfer remains restricted. |
| Concentration / aux-B | **Open conjectural gate, not source-pending** | Manuscript open problem; issue #43 | Alternative finite-BPA route: exclusion of strict components with `K2=0`. Not required by Theorem 5.38. |
| General wedge productivity | **Open conjectural gate, not source-pending** | Manuscript open problem and Proposition 5.20 discussion; issue #85 | Alternative finite-BPA route: exclusion of strict components with `K2!=0`. Full span alone is insufficient. |
| Bounded degree-three exclusion | **Finite-domain theorem** | `docs/p1a-degree3-partial-theorem.md`; canonical Mojo certificate; PR #67 | Only the exact 4,554 substitutions with three letters and image lengths at most three. |
| Bounded degree-two wedge productivity | **Finite-domain theorem** | `docs/p1a-degree2-wedge-productivity.md`; canonical Mojo certificate; PR #71 | Same 4,554-member domain; fail-closed and replayable-countermodel boundary. |
| Seed-patch overlap graph finiteness | **Repository-proved** | `docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`; manuscript Theorem 4.22; PR #72 | Finite from bounded discrepancy; no G1 assumption. |
| Full-rank child-closed overlap constraint | **Repository-proved** | Manuscript Corollary 5.34; PR #76 | A nonempty child-closed noncoincidence set has full rational intersection-vector rank; this is a constraint, not an exclusion. |
| Closed irreducible bad-overlap normal form | **Repository-proved supporting reduction** | Manuscript Proposition 5.43; `docs/p1-overlap-minimal-obstruction-2026-09-14.md`, Proposition 2.1; PR #88 | Failure of overlap productivity has a finite child-closed recurrent nonproductive SCC with `PF(N_S)=beta`, full-rank `V_S`, and `spec(M) subset spec(N_S)`. Standard residual-SCC graph extraction is not claimed as novel. |
| Boundary obstruction / strict zipper dichotomy | **Repository-proved supporting reduction** | Manuscript Proposition 5.44 (with the first-/last-letter closure of the aligned pairs) and Lemma 5.45 (ordered cycle equation, purely periodic offsets); `docs/p1-overlap-minimal-obstruction-2026-09-14.md`, Proposition 3.1; exact Mojo/Python common-start checks; PR #88 | A bad SCC either contains an offset-zero non-eventually-coincident pair or all child factorizations are strict no-tie prefix-grid zippers. This constrains but does not close Open Problem 5.35. |
| Ordered affine overlap-cycle identity | **Repository-proved finite recurrence lemma** | `docs/p1-overlap-affine-pump-2026-09-15.md`, Lemma 1; canonical Mojo certificate and independent Python oracle | Actual ordered child occurrences satisfy `w'=Mw+q-p`; a replayed cycle satisfies the exact pump identity. A productive determinant-two example has such a cycle, so recurrence alone does not exclude a bad SCC. Context preservation and the recognizability/adelic contradiction remain open. |
| One-step overlap context equality | **Exact finite negative calibration** | `docs/p1-overlap-context-equality-2026-09-15.md`; canonical Mojo diagnostic and independent Python oracle | The same affine child state can arise with unequal paired prefix-suffix addresses. Affine-state equality alone cannot justify pumping. A depth-`k` periodic-patch collar and its recognizability bridge remain open. |
| Coincidence density / dense-good-set equivalence | **Repository-proved** | Manuscript Lemma 5.36; PR #77 | Corrected proof does not assume finite-stage good sets are nested. |
| Density-to-PDS bridge | **Imported theorem** | Barge–Štimac–Williams; manuscript Imported Theorem 5.37; PR #77 | Exact hypotheses checked in the standing PIP regime; no G1 hypothesis. |
| One-seed overlap productivity implies PDS | **Conditional theorem** | Manuscript Theorem 5.38 | Only open premise is seedwise overlap productivity. |
| Endpoint-aligned overlaps = strong-coincidence boundary cases | **Repository-proved** | Manuscript Proposition 5.39; PR #82 | Prefix/suffix boundary cases only; does not prove arbitrary interior overlap productivity. |
| Boundary-hitting criterion | **Repository-proved** | Manuscript Proposition 5.40 / Corollary 5.41; PR #82 | Offset-zero descendant iff exact prefix-Parikh/common-left-endpoint hit. |
| Seedwise overlap productivity / Open Problem 5.35 | **Open conjectural gate — current shortest-path gate** | Manuscript Open Problem 5.35; issue #84 | It suffices that one swap seed have only productive reachable overlaps. All-seed/all-vertex productivity is stronger. |
| SCC Producer / C1 | **Open theorem target** | `docs/conjecture-ledger.md`; manuscript unresolved statements | Can be reached through the finite-BPA carrier route; stronger overlap productivity also implies productivity of reachable BPA states. |
| Realization / coincidence-rank chain | **Open bridge, not source-pending** | `docs/source-imports/issue-45/realization-coincidence-rank-audit.md`; PR #69 | Seven obligations G0–G6 remain; formal recurrence, global realization, and collar survival are distinct. |
| Finite collar death | **Empirical evidence** | Realization/collar notes and census artifacts | Requires an independent collar-completeness bound before theorem use. |
| BPA termination / literature interface | **Imported theorem plus repository-interface audit** | `docs/bpa-literature-bridge.md` and cited literature | Do not silently identify the normalized all-seed graph with a literature algorithm. |
| Pisot substitution conjecture in the standing regime | **Open** | Manuscript abstract / unresolved statements | Current shortest route has the single open seedwise-overlap-productivity premise. |

## Current completion frontier

The shortest no-G1 route is now:

```text
G1b-1 bounded discrepancy                       [PROVED]
=> finite seed-patch overlap graph              [PROVED]
=> one-seed overlap productivity                [OPEN: issue #84]
=> coincidence density one / dense good set     [PROVED]
=> PDS                                          [IMPORTED theorem].
```

Accordingly:

1. **Primary proof target:** seedwise overlap productivity, now normalized to a closed irreducible bad-overlap SCC and split into aligned versus strict-zipper branches by PR #88.
2. **Stronger parallel theorem:** G1b-2 renewal finiteness and finite BPA (issue #44).
3. **Alternative finite-BPA coincidence route:** concentration and wedge productivity (issues #43 and #85).
4. **Secondary certificate route:** realization/coincidence-rank bridge G0–G6.

The historical v16 manuscript is not a prerequisite in this list.

## Source-resolution decisions

### G1b-1

The reported historical contraction estimate

```text
Disc(sigma w) <= c Disc(w) + 2 E_sigma
```

was not recovered and is not used. PR #69 supplied a different global proof from bounded contracting components of inflated swap-seed prefixes. Therefore the mathematical claim is repository-proved even though the reported historical derivation remains unavailable.

### Degree-two carrier propagation and aux-B

The live carrier implication does not depend on recovery of a v16 manuscript. The degree-two rational carrier-span result is self-contained on `main`. The archived degree-three certificate is a different, restricted theorem.

“Aux-B” is not a proved theorem waiting for source recovery. Its live content is the open concentration statement.

### Realization and coincidence rank

The former status-level equivalence has been decomposed into obligations G0–G6. The correct status is **open bridge**, not **source-pending theorem**.

### P0 source/status issue

Issue #45 is closed as completed at the status level: the missing v16 artifact remains historical provenance metadata, while all live claims have a current proof, an exact imported source, or an explicit open classification. Recovery of v16 would trigger archive comparison, not automatic theorem promotion.

## Finite-certificate boundary

Finite-domain claims must preserve their exact domain and fail-closed semantics:

1. every domain parameter remains in the theorem statement;
2. catalogue caps fail closed;
3. zero-survivor conclusions require predicate calibration;
4. survivors are retained as replayable countermodels;
5. absence of observed higher-degree states or bad overlaps is empirical unless an independent completeness theorem excludes them;
6. the 4,554-member overlap census is extremely strong evidence for Open Problem 5.35 but not a universal theorem.

## Hypothesis / generality firewall

- Tile-length rational/integer independence must be derived from irreducibility where used, not added as a standing assumption.
- UD is derived from full incidence rank, not assumed.
- FI, prefix/suffix permutation, or boundary-injectivity conditions are extra hypotheses unless derived.
- Do not import unimodularity through a converse theorem or internal-space argument without restricting the statement.
- Do not treat `pi_s(Z^A)` as a discrete lattice in general.
- Do not identify formal recurrence with global realization.
- Do not treat a finite corpus or collar radius as self-certifying completeness.

## Retired / corrected routes

Do not use:

- predecessor contraction as a proof of finite BPA;
- `UD => bounded total padding`;
- bounded discrepancy alone as finite-BPA proof;
- naive zero-sum-hyperplane contraction;
- unlabelled difference-walk injectivity;
- rank-deficiency of a child-closed bad overlap set;
- nesting of finite-stage good sets in the coincidence-density proof;
- `rho(N_S)<beta` inferred merely from calling a residual real-overlap SCC a boundary system: Akiyama–Lee's residual graph can carry the full expansion spectral radius precisely when a genuine noncoincident overlap remains.

## Citation and maintenance rules

- Cite the current manuscript for exposition and the underlying proof note for load-bearing reconstructed arguments.
- Cite PR/merge identifiers for provenance, not as mathematical proof.
- Cite the archived certificate only with its seed-specific degree-three scope.
- Label the two exhaustively certified 4,554-corpus carrier exclusions as finite-domain theorems; the overlap productivity census remains finite evidence for the general gate.
- Never describe overlap productivity, G1b-2, concentration, general wedge productivity, realization G0–G6, SCC Producer, or PSC as proved.
- When a status changes, update this map, `docs/conjecture-ledger.md`, `docs/proof-ladder.md`, `docs/current-proof-architecture-2026-09-14.md`, the manuscript status table, and `tla/Ledger.tla` as applicable.
