# Claim status and source map

**Status date:** 2026-09-13  
**Repository baseline:** `main@db5b217b6737c369170bb04ae6e3e7f05f638be8`

This is the short authoritative index for deciding whether a mathematical
statement is proved, imported, computationally certified on a finite domain,
conditional, or open. It supplements the full exposition in
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex` and the dependency
structure in `docs/proof-ladder.md`.

The absence of a historical file and the absence of a proof are different
conditions. A result can cease to be source-pending because it has been
independently reconstructed, or because audit shows that it is an open
conjectural obligation rather than a theorem awaiting recovery.

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
| G1b-1 bounded discrepancy | **Repository-proved by reconstruction** | `docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md`; manuscript Theorem 4.4; PR #69, merge `7fa20b6` | Bounds the prefix-difference walk, not state length; does not imply G1. |
| G1b-2 renewal finiteness | **Open conjectural gate** | Manuscript Open Problem 4.10; `docs/proof-ladder.md` | Equivalent to G1 after G1b-1; must be non-unimodular-safe. |
| Finite BPA, G1 | **Open conjectural gate** | Manuscript Proposition 4.11 and open-problem list | Bounded discrepancy alone is insufficient. |
| Sink-SCC reduction under G1 | **Conditional theorem** | `docs/sink-scc-reduction.md`; manuscript Theorem 5.1 | Requires finite BPA to extract a finite recurrent obstruction. |
| Degree-two carrier span / wedge dichotomy | **Repository-proved by reconstruction** | Manuscript Theorem 5.16(i) and Proposition 5.20; `docs/galois-aux-b-source-resolution-2026-09-13.md`; PR #68, merge `accda1a` | If a closed nonproductive carrier has nonzero `K2`, its rational span is all of `Lambda^2 Q^3`. This does not prove productivity. |
| Historical degree-three dominant capture | **Historical restricted theorem** | `archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md`, §§8–10; import commit `013fbedc` | Applies to six explicit length-seven `K2=0` seed defects; SCC transfer remains conditional. |
| Concentration / aux-B | **Open conjectural gate, not source-pending** | Manuscript open problem; formulation provenance `af46a0e`, `1297174`; PR #68 source resolution | Means exclusion of strict components with `K2=0`; the archived seed theorem does not prove it. |
| General wedge productivity | **Open conjectural gate, not source-pending** | Manuscript open problem and Proposition 5.20 discussion | Means exclusion of strict components with `K2!=0`; full wedge span alone is insufficient. |
| Bounded degree-three exclusion | **Finite-domain theorem** | `docs/p1a-degree3-partial-theorem.md`; canonical Mojo certificate; PR #67, merge `44e8ad9` | Only the exact 4,554 substitutions with three letters and image lengths at most three. |
| Bounded degree-two wedge productivity | **Finite-domain theorem** | `docs/p1a-degree2-wedge-productivity.md`; canonical Mojo certificate; PR #71, merge `db5b217` | Same 4,554-member domain. The certificate fails closed on capped catalogues and retains replayable countermodels. |
| Seed-patch overlap graph finiteness | **Repository-proved** | `docs/overlap-finiteness-and-coincidence-density-2026-09-13.md`; manuscript Theorem 4.22 | Finite from bounded discrepancy; this does not prove that every overlap is productive. |
| Overlap productivity / coincidence density one | **Open conjectural gate** | Manuscript Open Problem 5.34 | Exact 4,554-corpus productivity is finite evidence only. |
| Density-to-PDS bridge | **Open bridge** | Manuscript Open Problem 5.35 | A positive result could bypass G1 on the PDS route but would not prove G1. |
| SCC Producer / C1 | **Open theorem target** | `docs/conjecture-ledger.md`; manuscript unresolved statements | Conditional reductions and bounded exclusions do not prove it generally. |
| Realization / coincidence-rank chain | **Open bridge, not source-pending** | `docs/source-imports/issue-45/realization-coincidence-rank-audit.md`; PR #69 | Seven obligations G0–G6 remain; formal SCC recurrence, global realization, and collar survival are distinct. |
| Finite collar death | **Empirical evidence** | Realization/collar notes and census artifacts | Requires an independent collar-completeness bound before theorem use. |
| BPA termination / pure discrete spectrum bridge | **Imported theorem plus open repository-interface audit** | `docs/bpa-literature-bridge.md` and cited balanced-pair literature | The standard algorithm must not be silently identified with the normalized all-seed graph. |
| Pisot substitution conjecture in the standing regime | **Open** | Manuscript abstract and unresolved-statements section | Neither finite census closes the general theorem. |

## Source-resolution decisions

### G1b-1

The reported historical contraction estimate

```text
Disc(sigma w) <= c Disc(w) + 2 E_sigma
```

was not recovered and is not used. PR #69 supplied a different global proof
from bounded contracting components of inflated swap-seed prefixes. Therefore
the mathematical claim is repository-proved even though the reported
historical derivation remains unavailable.

### Degree-two Galois propagation

The live carrier implication does not depend on recovery of a v16 manuscript.
The characteristic polynomial of `Lambda^2 M` is irreducible in the standing
irreducible cubic regime. Hence a nonzero invariant rational carrier span must
be the whole wedge space. This is the self-contained wedge dichotomy on
`main`.

The archived degree-three certificate is a different theorem and must not be
used as a carrier-level proof.

### Concentration and aux-B

“Aux-B” previously sounded like a proved lemma with a missing source. The audit
shows that the live content is the open assertion that a strict carrier cannot
have identically zero `K2`. It has formulation provenance but no proof.
Recovery of a historical file is not part of the current dependency plan.

### Realization and coincidence rank

The former status-level equivalence has been decomposed into obligations G0–G6.
These are open transfer and completeness problems. The correct status is
**open bridge**, not **source-pending theorem**.

## Finite-certificate boundary

The degree-two and degree-three certificates jointly eliminate the two
first-defect cases on the exact 4,554-member short-image corpus. They do not
supply a uniform bound on substitution image length, component size, state
length, collar radius, or first-defect degree. Accordingly:

1. every domain parameter must remain in the theorem statement;
2. catalogue caps must fail closed;
3. zero-survivor conclusions require positive and negative predicate
   calibration;
4. a surviving component must be emitted as a replayable state-and-edge
   countermodel;
5. absence of observed higher-degree states is empirical unless an independent
   completeness theorem excludes them.

## Current no-assumption frontier

The shortest honest completion program now has two possible assembly routes:

1. prove G1b-2, equivalently G1 after the reconstructed G1b-1 theorem;
2. prove general concentration for the `K2=0` case;
3. prove general wedge productivity for the `K2!=0` case;
4. assemble SCC Producer from the finite-graph reduction and the two carrier
   exclusions;
5. alternatively, prove overlap productivity and the density-to-PDS bridge to
   obtain a G1-free PDS route;
6. audit the exact interface from the repository's normalized BPA to the
   literature's pure-discrete-spectrum criterion.

The historical v16 manuscript is not a prerequisite in this list. If recovered,
it should be archived and compared against the reconstructed proofs and open
obligations, not automatically promoted.

## Citation and maintenance rules

- Cite the current manuscript for exposition and the underlying proof note for
  load-bearing reconstructed arguments.
- Cite PR and merge identifiers for provenance, not as mathematical proof.
- Cite the archived certificate only with its seed-specific degree-three scope.
- Label all 4,554-corpus statements as finite-domain theorems.
- Never describe concentration, general wedge productivity, G1b-2, the
  realization bridge, SCC Producer, or PSC as proved.
- When a status changes, update this map, `docs/conjecture-ledger.md`,
  `docs/proof-ladder.md`, `docs/current-proof-architecture-2026-09-11.md`,
  the manuscript status table, and `tla/Ledger.tla` in the same PR.
