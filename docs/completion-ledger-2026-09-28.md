# PSC weekly completion ledger — 2026-09-28

**Repository baseline:** `main@7eb4d58926456647d3fa2b44a803ad105feba338`, including the merged current-state audit PR #167.  
**Purpose:** weekly completion/status snapshot. This file is not itself a proof source. The authoritative theorem-status sources remain the manuscript, claim/source map, generated proof ledger, and claim-governance record.  
**Current status caveat:** the project-management layer now treats general PSC as closed, while the canonical mathematical record still classifies PSC and the remaining overlap-productivity obligations as open. Issue #153 owns that provenance/status reconciliation.

## Executive status

The principal development this week is a **status/provenance split**, not a newly merged proof of the remaining general theorem.

The project-management layer has moved into a Tier 2 phase: issue #151 carried, before its 2026-09-28 revision, an explicit project premise of general-PSC closure, and issues #84 and #138 were administratively closed on 2026-09-26. At the same time, the canonical mathematical record on `main` still says:

- the Pisot Substitution Conjecture is open;
- seedwise overlap productivity is an open premise of the shortest G1-free sufficiency route;
- the aligned strong-coincidence branch remains mathematically unresolved;
- the strict-zipper branch remains open as the `AdelicPeriodicOffsetHitting` problem;
- G1b-2, concentration, general wedge productivity, and the realization bridge remain open.

Issue #153 explicitly requires the accepted proof source and immutable provenance to be recorded, the authoritative proof/status record changed, and all generated surfaces regenerated before the PSC-closed premise becomes canonical theorem status.

Accordingly, this ledger uses the following boundary:

> **Canonical theorem status remains open; “PSC closed” is currently a project premise pending authoritative proof-source reconciliation through #153.**

This distinction does not block Tier-2 experiments. It only prevents project-management closure from being used as theorem provenance before the repository's own acceptance process has been completed.

---

## 1. Status vocabulary

This ledger distinguishes:

- **Theorem-level / repository-proved:** proved in the repository under the stated hypotheses.
- **Imported theorem:** published external result whose exact hypotheses have been audited.
- **Conditional theorem:** the implication is proved, but one or more premises remain open.
- **Finite-domain theorem:** exact theorem over an explicitly enumerated finite domain only.
- **Empirical / computational evidence:** exact or numerical evidence without a universal completeness theorem.
- **Conjectural bridge:** a proposed implication or mechanism whose missing theorem is named.
- **Open dependency:** an unresolved theorem obligation.
- **Administrative/project status:** issue or roadmap state that does not by itself alter mathematical proof status.

No finite census, issue closure, collar depth, coincidence depth, or research-note claim is promoted to a universal theorem without an independent completeness/provenance argument.

---

## 2. Current proof architecture

The shortest current sufficiency route remains G1-free:

```text
primitive irreducible Pisot
=> G1b-1 bounded discrepancy                           [PROVED]
=> finite exact seed-patch overlap graph               [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN]
=> coincidence density one / dense eventual coincidence [PROVED]
=> pure discrete spectrum                              [IMPORTED: BSW]
```

The important logical split is:

- **OP_seed:** productivity of every overlap reachable from one selected periodic swap seed; this is sufficient for Theorem 5.38.
- **OP_all:** productivity of every vertex of the union overlap graph; this is the stronger manuscript Open Problem 5.35.

Consequences of `OP_all` such as all-pairs two-sided strong coincidence must not be silently transferred to `OP_seed`.

### Established normal form for a failure

A failure of overlap productivity can be reduced to a finite child-closed irreducible nonproductive SCC `S` satisfying:

```text
PF(N_S) = beta,
N_S V_S = V_S M^T,
rank_Q(V_S) = |A|,
spec(M) subset spec(N_S).
```

Thus the hard obstruction is **full rank**, not rank deficient. Generic Perron growth does not contradict the obstruction: `rho(N_S)=beta` is the hard residual case.

The obstruction then splits:

```text
bad closed irreducible S
=> aligned branch:
   S exposes an offset-zero/right-aligned non-eventually-coincident letter pair
OR
=> strict-zipper branch:
   no offset-zero vertex occurs and the ordered prefix-grid zipper remains strict.
```

The two branches are mathematically different and should remain separate research obligations.

---

## 3. Established theorem-level results

| Component | Status | Current standing |
| --- | --- | --- |
| Full incidence rank in the standing irreducible regime | **Repository theorem** | Closed. |
| Unique decodability of substitution images | **Repository theorem** | Closed via full rank + defect theorem. |
| UD for powers | **Repository theorem** | Closed because `det M_{sigma^r}=(det M_sigma)^r != 0`. |
| Tile-length rational/integer independence where used | **Derived theorem input** | Must be derived from irreducibility/cyclic-vector structure, never added independently. |
| G1b-1 bounded discrepancy | **Repository theorem** | Closed; no unimodularity or UD hypothesis. |
| Finite exact swap-seed overlap graph | **Repository theorem** | Closed; does not require finite BPA/G1. |
| Bad-SCC full-rank normal form | **Repository theorem** | Closed; rules out the rank-deficiency route. |
| Endpoint/boundary-hitting criterion | **Repository theorem** | Closed. |
| Ordered affine cycle equation | **Repository theorem** | Closed. |
| Coincidence-density / dense-good-set equivalence | **Repository theorem** | Closed after the non-nesting correction. |
| Dense eventual coincidence => PDS | **Imported BSW theorem** | Source-audited; no seed-legality or unimodularity leak. |
| One-seed overlap productivity => PDS | **Conditional theorem** | The implication is proved; productivity remains the open premise. |
| Exact 4,554-corpus degree-two / degree-three carrier exclusions | **Finite-domain theorems** | Exact only on their enumerated domains. |

---

## 4. Level 2 and unique decodability

### 4.1 UD is no longer the bottleneck

UD is derived, not assumed. It is therefore incorrect to list “prove UD” as a remaining completion task or to add UD as an independent hypothesis.

The corrected logic is:

```text
irreducible + det M != 0
=> full incidence rank
=> defect theorem
=> unique decodability
=> UD for powers.
```

UD is a parsing theorem. It does **not** imply finite balanced-pair dynamics.

### 4.2 Retired Level-2 route

The following chain is withdrawn:

```text
UD
=> bounded total padding
=> predecessor contraction
=> finite BPA.
```

The pair-versus-word distinction is load-bearing: uniquely decoding each individual word does not control how two different balanced words may coexist through indefinitely many compatible substitution contexts.

The project must not reintroduce:

- `UD => bounded total padding`;
- bounded discrepancy alone `=>` finite BPA;
- naive contraction on the zero-sum hyperplane;
- unlabelled cumulative difference walk as a complete state invariant;
- a unit-determinant-only Rauzy argument presented as general.

### 4.3 Live Level-2 target: G1b-2

The stronger Level-2 program is

```text
G1b-1 bounded discrepancy [PROVED]
=> G1b-2 renewal finiteness [OPEN]
=> finite BPA / G1.
```

G1b-2 asks for a **uniform finite-return theorem for realizable labelled first-return words** within the established discrepancy bound.

The reason another norm estimate will not suffice is already visible in the exact corpus:

- maximum reachable discrepancy: **14**;
- reachable balanced-pair state length: at least **48,020**.

The structural target remains:

```text
realizable labelled first-return word
=> level-scaled contracting / Rauzy address
=> finite local return types / uniform discreteness
=> G1b-2.
```

Any successful proof must retain labels/order and must handle the non-unit internal space.

---

## 5. Primary mathematical gate: overlap productivity

### 5.1 Aligned branch

The aligned branch reduces a bad SCC to a letter pair that is not eventually coincident, together with strong endpoint-map restrictions.

Current reusable inputs:

- Barge–Diamond supplies a good-pair existence input, not a ternary all-pairs theorem.
- The repository has the hub-letter / endpoint-map normal form.
- The pair-language automaton gives a conditional least-coincidence-level bound once nonemptiness is known.
- The exact 4,554-member corpus satisfies the tested two-sided strong-coincidence condition.

The missing theorem is still a **uniform propagation/elimination result** for every ternary PIP substitution, including the reversed substitution.

Issue #138 is administratively closed, but no corresponding theorem promotion has landed in the canonical record.

### 5.2 Strict-zipper branch

This branch has seen the clearest theorem-target refinement.

The literature transfer audit now explicitly separates:

- Ito–Rao: useful unit/Pisot prefix-suffix geometric dictionary;
- Barge–Kwapisz: explicitly unimodular geometric realization;
- Akiyama–Lee: residual overlap algorithm and the hard full-growth component;
- Minervino–Thuswaldner: the correct non-unit adelic representation space;
- Barge class results: positive controls for special substitution families.

None proves the required general pointwise hit.

The residual theorem is now named:

### `AdelicPeriodicOffsetHitting` — OPEN

For a realized child-closed recurrent strict-zipper component, prove that some realized overlap vertex `(i,j,w)` and some level `m` satisfy

```text
M^m w in P_m(i) - P_m(j).
```

Equivalently, the full adelic image of a realized periodic offset orbit must hit the actual occurrence-compatible prefix-difference cylinder.

The exact target specification now correctly includes:

- an `M`-equivariant algebraic binding into `Q(beta)`;
- non-dominant Archimedean places;
- finite places dividing `(beta)` in the non-unit case;
- occurrence-labelled prefix differences;
- exact integer/algebraic equality as acceptance;
- affine periodic-orbit replay retaining the forcing digits.

A finite cap, a closure point, positive measure, multiple covering, or an Archimedean-only collision does not close the theorem.

---

## 6. New recurrent-trim / geometric Lyapunov program

PR #161 opened a new finite-carrier proof program.

For an irreducible balanced-pair defect block `T`, define its common geometric mass `L(T)`. The candidate recurrence is

```text
L(T') = beta L(T) - tau(T -> T').
```

The proposed recurrent inequality is

```text
tau(T -> T') < (beta - 1)L(T),
```

which would force `L(T') > L(T)` and therefore exclude a directed cycle on a finite recurrent noncoincidence carrier.

This differs fundamentally from the retired Parikh-difference contraction route because `L` tracks common geometric mass, not the zero Parikh difference.

### Current finite experiment

The working study reports:

- **42/42** recurrent noncoincidence edges satisfying the candidate trim inequality across four explicit specimens;
- minimum observed growth ratio `L(T')/L(T) = 1.528`;
- **39/39** reduced recurrent edges with no genuine interior coincidence cut.

These are empirical/finite results, not a theorem.

### Missing lemmas

The current note still needs:

1. exact irreducible-child lemma;
2. suffix forcing without circularity;
3. rigorous recurrent boundary-trim bound;
4. uniform reduced recurrent size lemma;
5. canonical Mojo reconstruction of the finite experiment.

### Bridge to the shortest route

PR #162 isolates the missing implication:

```text
closed nonproductive seed-patch overlap SCC
=> bounded/recurrent ordered irreducible defect chain.
```

If proved without G1, trim growth could attack the G1-free overlap route directly. If false, a replayable unbounded-chain countermodel would cleanly separate the trim route from the shortest PSC route.

The known affine-pump and collar examples remain mandatory negative controls: recurrence of an affine overlap state does not imply recurrence of the entire ordered defect block.

---

## 7. Computational evidence

### 7.1 Exact 4,554-member ternary PIP corpus

| Measurement | Exact result |
| --- | ---: |
| Overlap graphs built / capped / failed | **4,554 / 0 / 0** |
| Total exact overlap vertices | **1,118,850** |
| Largest overlap graph | **2,640** |
| Specimens containing a nonproductive overlap | **0** |
| Maximum first-coincidence depth | **18** |
| Maximum first left-aligned depth | **17** |
| Maximum prefix strong-coincidence depth | **15** |
| Maximum suffix strong-coincidence depth | **15** |
| Ordered letter pairs decided by coincidence automata | **40,986** |
| Re-derived witnesses | **40,986** |
| Unimodular specimens | **2,628** |
| Determinant-two specimens | **1,926** |
| Unimodular specimens with zero-shift-free affine pumps | **2,598 / 2,628** |

Important consequence: the affine-pump obstruction is **not** a specifically non-unimodular pathology.

### 7.2 Determinant generalization warning

The declared 4,554 corpus contains determinant classes:

```text
-1, +1, +2.
```

The broader image-length-at-most-four screen contains **135,990** PIP specimens and determinant classes:

```text
-2, -1, +1, +2, +3.
```

Therefore determinant-two evidence must never be described as “the non-unimodular case.”

### 7.3 Arithmetic reliability

The exact cubic arithmetic audit reports zero disagreements against the independent oracle on its declared tests, including wide-magnitude Perron-sign checks.

This materially increases confidence in the finite experiments but does not turn them into universal proofs.

### 7.4 Older corroborating surveys

Historical v15-era surveys remain useful calibration:

- **6,009** irreducible Pisot specimens across alphabets 3–5 showed no strong-coincidence failure;
- **59,319** ternary substitutions were checked for UD, and all **7,491** non-UD cases had zero determinant.

These are historical/finite evidence only.

---

## 8. New contradictions, corrections, and attribution fixes

The following corrections remain binding.

| Claim / shortcut | Current verdict |
| --- | --- |
| `UD => bounded total padding` | **Withdrawn / false route** |
| padding bound => predecessor contraction => finite BPA | **Withdrawn** |
| no recurrent noncoincident cycle | **False in general** |
| recurrent noncoincident cycle => nonzero displacement | **False** |
| same coarse Parikh/offset data => same cutting | **False / information-losing quotient** |
| bad SCC should be rank deficient | **Wrong direction; bad SCC is full rank** |
| residual component must satisfy `rho < beta` | **False shortcut; `rho=beta` is the hard case** |
| Barge–Diamond gives ternary all-pairs strong coincidence | **Attribution error** |
| Barge–Kwapisz can be imported without unimodularity | **Attribution/hypothesis error** |
| purely Euclidean contracting space suffices in non-unit case | **Unsafe; finite-place factors may be required** |
| compactness / positive measure / multiple tiling forces the distinguished periodic hit | **Insufficient** |
| recurrence of affine overlap state => recurrence of ordered defect chain | **Unproved; negative controls exist** |
| issue closure => theorem closure | **Invalid provenance shortcut** |

### BSW attribution fix

The density-to-PDS import is now source-audited.

The Barge–Štimac–Williams Section 3 route permits periodic patches that are not necessarily legal, uses topological density of eventual coincidence, and does not add a unimodularity hypothesis to the one-dimensional argument used here.

This means Theorem 5.38's conditional sufficiency direction is on much firmer attribution footing than it was before the 2026-09-20 audit.

---

## 9. Independence and unimodularity firewall

Every future proof or import must be rejected, restricted, or explicitly downgraded if it silently uses one of the following.

| Potential leak | Required treatment |
| --- | --- |
| Seed word `ab` assumed language-legal | **Forbidden.** The periodic comparison seed need not be legal. |
| Rational/integer tile-length independence assumed independently | **Forbidden.** Derive it from irreducibility where used. |
| UD assumed independently | **Forbidden.** UD is already derived. |
| Finite BPA / G1 assumed in the G1-free overlap route | **Forbidden unless the theorem is explicitly restricted.** |
| FI / prefix-suffix permutation / boundary injectivity | **Extra hypotheses unless derived.** |
| `|det M| = 1` used as a general assumption | **Unimodularity leak.** |
| Ito–Rao unit geometry imported into the non-unit branch | **Unimodularity/unit leak.** |
| Barge–Kwapisz converse imported with “unimodular” deleted | **Unimodularity leak.** |
| Non-unit internal space replaced by a Euclidean stable plane | **Invalid unless finite-place coordinates are proved irrelevant.** |
| `pi_s(Z^A)` treated as a discrete stable lattice | **Unsafe in the required generality.** |
| Formal recurrent graph cycle treated as globally realized | **Realization shortcut.** |
| Finite corpus, collar, or depth bound treated as complete | **Computational completeness leak.** |
| `rho(N_S)=beta` treated as contradiction | **Wrong; it is the hard residual case.** |
| Full wedge span treated as productivity | **Unproved bridge.** |
| Nakaishi preprint claim treated as settled external theorem | **Attribution/status leak unless independently validated.** |

---

## 10. Current source/provenance split

This is now the highest-priority nonlocal issue in the project.

### Canonical mathematical record

The following still classify general PSC as open on `main`:

- `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`;
- `claim_governance.toml`;
- `docs/claim-status-and-source-map-2026-09-13.md`;
- `docs/conjecture-ledger.md`;
- generated proof ledger surfaces;
- `README.md`;
- `docs/research-roadmap-2026-09-21.md`;
- `docs/proof-ladder.md`.

### Project-management record

The following treated the project as having closed PSC:

- issue #151;
- the latest project-status comment on #84;
- administrative closure of #84;
- administrative closure of #138;
- Tier-2 Growth Bridge work.

### Required reconciliation

Issue #153 already states the correct acceptance criteria:

1. identify the accepted proof source;
2. establish immutable provenance;
3. audit its exact hypotheses against the standing PIP/non-unimodular target;
4. update the authoritative proof record;
5. regenerate ledger/TLA/relationship/status surfaces;
6. explicitly classify #84/#138/#139 as proved, bypassed, or still-open stronger theorems;
7. run the full verification/provenance gates.

Until that is done, “PSC closed” is a project premise, not canonical theorem provenance.

---

## 11. Source-integrity risk

The 2026-09-27 audit found literal C0 control characters in three merged theorem-facing/research Markdown notes:

| File | C0 controls |
| --- | ---: |
| `p1b-strict-zipper-literature-gate-2026-09-21.md` | **19** |
| `level3-recurrent-trim-lyapunov-2026-09-25.md` | **16** |
| `p1-overlap-trim-bridge-2026-09-25.md` | **10** |
| `p1b-adelic-prefix-difference-cylinder-2026-09-21.md` | **0** |

The corrupted positions correspond to intended commands such as `beta`, `tau`, `rho`, `times`, `frac`, `boxed`, `rangle`, and `text`.

Issue #168 tracks repair plus a regression that rejects unexpected C0 controls in mathematical Markdown.

Until repaired, copy exact equations from the clean adelic-cylinder specification or manuscript/proof sources rather than the corrupted notes.

---

## 12. Recent literature / attribution check

No newly verified 2025–2026 peer-reviewed result has been incorporated into the repository as a general proof of PSC.

The external landscape relevant to the current program remains:

- Barge–Diamond: two-letter all-pairs strong coincidence and a partial higher-alphabet result;
- Ito–Rao: Pisot-unit atomic-surface / super-coincidence machinery;
- Barge–Kwapisz: unimodular Pisot geometric realization;
- Akiyama–Lee: overlap-coincidence algorithm and residual spectral criterion;
- Minervino–Thuswaldner: non-unit Pisot geometry in an adelic representation space;
- Barge class results: special positive-control families;
- Barge–Štimac–Williams: the audited dense-eventual-coincidence-to-PDS bridge used by Theorem 5.38;
- Nakaishi 2024: claimed general-proof preprint, not currently a load-bearing imported theorem in this project.

The project should continue to distinguish “claimed proof / preprint” from an accepted theorem source.

---

## 13. Prioritized completion ledger

| Priority | Item | Status now | What would close it | Next highest-value action |
| --- | --- | --- | --- | --- |
| **P0** | Resolve project-closed vs canonical-open PSC status (#153) | **OPEN critical provenance task** | accepted proof artifact + immutable provenance + exact hypothesis audit + authoritative proof-record change + regenerated surfaces | resolve #153 before any canonical “PSC proved/closed” promotion |
| **P0b** | Repair corrupted mathematical notes (#168) | **OPEN source-integrity task** | zero unintended C0 controls + reviewed formulas + CI regression | repair the three notes and add source-integrity check |
| **P1a** | Aligned strong-coincidence obstruction | **Canonical OPEN** | uniform elimination of every aligned bad SCC, including reversal, or an accepted stronger proof bypassing it | prove the hub-star/endpoint propagation lemma from a Barge–Diamond good pair |
| **P1b** | `AdelicPeriodicOffsetHitting` (#139) | **OPEN critical mathematical target** | uniform non-unit-safe recurrence/coverage theorem forcing an actual prefix hit | attack affine periodic-orbit cylinder recurrence in the full adelic representation |
| **P1** | One-seed overlap productivity | **Canonical OPEN** | P1a + P1b or one stronger theorem excluding every bad closed SCC | assemble only after branch closure; do not replace by a larger finite sweep |
| **P2** | G1b-2 renewal finiteness | **OPEN parallel theorem** | uniform finite-return theorem for realizable labelled first returns | develop label/order-preserving non-unit address theory |
| **P3** | Recurrent-trim theorem | **CONJECTURAL / partial finite evidence** | prove irreducible-child, suffix-forcing, boundary-trim, and size lemmas | reconstruct 42-edge evidence canonically, then prove the reduced recurrent size lemma |
| **P3b** | Overlap => recurrent defect-chain bridge | **OPEN conjectural bridge** | prove bounded/recurrent ordered defect chain or exhibit decisive unbounded-chain countermodel | test known affine pump/collar examples with exact ordered-chain instrumentation |
| **P4a** | Concentration, `K2=0` | **OPEN parallel** | uniform exclusion of strict zero-wedge closed carriers | seek ordered/ancestral invariant not erased by current span data |
| **P4b** | Wedge productivity, `K2!=0` | **OPEN parallel** | theorem converting surviving recurrence/order constraints into coincidence | identify invariant beyond full rational wedge span |
| **P5** | Realization / MEF G0–G6 | **OPEN secondary bridge** | formal recurrence => global realization or uniform nonrealizability theorem | keep formal recurrence, collar survival, and realization distinct |
| **Support** | Expanded exact computation | **EMPIRICAL / finite-domain support** | cannot close PSC by itself | use larger determinant classes to falsify proposed universal lemmas |

---

## 14. Highest-value proof tasks for the next cycle

1. **Resolve #153 before changing theorem status.** This is now the single highest-value repository task because every other completion label depends on knowing what proof source the project means when it says “PSC closed.”
2. **Repair #168 immediately.** The #139 literature gate is theorem-facing guidance and must contain exact formulas.
3. **For #139, prove or falsify the smallest complete adelic recurrence lemma.** Do not add another necessary-condition sieve.
4. **For the aligned branch, target propagation rather than another census.** The useful theorem is a ternary endpoint/hub-star propagation result, not a deeper finite coincidence search.
5. **Use the recurrent-trim route as a falsifiable bridge experiment.** A bounded/recurrent ordered-chain theorem or a replayable unbounded-chain countermodel are both high-value outcomes.
6. **Keep G1b-2 active but secondary.** It remains a valuable stronger structural theorem and must retain the non-unimodular and label/order firewalls.
7. **Use computation primarily to kill bad lemmas quickly.** The corpus is now strong enough that its highest value is adversarial calibration, not another “no counterexample found” count.

---

## 15. Net assessment

The project is in a substantially sharper state than the earlier “Level 2 then Level 3” architecture.

Closed theorem-level infrastructure now includes:

- UD and UD for powers;
- G1b-1 bounded discrepancy;
- finite swap-seed overlap graphs;
- full-rank bad-SCC normal form;
- exact boundary-hitting and affine-cycle structure;
- density equivalence;
- the source-audited BSW endpoint.

The shortest mathematical gap is now concentrated into a highly specific overlap-productivity obstruction, with its strict branch narrowed to an exact non-unit adelic hitting theorem. The new recurrent-trim program offers a second potentially powerful monotonicity mechanism, but its bridge to the G1-free route is deliberately still conjectural.

The largest immediate project risk is **not** a hidden unimodularity assumption. The current firewalls are substantially improved. The dominant risk is **status provenance**: administrative/project closure has moved ahead of the canonical theorem record.

Until #153 resolves that discrepancy, the correct weekly status is:

> **Canonical theorem status: open. Tier 2 project status: active by administrative premise. Proof-source reconciliation: pending.**

## Primary repository sources for this ledger

- `docs/audit-2026-09-27.md`
- `docs/research-roadmap-2026-09-21.md`
- `docs/proof-ladder.md`
- `docs/claim-status-and-source-map-2026-09-13.md`
- `docs/conjecture-ledger.md`
- `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`
- `docs/bsw-import-literature-gate-2026-09-21.md`
- `docs/p1b-strict-zipper-literature-gate-2026-09-21.md`
- `docs/p1b-adelic-prefix-difference-cylinder-2026-09-21.md`
- `docs/level3-recurrent-trim-lyapunov-2026-09-25.md`
- `docs/p1-overlap-trim-bridge-2026-09-25.md`
- issues #44, #43, #85, #139, #151, #153 and #168
