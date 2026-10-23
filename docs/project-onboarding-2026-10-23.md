# PSC project onboarding — current status and source firewall (2026-10-23)

**Purpose:** get a collaborator operational without importing withdrawn proof claims, conflating finite evidence with universal theorems, or losing the useful material from the historical v6/v9 manuscripts, the Plastic-A programme, and the 2D Penrose pilot.

**Authority:** this is an onboarding/index document, not a proof source and not a claim-status surface. When wording here conflicts with the claim ledger, live proof ladder, roadmap, manuscript, or generated ledger surfaces, those sources control.

**Pinned live baseline for this document:** `main@c439081855cc0730a8c6e2f7e95527fb43fd7d99`.

---

## 1. Read the project as four lanes, not one proof story

The repository currently contains four kinds of material that must remain distinct.

1. **Live theorem lane.** Governed claims on `main`: the shortest seed-overlap route to PDS, the two-obstruction completion theorem, finite/family certificates, and the remaining universal obligations.
2. **Historical proof manuscripts.** In particular the externally supplied v6/v9 line. These contain reusable lemmas and useful exposition, but some global closure steps were withdrawn after counterexamples/audits.
3. **Tier-2 / post-proof research.** Plastic-A, Padovan, finite-witness/FM compression, and Growth-Bridge experiments. These are research programmes and benchmark structures, not claim-status promotions.
4. **Cross-program geometric laboratory.** The 2D Penrose pilot, whose finite-interface/collar machinery is useful for G1b-2, realization, and strict-zipper intuition but is non-load-bearing for PSC.

A collaborator should first learn the boundaries between these lanes. Most past confusion came from mixing them.

---

## 2. Live theorem lane: what `main` currently says

### 2.1 Shortest route to pure discrete spectrum

The live sufficiency chain remains

```text
primitive irreducible Pisot
=> bounded discrepancy                                  [PROVED]
=> finite seed-patch overlap graph                      [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN]
=> coincidence density one / dense good set             [PROVED]
=> pure discrete spectrum                               [IMPORTED]
```

The open premise is the one-seed form of **seedwise overlap productivity** (issue #84 / Open Problem 5.35 context). It is stronger to prove productivity from every swap seed or for every potential overlap; those stronger forms are useful, but they are not required by Theorem 5.38.

### 2.2 Two-obstruction completion theorem

For ternary PIP substitutions, the repository has reduced the universal completion problem to two named obligations:

- **#138 / A1′ — aligned branch:** the residual fixed-letter hub-word pair is eventually coincident.
- **#139 / BH — strict-zipper branch:** every cyclic strict-zipper overlap has an occurrence-compatible descendant of offset zero.

The manuscript's two-obstruction completion theorem says that universal A1′ plus universal BH imply seed-overlap productivity and therefore PDS in the standing regime.

**Issue-status repair (2026-10-23):** GitHub issue #139 was erroneously closed
as completed despite the still-open universal BH quantifier; it is now **open**.
Closing an implementation PR or certifying a parameter family does not close the
universal theorem. The [reconciliation note](issue-139-tracker-mathematics-reconciliation-2026-10-23.md)
records the closure/reopening provenance, exact acceptance criterion and
remaining scope. This is a tracker correction only, not an accepted PSC step.

**Historical #138 status (verified 2026-10-23):** #138 was closed
2026-09-26 and already reopened 2026-10-01. It is **open now**; no duplicate
reopening action was necessary. The live two-obstruction theorem needs only
the **one-sided A1′ residual hub-edge statement**, not the issue's older
stronger two-sided goal. See [the #138 historical tracker audit](issue-138-tracker-history-2026-10-23.md).
Neither historical issue closure nor the narrower reduction constitutes proof.

These are universal obligations. Family certificates, bounded-domain censuses, residue-ray certificates, and line/wedge theorems do not silently promote them.

### 2.3 Stronger structural routes

The project keeps several parallel programmes because they expose reusable structure:

- **G1b-2 renewal finiteness -> finite BPA (G1).**
- **All-seed overlap productivity -> finite BPA** by the overlap-depth route.
- **All-seed strict-zipper exclusion -> finite BPA** by the half-coincidence route.
- **Finite-BPA carrier route:** concentration / wedge-productivity / SCC Producer.
- **Realization / MEF route:** formal recurrence, global realization, and collar survival are kept distinct.

These routes are useful, but the direct seed-overlap route does not require solving all of them first.

---

## 3. Stable base a new collaborator can rely on

The following are part of the settled base at their recorded scopes.

### 3.1 Unique decodability

Full incidence rank gives unique decodability through the classical defect theorem. The same argument applies to every power because `det(M^r) != 0`.

This is the correct way to salvage the clean v6/v9 insight:

```text
full incidence rank
=> image words form a code
=> sigma is UD
=> every power sigma^r is UD.
```

UD is derived; it is not an extra standing hypothesis.

### 3.2 Local hierarchy inside a specified supertile

UD for powers gives a useful local statement:

> Once a level-`n` supertile is specified, its lower-level substitution hierarchy is uniquely determined.

This is a legitimate witness/hierarchy lemma. Its scope is local to the specified supertile.

Do **not** upgrade it to a claim that one supertile determines the whole bi-infinite tiling, or that a recurrent noncoincident cycle is thereby impossible.

### 3.3 Bounded discrepancy and finite seed-overlap graph

The repository independently proves bounded discrepancy in the non-unimodular standing regime and then derives a finite exact seed-patch overlap graph.

This graph is the finite object used by the shortest route. The missing theorem is productivity/eventual coincidence on that finite represented universe, not finite coverage itself.

### 3.4 Density-to-PDS import

The repository side proves the coincidence-density / dense-good-set equivalence, and the Barge–Štimac–Williams theorem is imported with its hypotheses audited.

Thus the current bottleneck is before the final spectral step.

---

## 4. v6/v9 extraction firewall

The historical manuscripts are valuable, but must be read through the repository audit.

### Keep

- concise UD proof via full incidence rank / defect theorem;
- UD for powers;
- unique lower-level hierarchy inside a specified supertile;
- Plastic-A as an exact benchmark specimen;
- finite-witness constructions as research objects when their scope is stated exactly.

### Do not import as live closure claims

- `UD => bounded total padding => finite BPA`;
- the withdrawn predecessor-contraction proof of G1;
- universal exclusion of recurrent noncoincident BPA cycles;
- global pointed-realization injectivity from one common supertile;
- diameter-only witness preservation.

The diameter point is especially important: a displacement smaller than a supertile diameter does **not** by itself imply that two points lie in the same supertile; they can straddle a boundary.

The repository's v9 extraction audit is the canonical reference for this split.

---

## 5. Current obstruction normal form

If overlap productivity fails, the repository can pass to a finite child-closed recurrent nonproductive obstruction with strong algebraic constraints.

The useful picture is:

```text
bad overlap set
=> finite child-closed recurrent obstruction
=> aligned / offset-zero branch
   OR
   strict no-tie prefix-grid zipper branch.
```

Important supporting facts include:

- full rational rank of the bad-set intersection-vector span;
- inherited Galois spectrum constraints;
- exact ordered affine child recurrence `w' = M w + q - p`;
- boundary-hitting / common-left-endpoint criteria;
- occurrence and collar firewalls preventing symbolic pumping from being inferred from affine-state equality alone.

Bare cycle recurrence is not a contradiction. The project has exact productive recurrent cycles and other negative controls showing why occurrence data and the full representation-space hypotheses matter.

---

## 6. Exact finite and family evidence: how to use it

Finite certificates are genuine theorems on their declared domains, but they are not universal closure.

A collaborator should know three representative scales.

### 6.1 Standing exact corpus

The repository uses an exact 4,554-member ternary PIP short-image corpus for many regressions and structural censuses.

### 6.2 Theorem Omega finite-domain PDS certificate

The complete box-automaton certificate proves PDS on exactly **145,806** ternary PIP substitutions in the union of the declared bounded domains.

This is a finite-domain theorem with explicit executable certificates.

### 6.3 Infinite family theorems

The repository now contains many exact line, wedge, residue-ray, and determinant-two family theorems, including substantial class-A/C/D boundary-hitting progress.

Their purpose is twofold:

1. settle large explicit infinite subclasses;
2. expose the algebraic normal forms needed for the remaining universal theorem.

Never turn “all members of this family are certified” into “#139 is proved” unless the family cover itself is universal and that coverage has been proved.

---

## 7. Plastic-A / Padovan: Tier-2 benchmark lane

The Plastic-A note is intentionally a research/conjecture programme, not a proof source.

Use

```text
1 -> 2
2 -> 3
3 -> 12.
```

Verified benchmark facts include:

- coincidence horizon 12 on the canonical deep chain;
- exact span law `span(k) = beta^(k+3)`;
- Padovan word-length recurrence;
- threshold relation `n_0 = H + 3` on that chain;
- radius-0 FM witness nontrivial mod 2 at every tested deep-chain transition;
- radius-1 centered multiset profile separates every tested deep-chain state.

The useful research questions are about:

- root/iterate normalization of deep horizons;
- FM witness compression;
- least detecting primes;
- higher-alphabet adversarial families;
- the relation between exact algebraic recurrence and finite quotient dynamics.

Padovan controls the quantitative benchmark. It is not a load-bearing ingredient of the live PSC proof.

---

## 8. Tier-2 bridge taxonomy: Descent versus Growth

The repository's Tier-2 bridge note gives a useful mechanism distinction.

### Descent Bridge

```text
finite exhaustive state universe
+ eventual confinement
+ well-founded noncoincident rank
=> eventual coincidence.
```

This is a termination mechanism.

### Growth Bridge

```text
finite represented overlap universe
+ packet factorisation / recurrence
+ lifted exact arithmetic cocycle with uniform positive growth
=> spectral or phase-locking obstruction.
```

This mechanism allows recurrence in the finite quotient. The growth object lives on a lifted exact state, not necessarily on the recurrent quotient itself.

This distinction matters for #139 because the repository already knows that bare affine recurrence and bare cycle exclusion are insufficient. Growth-Bridge work must identify the exact lifted arithmetic quantity and the exact contradiction it creates.

The bridge note moves no theorem status.

---

## 9. 2D Penrose pilot: what transfers and what does not

The Penrose programme is best used as a geometric finite-interface laboratory.

### 9.1 Source-grounded pilot facts

- `D0,...,D4` are five **unoriented** line-direction classes.
- Robinson triangles `A,B` are the prototiles.
- `A -> A+B`, `B -> A+2B`, with PF eigenvalue `phi^2`.
- parent orientations, positive child-placement rows, and boundary partitions are source-grounded.

### 9.2 Mechanically derived pilot facts

- `Q_L(B2) = phi^2 + 1`;
- reflected `epsilon=-` rows;
- `I_oriented_1`;
- process-level `I_side`;
- prefix-level continuation data for `I_oriented_2`.

These are derived project outputs, not source-verbatim facts.

### 9.3 Open Penrose targets

- full continuation of `I_oriented_2`;
- rhomb<->triangle aggregation writeup `G2D-1`;
- strict-growth invariant `Phi` (`G2D-2`).

### 9.4 Strongest PSC analogies

The repository bridge identifies the strongest transfers as:

- residual interface patch <-> realizable labelled first return / G1b-2;
- collar propagation <-> finite local return type;
- formal interface vs legal/global patch <-> PSC realization firewall;
- strict-growth `Phi` <-> a possible monotone-potential mechanism;
- separator hitting <-> #139 boundary intuition.

These are analogies and experimental transfers only. Penrose does not supply an adelic/non-Archimedean boundary-hitting theorem for PSC.

---

## 10. Superseded onboarding summaries

Two assistant-generated summaries from the source-compression thread should **not** be used as current status documents:

- `PSC_project_up_to_speed_briefing`;
- `PSC_project_onboarding_memo_tight`.

Their useful ideas are retained here only after applying the live repository firewall.

In particular, do not use these older summary claims without rechecking `main`:

- “the finite-witness contradiction is the settled live proof core”;
- “recognizability plus coarse ancestry closes recurrent noncoincident cycles”;
- the unproven diameter-only preservation step;
- the 19,953 / 3,060 survey as a canonical current corpus;
- Trib-excess-A as a source-backed project specimen without separate provenance.

---

## 11. Working queue for a new collaborator

### Live universal lane

1. Read the current roadmap, proof ladder, and two-obstruction theorem.
2. Keep #138/A1′ and #139/BH distinct until a theorem joins them.
3. Preserve occurrence compatibility, non-unit representation-space data, and the exact hypothesis firewall.
4. Use current line/wedge/residue certificates to search for a finite parametric cover or a uniform descent/hitting theorem.
5. Treat finite and family certificates as exact scoped theorems, never as implicit universal coverage.

### Parallel structural lane

1. Continue G1b-2 renewal-finiteness work where a finite-return theorem is the actual target.
2. Use collars and realization data only with explicit local/global scope.
3. Retain counterexamples to bare pumping, bare recurrence exclusion, and projected-state sufficiency.

### Tier-2 lane

1. Continue Plastic-A / FM / Padovan benchmark research.
2. Build exact loop-gain and lifted-cocycle fixtures for the Growth Bridge.
3. Use the Penrose `Phi` programme as an independent finite-interface laboratory.
4. Promote only dimension-independent exact kernels to shared infrastructure.

---

## 12. Minimal reading order

For fastest onboarding:

1. `README.md` — current headline and implementation policy.
2. `docs/research-roadmap-2026-09-21.md` — live completion roadmap.
3. `docs/proof-ladder.md` — shortest honest dependency chain.
4. `docs/claim-status-and-source-map-2026-09-13.md` — status/source authority.
5. `manuscripts/PSC_balanced_pair_state_2026-09-13.tex` — full theorem statements.
6. `docs/v9-extraction-audit-2026-09-23.md` — historical-manuscript salvage firewall.
7. `docs/tier2-bridge-salvage-2026-09-23.md` — Descent/Growth distinction.
8. `docs/post-proof-padovan-plastic-a-conjectures-2026-09-23.md` — Tier-2 benchmark programme.
9. `docs/bridges/penrose-2d-to-psc-interface-program.md` — 2D interface laboratory.
10. `docs/side-notes-ledger.md` — negative controls and failed routes before inventing a new mechanism.

---

## Bottom line

The project is easiest to understand when its authority planes remain explicit:

```text
live governed theorem lane
!= historical proof manuscripts
!= finite/family computational evidence
!= Tier-2 benchmark research
!= Penrose cross-program analogy.
```

The historical finite-witness material remains valuable, but only after the v9 firewall. Plastic-A and Growth-Bridge work remain valuable, but as Tier-2 research. Penrose remains valuable, but as a geometric interface laboratory. The live universal PSC work is governed by the current overlap-productivity / A1′ / BH architecture and its exact status surfaces.
