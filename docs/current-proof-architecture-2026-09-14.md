# Current PSC proof architecture — 2026-09-14

**Canonical architecture summary.** For theorem status and provenance use `docs/claim-status-and-source-map-2026-09-13.md`; for the weekly evidence/priorities snapshot use `docs/completion-ledger-2026-09-14.md`; for full statements use `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`.

## Headline

The shortest current route to pure discrete spectrum is G1-free and has one open premise:

```text
PIP
=> G1b-1 bounded discrepancy                         [PROVED]
=> finite seed-patch overlap graph                   [PROVED]
=> productive overlaps from one legal swap seed      [OPEN: Open Problem 5.35]
=> coincidence density one / dense good set          [PROVED]
=> PDS                                                [IMPORTED: Barge–Štimac–Williams]
```

G1b-2, finite BPA, concentration, wedge productivity, SCC Producer, and the realization/rank bridge all remain open in their respective programmes. They are not hidden assumptions of manuscript Theorem 5.38.

## Primary gate — seedwise overlap productivity

For every primitive irreducible Pisot substitution, prove that there is a legal pair `a != b` such that every exact overlap reachable from the seed overlaps of `(ab,ba)` is productive.

The graph on which this is asked is already finite. A hypothetical counterexample therefore contains a finite reachable child-closed nonproductive set `S`.

Current constraints on such an `S`:

1. **Full rank (PR #76).** The span of its intersection vectors is a nonzero rational `M_sigma`-invariant space; irreducibility forces full rank, and the child-count matrix inherits the Galois spectrum of `M_sigma`.
2. **Endpoint alignment (PR #82).** Offset-zero and right-aligned seed overlaps are exactly the prefix/suffix strong-coincidence cases.
3. **Boundary-hitting criterion (PR #82).** An overlap reaches offset zero at level `m` iff `M^m w` is a difference of proper-prefix Parikh vectors, equivalently iff inflated descendants have a common left endpoint.
4. **Strong finite evidence.** In the exact 4,554-member corpus, all 1,118,850 overlap vertices are productive; largest graph 2,640; largest first-coincidence depth 18; first left-aligned depth at most 17; prefix/suffix strong-coincidence depth at most 15.

The preferred next theorem is a minimal-bad-set contradiction combining full rank, ordered descendant structure, prefix-Parikh boundary avoidance, and Pisot contraction.

## Stable base

### Unique decodability

UD and UD for powers are repository-proved consequences of full incidence rank / the defect theorem. They are not standing assumptions.

### Bounded discrepancy

G1b-1 is repository-proved by the PR #69 reconstruction using primitivity and the Pisot spectrum. It neither assumes unimodularity nor proves finite BPA.

### Finite overlap graph

PR #72 converts bounded discrepancy into an explicit finite set of exact seed-patch overlap types. This is the finite object used by the primary route.

### Density to PDS

Lemma 5.36 proves the repository side of the density condition. PR #77 imports the Barge–Štimac–Williams theorem with its hypotheses audited in the standing PIP regime. Therefore density-to-PDS is no longer an open bridge on this route.

## Parallel programme A — G1 / BPA finiteness

```text
G1b-1 bounded discrepancy [PROVED]
=> G1b-2 renewal finiteness [OPEN]
=> finite BPA (G1).
```

G1b-2 remains the exact missing theorem for finite BPA. The target is a realizability/renewal statement for labelled first-return words, not another bounded norm. Any contracting-address proof must handle non-unimodular substitutions and may not treat the stable projection of the integer module as a lattice.

## Parallel programme B — finite-BPA closed carriers

Under G1:

```text
nonproductivity
=> finite closed/sink recurrent carrier
=> K2 == 0 or K2 != 0
=> concentration [OPEN] or wedge productivity [OPEN]
=> SCC Producer.
```

The degree-two carrier-span theorem is repository-proved. Full span alone does not imply productivity. The two 4,554-corpus exclusion certificates remain finite-domain theorems only.

## Parallel programme C — realization / MEF

The realization/coincidence-rank chain is an audited open bridge with obligations G0–G6. Formal recurrence, global realization, and survival to a finite collar are not interchangeable. This route is useful for certification/reformulation but is not required by the primary overlap theorem.

## Generality firewall

A valid general PSC proof must not silently add any of the following:

- rational/integer tile-length independence as an independent hypothesis;
- UD as an independent hypothesis;
- finite injectivity or prefix/suffix permutation hypotheses;
- unimodularity `|det M|=1`;
- purely Euclidean internal-space assumptions in a non-unimodular step;
- discreteness of `pi_s(Z^A)`;
- global realization of a formal recurrent component;
- completeness of a finite corpus or collar bound without an independent theorem.

## Priority order

1. **Overlap productivity / minimal bad overlap set.** Current shortest-path gate.
2. **G1b-2 renewal finiteness.** Stronger independent BPA theorem.
3. **Concentration and wedge productivity.** Alternative finite-BPA SCC route.
4. **Realization bridge.** Secondary certificate route.
5. **Status synchronization and exact certificates.** Ongoing P0 discipline.

The project should not prioritize another fixed-size carrier sieve over item 1 unless that sieve yields a uniform theorem feeding the overlap gate.
