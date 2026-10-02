# BPA versus overlap representation-control audit — 2026-10-02

**Status:** documentation-only representation-control audit. This note records a
negative result about proposed balanced-pair quantitative observables. It does
not change theorem status, does not close Open Problem 5.35 / issue #84, and
must not be imported into `claim_governance.toml` as a proved mathematical
claim. The live proof architecture remains the overlap-productivity route of
`docs/conjecture-ledger.md`, `docs/p1-two-route-map-2026-10-01.md`, and
`docs/claim-status-and-source-map-2026-09-13.md`.

## 1. Question audited

A proposed Pisot-substitution / complex-dynamics cross-walk suggested that raw
balanced-pair automaton drainage statistics might have a quantitative shadow:

- **C1:** a universal productivity-margin lower bound `margin >= 1 - gamma`,
  where `gamma = 1 - |second conjugate modulus|`;
- **C2:** determinant size `|det M|` drives exponential balanced-pair automaton
  state-count growth;
- **C3:** determinant size sets a productivity-margin level.

The audit question was whether these quantities survive a representation
change from the balanced-pair automaton (`B_sigma`) to the standard
overlap-coincidence representation. Surviving that change is a minimum
requirement before treating such statistics as dynamical invariants or as
proof-facing evidence for PSC.

## 2. Representation-control outcome

The quantitative claims do **not** survive the overlap cross-check.

Representative specimens:

| specimen | det | BPA states | overlap states |
| --- | ---: | ---: | ---: |
| Tribonacci `(01,02,0)` | `+1` | `8` | `9` |
| floor `(11,02,002)` | `+2` | `606` | `19` |
| `(21,22,102)` | `+2` | `626` | `39` |
| `(022,20,11)` | `+2` | `2308` | `42` |

The determinant-correlated blow-up is therefore a raw BPA growth effect, not an
invariant state-complexity law. The result is consistent with the standard
balanced-pair / overlap distinction: balanced pairs can grow in both number
and word length, while overlaps track geometric overlap types.

The proposed margin law also fails representation control. The same
substitution can give different margin values under the two presentations; for
example Tribonacci gives a positive BPA margin but zero overlap margin in the
cross-check. The overlap computations also produced values above `1` for some
normalizations, which is a warning that the BPA normalization is not the right
scale for that overlap transition statistic. The non-invariance conclusion does
not depend on interpreting those `> 1` values.

## 3. Disposition of the proposed claims

| Claim | Disposition | Permitted future use |
| --- | --- | --- |
| C1: `margin >= 1 - gamma` | **Retired as a representation artifact.** | May be discussed only as a BPA-specific diagnostic that failed overlap control. |
| C2: determinant-driven exponential state count | **Retired as a dynamical-invariant claim.** | May be used as an algorithmic warning about raw BPA blow-up, not as PSC evidence. |
| C3: determinant-driven margin level | **Retired with C1.** | No theorem or novelty use. |
| BPA / Yoccoz-tableau quantitative shadow | **Rejected at the level tested.** | Keep only as a structural analogy unless a representation-invariant object is defined. |

This note does **not** retire the finite-BPA route, SCC Producer target, or the
repository's overlap-productivity route. It retires only the attempted
quantitative BPA margin/determinant evidence for them.

## 4. Relation to the live proof architecture

The current proof architecture is already protected from this failure:

```text
primitive irreducible Pisot
=> bounded discrepancy                                  [PROVED]
=> finite seed-patch overlap graph                      [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN]
=> coincidence density one / dense good set             [PROVED]
=> pure discrete spectrum                               [IMPORTED theorem]
```

This representation-control audit supports keeping the overlap route as the
primary proof-facing route. It also supports keeping G1 / finite BPA and SCC
Producer as stronger parallel programmes rather than prerequisites of
Theorem 5.38.

The correct proof-facing obstruction remains a finite child-closed irreducible
nonproductive overlap SCC, split into the aligned and strict-zipper branches.
Raw BPA drainage margins do not supply a replacement for the missing forcing
lemma in either branch.

## 5. Complex-dynamics cross-walk disposition

The complex-dynamics cross-walk should be retained only in structural form.
The defensible dictionary is qualitative:

| Substitution side | Complex-dynamics side | Status |
| --- | --- | --- |
| recurrent overlap/BPA combinatorics | recurrent tableau/combinatorics | structural analogy |
| finite coincidence peeling | puzzle refinement / rigidity endpoint | analogy only |
| overlap productivity | eventual geometric coincidence/density | substitution-side theorem target |
| a priori bounds / analytic geometry | moduli and quasiconformal control | no finite-state substitution analogue supplied here |
| raw BPA margin | none | rejected as invariant |

Use "cross-walk", "dictionary", or "analogy schema" unless objects and
morphisms are explicitly defined. Do not call this a functor in repository
status surfaces.

## 6. Guardrails for future work

1. Any new quantitative balanced-pair observable must be tested against the
overlap representation before being treated as proof evidence.
2. Raw BPA state count, state length, SCC size, and drainage margin are
presentation-sensitive unless a quotient/invariance theorem is supplied.
3. Determinant effects may diagnose implementation blow-up, especially in
non-unimodular classes, but they do not by themselves supply a dynamical
obstruction or productivity theorem.
4. Overlap statistics with transition-matrix or margin normalizations require
an explicitly justified scale before quantitative interpretation.
5. Negative representation-control results may guide proof search and novelty
language, but they do not change the status of Open Problem 5.35, G1b-2,
SCC Producer, or PSC.

## 7. Viable next direction

The useful continuation is not another numerical BPA margin law. The useful
continuation is a presentation-invariance taxonomy:

| Observable | Expected status |
| --- | --- |
| eventual coincidence/productivity | robust |
| existence of a nonproductive recurrent overlap SCC | proof-facing obstruction |
| coincidence rank | literature-controlled invariant |
| raw BPA state count | presentation-sensitive |
| balanced-pair word length | presentation-sensitive |
| BPA drainage margin | presentation-sensitive |
| auxiliary transition spectral radius | unsafe unless attached to a defined invariant quotient |

A future note can make this precise as a map between presentations
(`B_sigma`, seed-patch overlap graphs, reduced overlap quotients, SCC quotients)
and classify which observables descend through those maps.