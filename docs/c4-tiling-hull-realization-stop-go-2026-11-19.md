# Tiling-hull realization: source decision

**Status:** Source decision for the first remaining obligation of the
[conditional periodic-partner formalization](c4-periodic-partner-formalization-2026-11-19.md):
construct the legal two-sided tiling space, its translation and inflation, endpoint
predicates, metric and geometric-realization map, and discharge the local contracts
on that instance. Starting revision: `main@18b2be6de83992b796ef0e50d4bf7f099ded7a45`.
No governed claim changes.

## Exact target

Replace the abstract carriers `X`, `translate`, `f`, `AgreeRight`, `EndsAt` and
`AgreementData` of `PscVerif.PeriodicPartnerDynamics`, `PeriodicPartnerCollapse`,
`PeriodicPartnerAsymptotic` and `PeriodicPartnerDichotomy` by one concrete Lean object:

- tilings of `ℝ` by labelled half-open tiles `[x, x + ℓ a)`, for any substitution with
  nonempty images and a positive length eigenvector `Σ ℓ(σ(a)ᵢ) = β ℓ(a)`;
- legality in the standard form: every bounded patch is a translate of a set of tiles of one
  supertile `σⁿ(a)`;
- translation `T ↦ T − t`, inflation by literal placement of `σ(a)` on the `β`-scaled tile;
- endpoint predicate "a tile labelled `b` ends at `y`" and agreement on the tiles meeting an
  open window or open right ray;
- a metric on the hull.

Then prove every local field of `RightBranchLaws` and `AgreementData`, the ray-window law and
the common-tile law **for that instance**, and restate the remaining published inputs as
fields of one named bundle about that instance.

## Sources

| Source | Input and boundary |
| --- | --- |
| Barge–Diamond–Swanson, [The branch locus for one-dimensional Pisot tiling spaces](https://arxiv.org/abs/0804.0930), abstract (re-read 2026-11-19) and §2 (re-read for [#612](c4-periodic-partner-formalization-stop-go-2026-11-19.md)) | The hull carries the inflation homeomorphism, which factors via geometric realization onto a solenoid; asymptotic pairs admit a common periodicizing translation. Stated for the usual tiling topology. Imported, not proved. |
| Baker–Barge–Kwapisz, [Geometric realization and coincidence](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Theorem 4.2 | The realization map, its semiconjugacy and finite fibres. The construction uses the Pisot contraction and an inverse-limit target; nothing in this target supplies it. Imported, not constructed. |
| Barge–Diamond, [Cohomology in one-dimensional substitution tiling spaces](https://arxiv.org/pdf/math/0702669), §§2–3 | Legal bi-infinite tilings, inflation and endpoint dynamics; matches the definitions above. |
| Mossé (1992), *Puissances de mots et reconnaissabilité des points fixes d'une substitution*, TCS 99; Solomyak (1998), *Nonperiodicity implies unique composition for self-similar translationally finite tilings*, DCG 20 | Recognizability: inflation is injective on the hull of an aperiodic primitive substitution. Bibliographic citation only; the texts were **not re-opened** in this session. Imported as a named field. |
| Anderson–Putnam (1998), *Topological invariants for substitution tilings and their associated C\*-algebras*, ETDS 18 | The usual (translation-tolerant) tiling metric and compactness of the hull. Bibliographic citation only, **not re-opened**; used only to state what the metric below is *not*. |

## Hypotheses that transfer, and those that do not

- **Transfer, proved locally.** Endpoint uniqueness, ray-to-endpoint agreement,
  translation/inflation transport, restriction and one-step inflation of agreement, the
  ray-window law and the full-length common tile are elementary facts about the
  literal tile sets. They are to be proved, not assumed.
- **Metric.** The usual tiling metric allows small translations; its triangle inequality and
  compactness are substantial. The contracts only need a metric whose small balls are
  controlled by exact centred agreement. Decision: use the exact-agreement ultrametric
  `(1/2)^N` (first disagreeing natural radius `N`). It dominates the usual metric, so
  collapse in it implies collapse in the usual one; its topology is finer, translation is not
  continuous, and compactness fails. Neither continuity nor compactness is used.
- **BDS in this metric.** In the ultrametric, metric translation-asymptoticity coincides with
  exact right-ray agreement (to be proved). Exact ray agreement implies asymptoticity in the
  usual metric, so the published BDS theorem implies the input in either form.
- **Do not transfer.** Recognizability, BDS periodicization, the realization map with its
  finite fibres, and (R4) need the Pisot/primitive hypotheses and non-local arguments. They
  stay named fields of `PublishedInputs`, never Lean axioms.

## Controls

Nonvacuity: prove a general nonemptiness theorem from a finite seed that tiles an interval
around the origin, grows under a power of inflation and is legal; instantiate it for
Thue–Morse (aperiodic, primitive; explicitly not irreducible Pisot).

## Decision

**Proceed** with the hull, its dynamics, predicates, ultrametric, all local contracts and the
instantiated consumers. **Defer** the geometric-realization construction: it needs the Pisot
contraction, recognizability and an inverse-limit target, and no part of it is local. It
stays an explicitly unconstructed field.
