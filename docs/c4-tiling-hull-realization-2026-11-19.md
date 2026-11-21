# The legal tiling hull as an instance of the periodic-partner contracts

**Status:** Lean now constructs the legal two-sided substitution tiling hull with
translation, inflation, endpoint and agreement predicates and an exact-agreement metric. It
proves every local contract of the [conditional periodic-partner formalization](c4-periodic-partner-formalization-2026-11-19.md)
for that instance. Lemma M and its periodic non-merging corollary hold on the hull with no
external input. The **geometric-realization map is not constructed.** Recognizability, BDS
periodicization, realization with finite fibres, and (R4) remain named published inputs
about this concrete hull. Independent human review is pending. C4 and PSC remain open;
no governed claim changes.

Starting revision: `main@18b2be6de83992b796ef0e50d4bf7f099ded7a45`.
[Source decision](c4-tiling-hull-realization-stop-go-2026-11-19.md).

## What is constructed

Module [`PeriodicPartnerHull.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerHull.lean),
for any `LengthSubst α`. This is a substitution `σ` with nonempty images, lengths `ℓ > 0`
and `Σ ℓ(σ(a)ᵢ) = β ℓ(a)`.

| Object | Definition |
| --- | --- |
| Tile, support | `(a, x)` occupies `[x, x + ℓ a)` (`supp`) |
| `place w x` | `w` laid out left to right from `x` |
| `inflate T` | every `(a,x) ∈ T` is replaced by `place (σ a) (β x)` |
| `shift t T` | `T − t` |
| `IsTiling` | every `z ∈ ℝ` lies in exactly one tile |
| `Legal` | every patch meeting `(-R,R)` is a translate of a subset of a supertile `inflateⁿ {(a,0)}` |
| `Hull` | legal tilings; `translate`, `inflateH` act on it (closure proved) |
| `EndsAt T y b` | `(b, y − ℓ b) ∈ T` |
| `AgreeRight T U y`, `Agree R T U` | same tiles among those meeting `(y,∞)`, resp. `(-R,R)` |
| metric | `dist T U = (1/2)^N`, `N` the first natural radius with differing patches (via `PiNat`) |

The metric is the exact-agreement ultrametric, not the usual translation-tolerant tiling
metric. It dominates the usual metric, has a finer topology, does not make translation
continuous, and does not make the hull compact. None of those properties is used.

## What is proved

| Theorem | Content | External input |
| --- | --- | --- |
| `isTiling_inflate`, `legal_inflate`, `isTiling_shift`, `legal_shift` | the hull is closed under inflation and translation | none |
| `inflate_shift`, `translate_injective` | `inflate (T − t) = inflate T − βt`; translations are injective | none |
| `rightBranchLaws` | all seven fields of `RightBranchLaws inflateH translate β g_R AgreeRight EndsAt`, `g_R` = last letter | none |
| `agreementData` | `AgreementData Hull inflateH β`: restriction, inflation of radius, metric modulus | none |
| `window_of_ray`, `common_patch` | a ray from `≤ −R` gives centred agreement `R`; a common ray at `0` and a common origin endpoint `a` give agreement of full radius `ℓ a` | none |
| `rightAsymptotic_iff_translationRightAsymptotic`, `bds_ray_iff_metric` | in this metric, translation-asymptoticity **is** exact right-ray agreement; the two BDS forms coincide | none |
| `distance_tendsto_zero_of_endpoint_merge` | Lemma M on the hull, any alphabet | none |
| `endpoint_persistent_of_periodic` | distinct periodic tilings with a common ray at a common origin endpoint never merge labels | none |
| `hull_endpoint_merge_iff_collapse`, `hull_two_step_iff_pairPeriodic` | ternary two-step test ⇔ collapse, ⇔ joint periodicity | BDS only |
| `hull_two_step_iff_zero_fibre`, `hull_branch_triple_dichotomy` | Lemma E and the triple dichotomy on the hull | `PublishedInputs` |
| `hull_nonempty_of_seed` | a seed tiling `[x,y) ∋ 0`, contained in its `k`-fold inflation and legal, generates a hull element | none |
| `thueMorse_hull_nonempty` | the construction is not vacuous | none |

`PublishedInputs S Y` has these fields: `inflate_injective` (recognizability: Mossé, Solomyak);
`bds` (metric form, equivalent here to the ray form); `realize`, `A`, `semiconj`,
`finite_fibres` (Baker–Barge–Kwapisz realization); and `q₀`, `q₀_fixed`, `r4`. Every one is a
structure field. None is a Lean axiom, and every compiled declaration uses only `propext`,
`Classical.choice` and `Quot.sound`.

## Non-claims and remaining gaps

1. **Geometric realization is not constructed.** It needs the Pisot contraction, an
   inverse-limit/solenoid target in the nonunit case, and recognizability. It remains the
   field `PublishedInputs.realize` with its semiconjugacy and finite fibres.
   *Update:* the [realization note](c4-geometric-realization-2026-11-19.md) constructs it into the
   solenoid under `PisotData` and bijective inflation, with semiconjugacy, flow equivariance and
   (R4) proved; finite fibres remain an input.
2. **Published theorems are not proved.** Recognizability, BDS, finite fibres and (R4) are
   supplied as fields. Primitivity and the Pisot property are hypotheses of those
   theorems. They are not fields of `LengthSubst`, whose local contracts need neither.
3. **The usual tiling metric is not constructed.** Results stated with the ultrametric
   transfer to it in the direction used (collapse), but compactness arguments of the written
   notes cannot be replayed on this metric.
4. **The joining relation is not instantiated.** Lemma P on the hull still needs the strict
   relation `Z` and its consequences of Z1, Z2 and Z4.
5. **Nonemptiness for PIP3 members is not instantiated.** `hull_nonempty_of_seed` applies
   once a legal growing seed and the real eigenvector are supplied. Only Thue–Morse is
   checked.
   *Update:* [closed](c4-hull-nonempty-2026-11-21.md). The seed exists whenever `1 < β`, so
   every PIP3 member, every census specimen and Tribonacci has a nonempty hull.
6. The left-hand consumers of `PeriodicPartnerReflection` are not re-instantiated. The
   right-hand laws transfer through the existing reflection theorems once a reflected hull
   map is supplied.

Witness selection under (NM_V) and the global rank-two contradiction (gaps 2 and 3 of the
formalization note) are untouched.

## Replay

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

The scoped gate builds `PscVerif.PeriodicPartnerHull` with the other periodic-partner modules
from fresh sources and audits every compiled declaration.
