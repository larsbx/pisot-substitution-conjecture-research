# Ordinary topology on the legal tiling hull

**Status:** the fresh scoped build and compiled axiom audit pass. The four
new modules add 44 named Lean proofs. They give the existing legal tilings their ordinary
local topology, identifies its neighbourhoods by small translations and
exact agreement on large windows, and proves continuity of translation and
inflation. A separate criterion reduces continuity of an equivariant map
to continuity on the exact-agreement presentation. It does not establish
continuity of the concrete geometric realization.

Starting revision: `ec026774e666fb8e8ac43b1ba975b9a4df8891b2` (PR #623).
The [pre-code source decision](c4-ordinary-hull-topology-stop-go-2026-11-19.md)
compares the construction with Baker–Barge–Kwapisz, Barge–Diamond–Swanson,
and Barge–Diamond. This is a formalization of the standard topology on
one-dimensional tiling spaces; no mathematical novelty is claimed. No
governed claim changes, and C4 and PSC remain open.

## Work shown

### Assumptions and hypotheses

| Object or premise | Role and scope |
| --- | --- |
| `LengthSubst alpha` | The existing substitution, with positive tile lengths, nonempty image words and the length-eigenvector equation. |
| `S.Hull` | The existing carrier of legal tilings by labelled half-open intervals. It retains its exact-agreement metric and all existing consumers. |
| `LocalHull S` | A wrapper for precisely the same tilings, with a separate topology. It introduces no new tilings, legality predicate or geometric identification. |
| `[Nonempty alpha]` | Used for inflation, through the already proved positivity of `S.beta`. The topology and translation arguments do not require a finite alphabet. |
| A continuous target flow and equivariance | Used only in `continuous_iff_exact_of_equivariant`, for an arbitrary map to an arbitrary topological target. |

No recognizability, primitivity, Pisot contraction, determinant condition,
compactness, finite fibres or BDS periodicization is assumed in the new
topology results. In particular, no assumption that inverse inflation is
continuous is inserted.

### Derivation / reduction

#### 1. Exact agreement supplies the transverse topology

`PeriodicPartnerHullContinuity` works with the existing exact metric.
Agreement on radius `R + abs(t)` implies agreement on radius `R` after
translating both tilings by the fixed time `t`. Inflation carries radius
`R` agreement to radius `beta * R` agreement. Together with the existing
metric bounds, these give `uniformContinuous_translate` and
`uniformContinuous_inflateH`.

Translation by `-t` is the inverse of translation by `t`, producing
`translateHomeomorph` for each fixed `t`. This says nothing about
continuity as the time parameter varies. The natural-radius agreement
cylinders are open and form a neighbourhood basis, as recorded in
`isOpen_agreement` and `nhds_agreement_basis`.

#### 2. The ordinary topology is an open quotient

`PeriodicPartnerLocalTopology.chart` sends `(t,T)` to the tiling `T - t`,
viewed as `LocalHull S`. The new topology is coinduced by this map from
`Real x S.Hull`. Surjectivity follows from the representative `(0,T)`.

For a fixed `s`, changing the representative by

`fibreShift s (t,T) = (t+s, translate (-s) T)`

preserves its image. This change is continuous because the translation in
its second coordinate is fixed. `chart_saturation` identifies the
preimage of the image of any set `U` with the union, over all `s`, of
`fibreShift s` preimages of `U`. For open `U`, each of those preimages is
open. Hence the chart is open, and `isOpenQuotientMap_chart` provides an
open quotient map, not only a surjection with a chosen topology.

The map `ofExact` is the identity of carriers from the old presentation to
the new one, and `continuous_ofExact` follows by composing the chart with
`T -> (0,T)`. This is the direction from the finer exact topology to the
ordinary topology.

#### 3. The neighbourhood basis matches the ordinary tiling definition

For `epsilon > 0` and a natural radius `n`, `patch S T epsilon n` consists
of tilings `U` for which some `t`, with `abs(t) < epsilon`, satisfies

`Agree n T.toHull (translate (-t) U.toHull)`.

Equivalently, it is the chart image of the product of the time ball about
zero and the exact agreement cylinder about `T`. `patch_eq_image` proves
this equivalence, `isOpen_patch` proves openness, and
`nhds_patch_basis` proves these sets form a neighbourhood basis.
`mem_nhds_iff` and `isOpen_iff` give the corresponding explicit criteria.
This identifies the coinduced topology with the usual small-translation,
large-window topology. The identification does not rest on naming the
new type an ordinary hull.

#### 4. Translation and inflation descend continuously

For translation, take the product of the identity on `Real` with the
open quotient chart. Products of open quotient maps remain quotient maps.
After composition with this map, the proposed action is

`(s,(t,T)) -> chart (s+t,T)`,

which is continuous by addition and `continuous_chart`. The quotient
criterion gives the jointly continuous action `continuous_translate` on
`Real x LocalHull S`. It also gives a `translateHomeomorph` at each fixed
time in the new topology.

Inflation obeys `inflate_chart`: inflating `chart (t,T)` yields
`chart (beta*t, inflateH T)`. The map on this chart domain is continuous
by scalar multiplication and the exact-source inflation theorem, so
`continuous_inflate` follows by the same quotient criterion. Neither
injectivity nor a continuous inverse follows from this statement.

#### 5. Equivariant continuity has a precise remaining obligation

For `f : LocalHull S -> Y`, a jointly continuous target flow, and the law
`f (translate t T) = flow t (f T)`, the theorem
`continuous_iff_exact_of_equivariant` states

`Continuous f <-> Continuous (f composed with ofExact S)`.

The forward direction uses `continuous_ofExact`. For the converse,
composition with the chart is `(t,T) -> flow t (f (ofExact S T))`;
continuity of the target flow and the exact-source map lets it descend.
The theorem is applicable to future realization work, but it does not
supply exact-source continuity of the existing realization. Its series,
desubstitution histories and changes of the origin tile still require
that separate proof.

`PeriodicPartnerLocalRealization` applies this criterion to the existing
concrete solenoid map. `realizeLocal` is exactly `realize` on the wrapped
carrier, and `realizeLocal_inflate` and `realizeLocal_translate` preserve
the existing identities. `continuous_realizeLocal_iff` proves that its
ordinary-hull continuity is equivalent to exact-source continuity. This
adapter retains `PisotData`, bijective inflation and `beta > 1` where the
existing flow-equivariance theorem requires them; it supplies neither
side of the continuity equivalence as an unconditional theorem.

### Evidence and replay

The unchanged canonical periodic-partner gate rebuilt the complete local
import closure from fresh sources and pinned dependency checkouts, using
only selected upstream source-hash cache artifacts. It reused no local
project objects. The compiled audit verified **24 modules, 1,458
declarations, 1,068 theorem declarations and all 577 source-named
proofs**, including the **44 new named proofs** in this increment. Every
compiled declaration uses only `propext`, `Classical.choice` and
`Quot.sound`; no additional axiom is accepted.

All 236 source and pin bindings were rechecked after dependency cloning,
upstream cache restoration, compilation and the compiled audit. Their
canonical snapshot SHA-256 is
`7bee0352555808162025eb1c3596ee278b90d5482348a1512bf5b0cdebbd45d8`.
The verified local source checkpoint is
`9fb7c7d7f528f3ccf35d9f393dc050d063e26762`; the published checkpoint is
`f407bd05f4ca12603e78026a08b7058e18e09cea`. Both have tree
`5d4cdfca23cac14478efd5a84c3bd4813cb0016b`. Subsequent documentation and
evidence packaging leave all checked Lean sources and gate support unchanged.

The [evidence packet](../evidence/ordinary-hull-topology-2026-11-19/README.md)
contains the lossless gate log, terminal receipts, exact source bindings
and repository-check records. All 252 focused regression tests pass; the
generated proof inventory, generated ledger, claim-governance audit and
Markdown-source checks also pass. The compiler is Lean 4.34.0-rc2 and mathlib
is pinned to `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.

| Module | Verified statements |
| --- | --- |
| [`PeriodicPartnerHullContinuity.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerHullContinuity.lean) | Exact agreement laws, fixed-translation homeomorphisms, uniform continuity of inflation, and the exact agreement neighbourhood basis. |
| [`PeriodicPartnerLocalTopology.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerLocalTopology.lean) | Chart saturation and open quotient, ordinary patch neighbourhoods, joint translation continuity, inflation continuity, and the equivariant continuity criterion. |
| [`PeriodicPartnerLocalTopologyControls.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerLocalTopologyControls.lean) | Small exact translations must be zero; arbitrarily small positive translates fail radius-one agreement; exact-topology orbit maps are discontinuous at zero; ordinary orbits are continuous and the reverse carrier projection is not. |
| [`PeriodicPartnerLocalRealization.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerLocalRealization.lean) | The unchanged concrete realization on the ordinary presentation, its equivariance, and the exact iff between its two continuity obligations. |

Direct module replay:

```sh
cd proof/PscVerif
lake build PscVerif.PeriodicPartnerHullContinuity \
  PscVerif.PeriodicPartnerLocalTopology \
  PscVerif.PeriodicPartnerLocalTopologyControls \
  PscVerif.PeriodicPartnerLocalRealization
```

The focused periodic-partner gate and compiled inventory include all four
new modules. Its full fresh replay command is
`./tools/check_c4_periodic_partner.sh` from the repository root. This is
scoped local acceptance; it does not claim a full root-library build or
hosted acceptance. Independent human review remains pending.

### Negative controls

`small_translate_eq_zero_of_agree` uses a tile meeting the agreement
window. If `abs(t)` is below that tile's length and translation by `t`
preserves its exact occurrence, the original tiling contains that tile
and its translated copy with overlapping interiors. Uniqueness of the
covering tile forces their positions to be equal, hence `t = 0`.

Choosing a tile that contains zero gives
`exists_small_translate_not_agree`: for every hull tiling and every
`delta > 0`, some `0 < t < delta` fails exact agreement on radius one.
`not_continuousAt_exact_orbit` converts this to discontinuity of the old
orbit map at zero. These are universal source statements, not a finite
sample; their compilation and axiom dependencies are covered by the receipt above. The
existing legal Thue–Morse seed supplies a nonempty hull independently of
recognizability.

In the ordinary topology `continuous_local_orbit` proves the corresponding
orbit maps continuous. `not_continuous_toHull` proves that the reverse
carrier projection to the exact metric is not continuous whenever an
actual hull tiling is supplied. Together with `continuous_ofExact`, these
results check the distinction between the two topology instances directly.

The pre-code review also records the periodic one-letter example
`a -> aa`: its phase is doubled by inflation, so inflation continuity
alone cannot supply injectivity. This is a written boundary example in
the source review, not an additional control claimed to have been
formalized in these modules.

### Non-claims / remaining gaps

1. No compactness, Hausdorffness or metric for `LocalHull` is established
   in this increment. The ordinary neighbourhood topology is identified
   directly, but those additional properties need their own proofs.
2. Recognizability remains an external input. No continuous inverse for
   inflation is constructed, and bare bijectivity in the old exact
   topology is not upgraded to a homeomorphism.
3. The concrete realization map is not proved continuous, even on the
   exact presentation. The equivariant criterion exposes a sufficient
   and necessary continuity obligation rather than discharging it.
4. The normalized correspondence with BBK's map, its surjectivity and
   finite fibres remain separate. In particular, BBK's global-attractor
   convention can include extra nonrecurrent orbits; the standard local
   topology does not remove that source-identification obligation.
5. BDS periodicization, witness-selection inputs and the remaining
   rank-two/global strict-system exclusions are unchanged. No C4 or PSC
   claim is promoted.

## Concrete continuity follow-up

The [next formalization](c4-realization-continuity-2026-11-19.md) discharges
the exact-source continuity obligation in this note. It proves completeness
of the exact hull, compactness of its fixed-origin fibres and finiteness of
possible parent origins, then derives continuity of the existing inverse
from bijective inflation. Uniform convergence of the actual stable series
proves continuity of the realization, and the iff above transfers it to
the ordinary topology. Ordinary inflation is also now a homeomorphism under
the same bijectivity input. Recognizability itself, full ordinary compactness
and separation, normalized BBK identification and finite fibres remain
separate. The receipt in this note continues to refer to its original scope.
