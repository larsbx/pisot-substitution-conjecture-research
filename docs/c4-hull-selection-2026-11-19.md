# Theorem S on the legal hull, the vertex-partner case of (A), and what obligation 3 is

**Status:** Lean proofs from named inputs, no new axioms. Independent human review is
pending. This closes gap 2 of the
[witness-selection note](c4-witness-selection-2026-11-19.md#non-claims--remaining-gaps):
`VertexLaws` and `BranchExistence` are now proved on
[`PeriodicPartnerHull`](c4-tiling-hull-realization-2026-11-19.md), so Theorem S holds on the
concrete hull. It adds one step towards gap 3 of the
[conditional formalization](c4-periodic-partner-formalization-2026-11-19.md#non-claims--remaining-gaps),
the global contradiction, and records why that gap is not a local step. No strict system is
excluded. C4 and PSC remain open; no governed claim changes.

Starting revision: `main@d28af05` (merge of #614).

## Source decision

| Source | Used for | Boundary |
| --- | --- | --- |
| [Witness-selection note](c4-witness-selection-2026-11-19.md), [its source decision](c4-witness-selection-stop-go-2026-11-19.md) | Theorem S, its contracts `VertexLaws` and `BranchExistence`, the named inputs | unchanged; not re-read beyond the statements |
| [Hull note](c4-tiling-hull-realization-2026-11-19.md) | the hull, `RightBranchLaws`, `PublishedInputs` | unchanged |
| Round-4 note, [§3.2–3.3](c4-round4-2026-11-17.md#32-statements-binding-form) | Lemma A (injective `g_R` ⇒ right (NM_V)), (Z2) | internal |
| Rank-two note, [Theorem W](c4-rank-two-wall-2026-11-16.md#62-statement) and [§10](c4-rank-two-wall-2026-11-16.md#10-what-is-still-open-at-coincidence-rank-two) | (W1) uniqueness of `Z`, (W2), the open statement 1 | internal |
| [Unique-partner note](c4-unique-partner-exclusion-2026-11-18.md) | Theorems UP, UP′: where a witness is forced | internal |

No external source is newly imported. The contract proofs are elementary tiling geometry.
**Decision: proceed** with the contracts and the vertex-partner lemma; novelty is claimed for
neither beyond their formal statement. **Stop** on obligation 3 as a local step (§3).

## 1. The two contracts on the hull

Module [`PeriodicPartnerHullSelection.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerHullSelection.lean),
namespace `Psc.PeriodicPartnerHullSelection`. `StartsAt T y a` is `(a, y) ∈ T`.

| Contract field | Proof on the hull | Hypothesis |
| --- | --- | --- |
| `agree_symm` | agreement on a window is symmetric | none |
| `start_of_end` (`startsAt_of_endsAt`) | the tile covering `y` cannot begin before `y`, else it overlaps the tile ending at `y` | none |
| `periodic_ray` | with `n`, `m` periods of `T`, `U`, both contain the supertiles `σ^{nmk}(a)` at `0` (`supertile_subset`); these tile `[0, β^{nmk} ℓ_a)` (`tilesOn_supertile`), which exhausts `(0, ∞)` | `1 < β` |
| `BranchExistence` (`branchExistence`) | `y = inf{x : T, U agree on (x, ∞)}` is finite (else `T = U`), agreement holds at `y`, a tile starts at `y` in both (`startsAt_of_least`), a tile ends at `y` in both (`endsAt_of_startsAt`), and equal end tiles would push agreement left of `y` (`agree_extend`) | finite alphabet |

The finite alphabet enters once: `endsAt_of_startsAt` uses a positive minimal tile length.
Without it a tiling may accumulate tiles at `y` from the left.

`hull_selection_dichotomy` is Theorem S with `f = inflateH`, `g = g_R` the last-letter map.
Its inputs are the fields of `PublishedInputs`, the joining relation `Z` with
translation invariance, same fibre and distinctness, (E1) `AsymptoticSameFibre`,
`NMVRight`, and two periodic letters. Every one is a hypothesis; none is a Lean axiom.

## 2. Case (A) with a vertex-type common partner

Theorem S case (A): the leaves `S`, `U` branch at `0` with letters `b ≠ c`, and the triple is
`Φⁿ`-fixed in `F₀`. Split by the common partner `T` at the origin:

- **(A_v)** `T` has a vertex at `0`, ending a tile `x`;
- **(A_i)** `0` is interior to a tile of `T`.

**Lemma VP (vertex partner).** In (A_v), `g_R` is a permutation of the three letters.

*Proof.* (Z2) at level zero: `T` shares no tile with `S` or `U`, so `x ≠ b` and `x ≠ c`
(the tiles `(x, −ℓ_x)` and `(b, −ℓ_b)` would coincide). The letter ending at `0` in a
`Φⁿ`-fixed tiling is `g_R`-periodic, by endpoint transport and uniqueness
(`periodic_letter`). So `x, b, c` are three distinct periodic letters of a map on three
letters, which is then injective (`injective_of_three_periodic`, by `decide`). ∎

**Consequences.** In (A_v), round-4 Lemma A gives (NM_V) on the right with no hypothesis, and
case (B) is empty on the right: there is no collapsed pair. So the residual of Theorem S on a
side with a non-injective `g_R` consists of (A_i) and (B) only.

**Controls.**
- `two_periodic_not_injective`: two periodic letters do not give injectivity
  (`g = (0,1,1)`), so the third letter is used.
- The seam model `K_{3,2}` of
  [`PeriodicPartnerControls`](../proof/PscVerif/PscVerif/PeriodicPartnerControls.lean)
  realizes (A_v) at the seam level (`model_asymptotic_copartners`): `(0,0)` has partners
  `(1,1)` and `(2,1)`, which share their right letter and use the two left letters other
  than `0`. That model is symmetric, triangle-free, has a partner everywhere and satisfies the
  co-partner conclusion of (W4). Lemma VP's conclusion holds in it. **Seam-level data
  therefore cannot exclude (A_v).**

| Statement | Lean |
| --- | --- |
| periodic origin letter | `periodic_letter` |
| three periodic letters ⇒ injective | `injective_of_three_periodic` |
| Lemma VP, abstract | `injective_of_vertex_partner` |
| Lemma VP, on the hull | `hull_lastLetter_injective_of_vertex_partner` |
| control | `two_periodic_not_injective` |

## 3. Obligation 3 is the rank-two wall, not a local step

The obligation reads: from a witness, obtain a contradiction. Three earlier results fix what
that means.

1. Under (NM_V), odd determinant and `cr = 2`, a witness exists whenever a strict system does
   (Theorems UP and UP′ with round-4 Lemma C(c)).
2. By (W1), `Z` is the unique minimal set of pairs of distinct fibre-mates, so it is the
   closure of the twin relation `{(T, T*) : the fibre of T is {T, T*}}`. By (W2) `π₁` is
   injective almost everywhere. Every partner of a zero-fibre tiling is a limit of twins.
3. Hence a contradiction from a witness, in this class, **is** the statement that no strict
   system exists at `cr = 2`. That is open statement 1 of the
   [rank-two note, §10](c4-rank-two-wall-2026-11-16.md#10-what-is-still-open-at-coincidence-rank-two),
   restricted to (NM_V) and odd determinant.

So the witness does not reduce the problem further on its own. Each finite datum it supplies
holds in the `K_{3,2}` model: the two strict links, the shared right ray, (Z2), triangle-freeness,
the (W4) co-partner relation, and now Lemma VP. A proof must consume something global. Three
inputs are not yet used together with the witness:

- **Irreducibility of `χ_M` beyond `ER` connectivity.** The `K_{3,2}` model is `ER`-level
  data; irreducibility enters Theorem UP only through B15 Theorem 22.
- **The twin involution.** `ι(T) = T*` is defined and continuous on the full-measure set of
  two-point fibres. Theorem UP used a continuous `ι` on all of `Ω`. A replacement must control
  `ι` near `F₀`, where (A_i) and (B) live.
- **The bigon substitution.** By (W1), `(T, S)` and `(T, U)` are fixed points of the primitive
  bigon substitution `τ` on `B`. In (A_v), `0` is a common vertex of both pairs, so they share
  their right bigon and differ in their left bigons. No constraint on `τ` from this is known.

None of these is attempted here.

## Evidence and replay

```sh
cd proof/PscVerif && lake build PscVerif.PeriodicPartnerHullSelection
lake env lean PeriodicPartnerAudit.lean          # every declaration: standard axioms only
cd ../.. && ./tools/check_c4_periodic_partner.sh # fresh clone, all eleven modules
python3 tools/make_proof_bank.py --check
```

Locally, the module builds with no warnings against the pinned toolchain and Mathlib cache
(incremental build), and `PeriodicPartnerAudit.lean` reports only `propext`,
`Classical.choice` and `Quot.sound` for its 26 declarations. The isolated gate's receipt must
come from CI.

## Non-claims / remaining gaps

1. **(A_i) and (B) are open.** Lemma VP removes neither.
2. **Obligation 3 is open** and, by §3, is the rank-two wall in this class.
3. **Hull inputs.** (E1), (NM_V), the joining relation and the fields of `PublishedInputs`
   remain hypotheses on the hull. The realization map is not constructed. The left-hand
   instance (reflected hull) is not built.

No assertion here makes (NM_V) universal, excludes a strict system, or changes the status of
C4 or PSC.
