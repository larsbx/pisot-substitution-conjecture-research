# Continuity of the concrete geometric realization

**Status:** the concrete ordinary-hull continuity theorem and its supporting
modules compile locally. The integrated fresh-closure build, compiled axiom
audit and repository acceptance receipts are pending and will be recorded
below. No hosted or full root-library acceptance is asserted by this status.

Starting revision: `c8d582ff502b18745f7b0a73037458c92e705ad9`, the merge of
PR #625. The [pre-code source decision](c4-realization-continuity-stop-go-2026-11-19.md)
checks BBK, Barge–Diamond–Swanson and Barge–Diamond and chooses the direct
compact-origin-fibre argument. This formalizes the standard continuity
construction on the repository's actual legal carrier and realization
formula; no mathematical novelty or C4/PSC closure is claimed.

## Work shown

### Assumptions and hypotheses

For the existing finite, decidable, nonempty alphabet and `LengthSubst S`,
the final theorem in `Psc.PeriodicPartnerRealizationContinuity` is:

```lean
theorem continuous_realizeLocal
    (P : PisotData S)
    (hR : Function.Bijective (inflateH (S := S)))
    (hβ : 1 < S.β) :
    Continuous (realizeLocal P hR)
```

`realizeLocal` is the unchanged concrete solenoid map on the ordinary-hull
presentation introduced in PR #625. The theorem adds no continuity,
compactness, local-recognition-radius or finite-fibre premise. In particular,
the needed continuity of `desub hR` is now proved from finite tile data and
the original bijectivity input.

| Hypothesis | Where it is used |
| --- | --- |
| Positive lengths and the existing legal hull | Exact local limits preserve coverage, uniqueness and legality. |
| Finite alphabet | A positive minimum tile length and finitely many labels give finitely many anchored windows and finitely many parent origins. |
| Nonempty alphabet | Supplies the existing minimum-length and positive-inflation-factor lemmas. |
| `hR : Bijective inflateH` | Identifies the existing `desub` as the inverse. Bijectivity itself remains the recognizability input. |
| `P : PisotData S` | Supplies the uniform geometric majorant for the stable-coordinate series. The proof allows `P.ρ = 0`. |
| `1 < S.β` | Used by the existing flow-equivariance theorem when transferring continuity to the ordinary hull. It is not required for exact inverse continuity. |

### Derivation / reduction

#### 1. Exact Cauchy sequences have legal limits

`PeriodicPartnerHullComplete` proves that every exact Cauchy sequence
eventually agrees on each bounded window. Define its limiting tile set by
eventual membership. On every fixed window this set agrees with a sufficiently
late tiling in the sequence. Coverage and uniqueness follow in a window
containing the point under consideration; legality follows because each
bounded limiting patch is already a patch in that late legal tiling.
The same agreement estimates prove convergence in the existing metric.

This establishes `CompleteSpace S.Hull` without a finite-alphabet premise.
It does not assert that the full exact hull is compact.

#### 2. Fixed-origin fibres are compact

`PeriodicPartnerOriginContinuity` proves that radius-one agreement identifies
the tile containing zero. Therefore `origin` is locally constant and its
fibres are both open and closed in the exact topology.

`PeriodicPartnerHullCompact` follows the actual adjacent tiles in both
directions. Their starts move outward by at least `n * minLen S`, and finite
induction proves that they cover the intervals between those starts.
With the origin tile fixed, each successive tile has only finitely many
possibilities: its label comes from a finite alphabet and its start is
obtained by adding or subtracting one tile length.

Consequently, every window of a fixed radius is contained in a uniform finite
set of exact tiles. Its possible tile sets form a finite powerset. The metric
agreement bound turns this into total boundedness; closedness and the proved
completeness then give

```lean
isCompact_origin_fibre (p : α × ℝ) :
  IsCompact {T : S.Hull | origin T = p}
```

Empty fibres are included. No global compactness premise is used.

#### 3. Finite possible parents make inflation closed

Fix a child origin tile `q`. The parent origin has a label `a` and a position

`(q.start - length(prefix)) / S.β`,

where `prefix` is an initial segment of `S.σ a`. The finite set
`parentOrigins S q` overapproximates all possibilities, and
`origin_mem_parentOrigins` proves membership for each actual parent.

The preimage of the child-origin fibre is closed by forward inflation
continuity, and lies in the finite union of the corresponding compact parent
fibres. Thus that preimage is compact, without a recognizability assumption.

For a closed set `F`, work inside an open child-origin fibre. The part of
`inflateH '' F` in that fibre is the image of a closed subset of its compact
preimage, hence is compact and closed in the exact metric space. These open
fibres cover the hull, so `isClosedMap_inflateH` proves that inflation is a
closed map globally.

Under `hR`, the existing inverse satisfies
`desub hR ⁻¹' F = inflateH '' F`. The closed-map result therefore proves
`continuous_desub hR`. This is a deduction from finite geometry and
bijectivity, not a new continuity field on the input.

#### 4. Prefix choices and the whole stable series are continuous

Equal parent origins determine equal child origins by uniqueness in the
same placed substitution word. In the actual definition of `offset`, these
equalities identify the existential choice predicates; proof irrelevance
then identifies their proof arguments. This proves `offset_eq_of_origin_eq`
and local constancy of the existing selector. No replacement selector or
injectivity of the length functional is introduced.

Continuity of desubstitution gives continuity of every iterated level and
local constancy of each `xs` and `cs` coordinate. The actual series terms
satisfy the uniform bound

`norm(M^k * proj(cs hR T k)) <= P.C * P.offsetBound * P.ρ^k`.

The majorant is summable, including when `P.ρ = 0`. The module proves
uniform convergence on the whole exact hull and applies uniform summation
to obtain continuity of `realVec`. Composing with the lattice quotient gives
`continuous_torusRealize`. Every solenoid coordinate is this map composed
with a continuous level; product and subtype continuity yield
`continuous_realize` for the full history map.

Finally PR #625's already proved `continuous_realizeLocal_iff` supplies
ordinary-hull continuity using the existing equivariance and continuous
target flow. The intermediate `_of_continuous_desub` lemmas expose the
analytic decomposition; the final theorem discharges their premise using
the new inverse theorem.

#### 5. Ordinary inflation now has a continuous inverse

`PeriodicPartnerLocalInflation` carries the existing inverse to `LocalHull`.
On the quotient chart it obeys

`desubLocal (chart (t,T)) = chart (t / S.β, desub T)`.

The right side is continuous by exact desubstitution continuity. The open
quotient criterion therefore gives `continuous_desubLocal`, and the existing
inverse identities package literal inflation as `inflateHomeomorph hR`.
The only recognizability hypothesis remains the original bijectivity input.

### Evidence and replay

The seven new modules have been compiled individually with pinned Lean
4.34.0-rc2 and `autoImplicit=false`. Integrated clean-build and compiled
axiom-audit evidence is pending; this paragraph will be replaced by its
terminal receipts after the gate completes.

| Module | Formal scope |
| --- | --- |
| [`PeriodicPartnerHullComplete.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerHullComplete.lean) | Stabilized windows, legal exact limits and completeness. |
| [`PeriodicPartnerOriginContinuity.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerOriginContinuity.lean) | Locally constant origins and the existing chosen prefix counts; clopen origin fibres. |
| [`PeriodicPartnerHullCompact.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerHullCompact.lean) | Adjacent tiles, finite windows, total boundedness and compact exact origin fibres. |
| [`PeriodicPartnerDesubContinuity.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerDesubContinuity.lean) | Finite parent origins, compact fibre preimages, closed inflation and continuous exact desubstitution. |
| [`PeriodicPartnerLocalInflation.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerLocalInflation.lean) | Continuous ordinary desubstitution and the inflation homeomorphism under `hR`. |
| [`PeriodicPartnerRealizationContinuity.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerRealizationContinuity.lean) | Uniform series convergence and actual exact/ordinary realization continuity. |
| [`PeriodicPartnerRealizationContinuityControls.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerRealizationContinuityControls.lean) | Discontinuity of the ordinary scalar origin start at a seam and on every inhabited hull. |

Replay the complete local periodic-partner closure and compiled audit with
the unchanged canonical gate, from the repository root:

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 -m pytest -q tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_recorded_data_integrity.py
```

### Negative controls

The new `not_continuousAt_local_originStart_of_zero` proves that the scalar
start of the origin tile jumps at an origin seam in the ordinary topology.
A sufficiently small negative translation places zero in the predecessor
tile, whose length remains positive. Its start stays separated from zero,
contradicting ordinary continuity. Translating any supplied tiling to one of
its seams gives `not_continuous_local_originStart` on every inhabited hull.

Thus the local origin and prefix continuity assertions belong to the exact
presentation. The ordinary conclusion concerns the quotient/solenoid map;
no globally continuous ordinary real-vector lift is asserted. The prior
universal controls distinguishing exact and ordinary orbit maps remain.

The pre-code note retains the one-letter phase-doubling example as a written
control against deriving injectivity from forward continuity. The geometric
majorant also preserves the existing allowance `ρ = 0`; it does not silently
strengthen the contraction hypothesis. No finite-domain experiment is used
as evidence for these unbounded continuity statements.

### Non-claims / remaining gaps

1. Recognizability itself remains supplied as `hR`. The continuous inverse
   is now derived from that input; bijectivity is not proved here.
2. The normalized identification with BBK's `h_φ`, surjectivity and finite
   fibres remain separate obligations. Continuity alone does not import
   BBK Theorem 4.2 or reconcile the global-attractor convention.
3. Full ordinary-hull compactness, Hausdorffness and a compatible numerical
   metric are not established in this increment. Compactness is proved for
   the exact anchored fibres actually used by the inverse argument.
4. BDS periodicization, remaining witness-selection and rank-two/global
   exclusions are unchanged. No governed claim is promoted; C4 and PSC
   remain open.
5. Independent human review is pending. Local module compilation, the fresh
   scoped gate, a full root-library build and hosted CI are separate scopes.
