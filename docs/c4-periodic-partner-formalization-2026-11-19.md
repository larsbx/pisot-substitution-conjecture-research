# Periodic partners: checked conditional dynamics and metric collapse

**Status:** The deductions of Lemmas P, E and M from
[PR #610](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/610)
are now Lean theorems under explicit geometric inputs. The right/left
orientation transfer, exact-ray/metric bridge and a combined ternary
dichotomy are also checked.
This does not construct the legal substitution tiling hull or prove that it
instantiates those inputs. Independent human review remains pending. C4 and
PSC remain open; no governed claim changes.

Starting revision: `main@15c4098e53dfc4a1a45fd1f134ee6fbb5dd1da1a`.
The [pre-code source decision](c4-periodic-partner-formalization-stop-go-2026-11-19.md)
records the primary-source check, the exact target and the controls.
Integration also includes `main@4b75e005a6f3ec793e8c7d5c872091e1e00486f5`
(PR #611's finite-corpus NM_V census). That census supplies no universal
witness-selection premise to the theorems below.

## Work shown

### Assumptions and hypotheses

The original [extraction note](c4-periodic-partner-extraction-2026-11-18.md)
uses actual substitution tilings in its written arguments. The new Lean
modules prove their deductions for abstract objects satisfying the listed
contracts. A contract is a theorem argument or an explicit structure; no
new Lean axiom asserts a geometric fact.

| Input | Exact formal role | Remaining realization obligation |
| --- | --- | --- |
| `BDSPeriodicization` | A distinct asymptotic pair admits one common translation making both leaves periodic. It mentions neither the common partner nor the distinguished fibre. The metric consumer accepts this input for distance convergence under translation. | Instantiate the legal hull and supply the published Barge--Diamond--Swanson theorem for that metric flow. |
| Finite semiconjugacy | `f` is injective, `h` semiconjugates it to `A`, and the specified fibres are finite. The distinguished point `q₀` is fixed by `A`. | Construct geometric realization, including the full solenoid in the nonunit case, and supply the published finite-fibre theorem. |
| Joining inputs | Translations preserve both links; links imply the same `h`-fibre and distinct points; common translations are injective and preserve the asymptotic relation. | Instantiate these consequences of Z1, Z2 and Z4 for the actual strict component. No assertion identifies the abstract relation with the whole geometric strictness condition. |
| `RightBranchLaws` | Primitive agreement and endpoint predicates obey one-step translation/inflation transport, endpoint-label uniqueness, and agreement strictly before an endpoint forces equal labels there. | Verify the predicates against literal labelled tiles and their substitution. |
| `R4ZeroFibre` | A periodic point with a labelled endpoint at the physical origin maps to `q₀`. Both premises are present. | Establish the integral strand normalization and its origin/fibre correspondence. Finite-fibre dynamics proves that `q₀`-membership implies periodicity; origin endpoints remain separately supplied. |
| `AgreementData` | Agreement on a centred radius restricts to smaller positive radii, inflates in one step, and uniformly controls metric distance. | Construct the local tiling metric and prove these local patch facts. |
| Ray covers window | Right-ray agreement starting at `r ≤ -R`, with `R > 0`, gives centred agreement of radius `R`. | Verify containment for the same literal patch predicates. Together with translation transport and the metric modulus this proves exact-ray asymptoticity implies metric translation-asymptoticity. |
| Positive common tile | A common half-ray and the same labelled origin endpoint give a common patch of that label's positive tile length. | Verify the literal patch extension. The common partner may have an interior origin and receives no artificial endpoint label. |

The existing scalar, word, address and right-infinite-word definitions do
not yet supply a complete two-sided legal tiling hull. The concrete models
below prove that the new contracts are jointly satisfiable where claimed;
they are not substitutes for that tiling realization.

The intended patch convention uses tiles meeting the **open** centred
interval `(-R,R)` and the open right ray `(y,∞)`, as in round-four
section 3.1. A tile ending at the left boundary of a centred window does
not meet that window. This convention makes the common-tile input at its
full positive length precise; a realization using closed windows must
supply an appropriate strictly smaller positive radius instead.

### Derivation / reduction

#### 1. Periodic triple promotion (P)

`PeriodicPartnerDynamics.periodic_triple_of_asymptotic_partners` begins with
`Z T S`, `Z T U`, `S ≠ U`, and an asymptotic relation on the two leaves.
The named periodicization input supplies a common translating parameter
for the leaves only. Translation invariance retains both links. The finite
semiconjugacy theorem already proved in #610 then makes the common partner
periodic in their periodic base fibre, and a common positive period fixes
all three objects.

The conclusion retains both links, all three pairwise inequalities, the
asymptotic leaves, the shared fibre and its periodic base point. It does
not assert that the fibre is `q₀`. No compactness, Z3, (NM_V), determinant
condition, or rank hypothesis enters this deduction.

#### 2. The endpoint criterion (E)

`BranchAt` is defined from right-ray agreement at a position and two
different labels ending there. Branch-position uniqueness is derived from
the local agreement rule by comparing two candidate positions. It is not
an interface field.

Lean proves the endpoint/agreement transport for every iterate. If the
different endpoint labels persist, the branch position of a common
periodicized pair must satisfy `y = β^q * y`. The hypotheses `β > 1` and
`q > 0` force `y = 0`; hence the translating parameter is zero for a pair
whose branch was already normalized to the origin. This proves common
periodicity of the original pair from persistent endpoints. Conversely,
periodicity returns both endpoint labels, and distinct periodic labels
cannot merge at an intermediate iterate.

At supplied origin endpoints, the forward origin/fibre input (R4) and
finite-fibre dynamics give the equivalence with membership in the
distinguished fibre. The existing ternary finite theorem then supplies
the exact test:

`g_R^[2] b ≠ g_R^[2] c`

iff the labels differ at every depth, iff the branch-normalized leaves
have a common positive period, iff both map to `q₀`. The same-fibre common
partner also maps to `q₀` and shares a common positive period. Its own
origin need not be a vertex.

`PeriodicPartnerReflection` checks the mirror argument using
`τ'(t) = τ(-t)`, agreement at coordinate `-y`, and labelled tile starts at
`-y`. It proves every local-law transfer, the BDS input transfer in both
directions, and preservation of the origin R4 input. The exported left
criteria therefore use the first-letter map `g_L` with proved translation
signs and origin bookkeeping.

#### 3. Expanding agreement and collapse (M)

`PeriodicPartnerCollapse` proves by induction that a common positive
radius `R` becomes `β^n * R`. Given any metric tolerance, the uniform
agreement modulus supplies a comparison radius. Elementary power growth
eventually exceeds it, and restriction to that radius supplies the
distance bound. Thus the distances of the unshifted forward iterates tend
to zero. A finite initial delay is removed using the filter theorem for
translation of natural indices.

The partial origin-endpoint interface derives a positive common patch
when two transported labels merge. It therefore proves Lemma M from local
patch facts, without assuming the desired convergence. It also proves
that existing limits along the same cofinal sequence of indices are equal.
Existence of such limits, compactness, and continuity of inflation are not
asserted or needed for that implication. Metric separation is used to
conclude equality rather than just distance zero.

A general helper proves that two periodic points whose forward-orbit
distance tends to zero were already equal: evaluate the distance estimate
at sufficiently late multiples of a common positive period. This helper
has no agreement-data, expansion, or tile-length parameters.

#### 4. Exact rays and the metric periodicization input

The starting witness in round-four Lemma C(c) has exact agreement on a
half-line. The published BDS input uses metric asymptoticity under the
translation flow. `PeriodicPartnerAsymptotic` checks this direction of
the correspondence from local patch facts.

Given exact agreement to the right of `y`, translation by `t` moves its
start to `y-t`. For a metric tolerance, the uniform patch modulus supplies
a positive comparison radius `R`. At every `t ≥ y+R`, the translated ray
covers `(-R,R)`, so the metric distance is below that tolerance. This proves
`dist (τ t S) (τ t U) → 0` as `t → +∞`. No conclusion about metric
asymptoticity is assumed as an interface field, and no converse from metric
closeness to exact ray agreement is needed.

The checked adapter passes metric BDS periodicization into the existing
exact-ray endpoint consumer. The published periodicization theorem itself
and the actual legal-hull instance remain explicit external obligations.

#### 5. The combined branch-origin dichotomy

`PeriodicPartnerDichotomy.endpointDataOfBranch` uses definitionally the
same ray and endpoint predicates as E. Its only additional link is the
local common-patch fact. It does not combine independently chosen
geometric relations through an unstated correspondence.

For a normalized ternary branch, Lean proves:

`g_R^[2] b = g_R^[2] c`

iff the distance between unshifted inflated leaves tends to zero. The
forward direction is M. For the converse, separation at two steps would
give periodic leaves by E, contradicting their distinctness and the
general periodic-collapse lemma.

With the explicit realization inputs, this also proves that the leaves
lie in the distinguished fibre iff their unshifted iterates do not
collapse. The final theorem `ternary_branch_triple_dichotomy` classifies a
same-fibre triple:

- **Separated endpoint images:** all three points lie over `q₀` and have
  one common positive period.
- **Merged endpoint images:** none of the three original points lies over
  `q₀`, the leaves are not jointly periodic, and their unshifted iterates
  collapse.

Both cases concern the **same fixed branch origin**. The second case does
not exclude another common translating periodicization from landing in
the zero fibre. The documented `1/012/21` example already shows why this
origin distinction must be retained.

### Evidence and replay

| Module | Checked scope |
| --- | --- |
| [`PeriodicPartner.lean`](../proof/PscVerif/PscVerif/PeriodicPartner.lean) | Existing finite-fibre and endpoint iteration lemmas. |
| [`PeriodicPartnerControls.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerControls.lean) | Existing literal words/addresses, triangle, nontriangle and period-two lift controls. |
| [`PeriodicPartnerDynamics.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerDynamics.lean) | P, derived branch uniqueness, E, finite-fibre equivalence and the periodic triple consumer. |
| [`PeriodicPartnerCollapse.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerCollapse.lean) | M, cofinal limit collision, periodic-collapse separation and partial endpoint consumers. |
| [`PeriodicPartnerReflection.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerReflection.lean) | Checked left/right coordinate transfer and left-hand E consumers. |
| [`PeriodicPartnerAsymptotic.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerAsymptotic.lean) | Exact-ray to metric translation-asymptoticity, metric BDS adapter and endpoint consumer. |
| [`PeriodicPartnerDichotomy.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerDichotomy.lean) | Same-predicate adapter, exact collapse criterion and the triple dichotomy. |
| [`PeriodicPartnerModels.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerModels.lean) | Concrete contract instances, consumer applications and missing-hypothesis controls. |

Replay on the pinned Lean/Lake release:

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
python3 tools/check_markdown_source.py
PYTHONPATH=tools python3 -m claim_governance.cli --root .
python3 tools/make_ledger.py --check
python3 -m pytest -q tests/test_markdown_links.py tests/test_recorded_data_integrity.py
```

The scoped gate compiles all eight modules and their complete local
import closure from copied sources and fresh pinned dependency checkouts.
It restores only selected upstream source-hash artifacts, audits every
owned compiled declaration, checks named-source-theorem coverage, and
rechecks the source/pin bindings after each stage. The updated workflow
binds the exact PR revision and retains the source/build/audit receipts.
The full proof-bank root imports every new module as well. No existing
acceptance check is weakened.

Development builds and source review are distinct from the isolated
acceptance receipt. Exact accepted revision, declaration counts, and
hosted results are recorded in the integration PR. Neither axiom auditing
nor a successful abstract model proves the external tiling-space inputs.

### Negative controls

The original `1/012/21`, `012/120/201`, finite `K₃,₂`, BDS nonzero-fibre,
and fixed-base period-two controls remain unchanged. The new models add:

| Model | Exact point checked |
| --- | --- |
| Constant dynamics on `Fin 2` over a singleton base | Finite fibres without injectivity can contain a nonperiodic lift. |
| Integer successor over a singleton base | Injectivity without finite fibres does not make lifts periodic. |
| `ℝ × Fin 3` with coordinate doubling and a star partner relation | The same metric, ray and endpoint predicates instantiate P/E, the metric BDS bridge and the combined E/M consumer. The two leaves are translation-asymptotic; every centre/leaf pair remains at distance at least one under every common translation. |
| Identity dynamics with bounded-radius agreement at `β = 1` | Every agreement-data field can hold while strict expansion fails and distinct points do not collapse. |
| Identity dynamics with agreement only at nonpositive radius | A zero seed radius does not support the collapse conclusion, even with `β = 2`. |
| Real halving with agreement `dist x y * R ≤ 1` | Positive-radius agreement genuinely gives collapse while the two finite iterates remain distinct. |
| A partial endpoint model on the halving dynamics | Different initial labels merge after one step, and the full endpoint-collapse theorem applies. This example already has a positive common patch; it does not claim that the merge first creates agreement. |

These are exact theorem applications, not numerical experiments. They are
explicitly abstract; none realizes a strict rank-two PIP3 joining.

For the joint model, inflation sends `(x,a)` to `(2x,a)` and translation
by `t` sends it to `(x-t,a)`. The metric is induced by the injective map
`(x,a) ↦ (x, (flag(a), a/(1+|x|)))` into a product of real metric spaces,
where `flag(0)=0` and `flag(1)=flag(2)=1`. The fixed flag separates the
centre from its leaves. Distinct leaves with the same coordinate have
distance at most `2/(1+|x|)`. A shared right ray starting at or before `-R`
therefore gives the required uniform metric estimate; radius `3/ε`
suffices for tolerance `ε > 0`.

The model proves its metric periodicization input directly: convergence
under common translation forces equality of the real coordinates, and
translation by that coordinate puts both points at inflation-fixed
coordinate zero. The exported endpoint and dichotomy consumers then use
that input through the checked metric-to-ray adapter, with every local
contract discharged. This establishes joint nonvacuity without asserting
a compact legal tiling hull or a strict-system realization.

### Non-claims / remaining gaps

The conditional **deductions** P/E/M, orientation transfer, exact-ray to
metric asymptoticity and ternary classification are formalized. The
remaining obligations are:

1. Construct the actual legal two-sided tiling space, its flow/inflation,
   endpoint predicates, local metric and geometric-realization map; prove
   the primitive contracts and connect the published BDS/R4 inputs to
   that instance. *Update:* the
   [hull instance](c4-tiling-hull-realization-2026-11-19.md) does all of this
   except the geometric-realization map, with an exact-agreement metric; the
   published inputs are fields of `PublishedInputs` on that hull.
2. Under the surviving strict rank-two, odd-determinant and (NM_V)
   hypotheses, select a witness that passes the endpoint test or treat
   its other periodic branch fibre. No theorem here supplies that selection.
   *Update:* [Theorem S](c4-witness-selection-2026-11-19.md) checks the reduction to
   interior leaves on the collapsed pair; that case stays open and is populated in
   `F₀` on the corpus.
3. Obtain the further global contradiction. The asymptotic leaves share
   tiles, so their mutual edge is not strict; W4 and the two strict links
   do not themselves give a noncoincidence triangle or a parity argument.
   *Update:* the [hull-selection note](c4-hull-selection-2026-11-19.md) shows that a
   vertex-type common partner in the origin case forces `g_R` to be a permutation, and
   records that this obligation, under (NM_V) and odd determinant, is the rank-two wall
   itself rather than a local step.

No universal (NM_V), no new strict-system exclusion, and no C4 or PSC proof
is claimed. The concrete tiling correspondence and independent human
validation remain distinct from these checked conditional deductions.
