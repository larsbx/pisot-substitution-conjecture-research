# C4 finite actual carriers and fixed-row escape: bounded controls

This note accompanies the prior
[literature stop/go](c4-finite-carrier-dual-literature-2026-11-10.md).
The controls preserve two separate reductions: finite support and interior
successors for actual marked word pairs, and the mass and dual behavior of
complete literal descendant lists. They reuse the canonical Mojo kernels;
the independent bounded specification runs in Quint. No new Python
mathematical implementation is introduced.

**Development status:** the source-bound Quint runner passed all **28
tests** and rejected all **12 deliberate mutations** at their specified
assertions. The receipt binds dirty worktree sources over
`main@35b4d4101d36288f41f7cb04851f4bf98e0092c5`; it is not a compiled Lean
or hosted Mojo acceptance receipt. Native assertions are supplied in
`kernel/tests/test_c4_finite_carrier.mojo` and the extended
`kernel/tests/test_c4_two_generation_rank.mojo`. Exact-head acceptance
still requires the implementation PR's hosted executions and complete
Lean declaration/axiom audit.

## 1. The actual finite carrier

Use the existing strict non-PIP fixture

\[
\sigma(0)=1,\qquad \sigma(1)=012,\qquad \sigma(2)=1,
\]

with the four ordered word pairs

\[
C=\{(01,10),(10,01),(12,21),(21,12)\}.
\]

Every pair is balanced and irreducible, has length two on each track,
and is noncoincident. Complete substitution and reduction retains exactly
two ordered children per parent, all in this set. The canonical
`build_derived_system` validates the two normalized states
`A=(01,10)` and `B=(12,21)`, with the exact oriented rows

\[
A\longmapsto A^-B^+,\qquad B\longmapsto A^+B^-.
\]

The native tests use `apply_substitution`, `coincidence_boundaries`,
`decompose`, `build_derived_system`, and `prefix_difference3` from the
existing kernel. Each packet label retains the selected top and bottom
letters and their **top-prefix minus bottom-prefix** Parikh residual.
All sixteen indexed marks in `C` produce sixteen distinct labels. For
the positive length row `ℓ=(1,2,1)`, twelve of these marks have strict
physical interior overlap. None of those twelve packets is diagonal.

The finite-support statement is about the image of actual marks. It does
not equate set cardinality with occurrence multiplicity. The separate
reducible diagonal pair `00/00` has four indexed marks, three distinct
packet labels, and one distinct interior packet label: its two aligned
marks produce the same label. This pair is a cardinality control and is
not inserted into the strict carrier.

### Perron scaling and every interior successor

The exact image lengths for `ℓ=(1,2,1)` are `(2,4,2)=2ℓ`.
The tests enumerate every valid digit pair for each of the twelve source
interior marks. Every source has at least one interior successor; every
interior successor selects one actual common balanced factor, retains its
packet when the balanced prefix is removed, and returns to the carrier's
interior support. No first-digit or first-child shortcut is used.

The independent positive binary family consists of all sixteen ordered
strict balanced parents of length two through four and all sixteen binary
substitutions whose two images have length two. Unit lengths have scale
two, giving **256 parent/substitution inputs**, with all valid marks and
digit pairs checked.

### Positive lengths alone can fail

Keep the same substitution and source `01/10`, but choose top index zero
and bottom index one with the positive row `ℓ=(2,1,1)`.

| Selected occurrence | Source interval | Only selected image interval |
| --- | --- | --- |
| Top `0`, index 0 | `[0,2]` | `σ(0)=1` at `[0,1]` |
| Bottom `0`, index 1 | `[1,3]` | `σ(0)=1` at `[4,5]` |

The source interiors overlap. Both selected images are singletons, so the
only valid digit pair is `(0,0)`, and the target interiors are disjoint.
In the actual inflated pair `1012/0121`, those digits have global indices
zero and three. The complete cuts are `[0,2,4]`, so the digits also belong
to distinct balanced factor occurrences. The canonical `descendant`
constructor rejects them as a split. The row does not satisfy the common
scaling equations; positivity and nonerasure cannot replace those
equations.

### A literal nonproductive cycle and boundary distinctions

With the correct row, marks `(0,0)` and digits `(0,0)` give the exact
two-cycle

\[
(01,10)\longrightarrow(10,01)\longrightarrow(01,10),
\]

using child ordinal zero at both steps. Its selected packets alternate
between `(0,1,0)` and `(1,0,0)`. Every selected packet has geometric
interior overlap and is non-diagonal. This is a realized non-PIP control
against upgrading seriality or finite recurrence to productivity. It does
not assert a shared legal or recognizable limit hierarchy.

Native `TargetPacket.interior` is a different predicate: it records a
selected **interior left balanced-factor boundary**. These cycle steps
are at global position zero, so their native flags are false while their
physical intervals overlap. The native tests check both facts explicitly.
They construct packets from the complete canonical swap-seeded BPA;
`build_packets` is not supplied an invented automaton containing only the
strict component.

Endpoint contact remains insufficient. In the diagonal pair `01/01`,
marks zero and one meet at physical coordinate one for `ℓ=(1,2,1)`, but
have disjoint interiors and belong to different factor ordinals. The
earlier independent Quint boundary-contact test and its strict-inequality
mutation remain unchanged.

## 2. Fixed-row escape and complete occurrence mass

For `σ=1/02/202` and source `01/10`, the existing canonical
`literal_two_generation_parikh_rank` returns the following complete
ordered forest. Both parent and child ordinals are retained.

| Record ID | Depth | First ordinal | Second ordinal | Actual ordered pair | Parikh column | Row `(1,-1,0)` |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 0 | — | — | `01/10` | `(1,1,0)` | 0 |
| 1 | 1 | 0 | — | `102/021` | `(1,1,1)` | 0 |
| 2 | 2 | 0 | 0 | `021/120` | `(1,1,1)` | 0 |
| 3 | 2 | 0 | 1 | `2/2` | `(0,0,1)` | 0 |
| 4 | 2 | 0 | 2 | `0/0` | `(1,0,0)` | 1 |
| 5 | 2 | 0 | 3 | `2/2` | `(0,0,1)` | 0 |

The same nonzero row vanishes on every occurrence at depths zero and one.
Its only depth-two witness is the singleton `0/0`, at child ordinal two.
Dropping diagonal children therefore removes the witness. The correct
depth-two mass is `(2,1,3)`, while deduplicating the repeated `2/2` gives
`(2,1,2)`. Omitting every diagonal child leaves only mass `(1,1,1)`.

Native assertions compare each complete depth-zero/one/two mass with the
Parikh column of the corresponding whole inflated source word. Quint
independently counts word populations, constructs the incidence action
from the three image words, and checks the mass identity through depth
four on this fixture.

The reducible balanced source `00/00` supplies a second control. Its
depth-zero descendant list is the **single whole source pair**. At depth
one it has two `1/1` occurrences; continuing to inflate both gives four
depth-two singleton occurrences with total mass `(2,0,2)`. Quint checks
mass through depth three. This descendant list intentionally continues
after coincidences; the canonical BPA's policy of leaving coincidences
terminal is a separate interface.

The existing full-rank primitive but reducible strict fixture
`σ=10/102/211`, source `102/210`, retains rank two. Every actual column
at depths zero, one and two satisfies `p₀=p₂`, so the fixed nonzero row
`(1,0,-1)` annihilates them all. Full incidence rank cannot replace
characteristic-polynomial irreducibility. The empty source has zero mass;
the native bounded rank certificate refuses it, while the Quint literal
model explicitly gives the singleton empty pair at depth zero and the
empty descendant list thereafter.

The pre-existing `01/12/021` PIP control is retained without modification
to its assertions: two complete physically flat generations already have
rank three, a good-edge newborn appears at depth three, and an actual
diagonal appears at depth four. Short flatness still does not supply a
common nonzero annihilator.

## 3. Exact bounded inventory

The first twenty Quint tests and their seven mutations are retained from
[the address/transport controls](c4-address-transport-controls-2026-11-10.md).
Their domains remain 576 strict-parent/substitution inputs, nine positive
binary length rows, 400 generic chunk lists with 1,620 in-range global
indices, 99 balanced binary pairs, and 10,400 source-index/digit choices.
The ternary extension has separate `parikh3`, `residual3`, complete
factor-list and incidence definitions; it does not silently reinterpret
the earlier binary affine arithmetic.

The runner enforces this exact ordered **28-test** inventory:

```text
domainCountTest
allSingletonsGiveNewbornTest
alignedLetterIsSingletonTest
interiorOverlapKeepsOrdinalTest
boundaryTouchIsInsufficientTest
repeatedFactorValuesLoseOccurrenceTest
erasureAndSingletonParentControlsTest
parentIrreducibilityIsNecessaryTest
bothNewbornSidesTest
existentialRouteAllowsAvoidingCycleTest
lookupDomainCountTest
globalToLocalReconstructionTest
exteriorAddressRejectedTest
balancedFactorLookupTest
transportDomainCountTest
literalAffineSquareTest
balancedPrefixTrimmingTest
trackSwapCovarianceTest
affineTermsAreNecessaryTest
sameLetterSplitStaysSplitTest
finiteActualPacketSupportTest
perronStrictCarrierSuccessorTest
equalLengthBinarySuccessorTest
positiveWrongRowDeadEndTest
actualNonproductiveInteriorCycleTest
descendantMassMultiplicityTest
fixedRowEscapeDepthTwoTest
reducibleAndEmptyDualControlsTest
```

The eight new tests assert the finite carrier counts, all twelve actual
interior-source successor cases, the 256-input positive binary family,
the wrong-row dead end, the actual cycle, complete mass including repeats,
the depth-two fixed-row witness, and the reducible/empty-source controls.
Every finite quantifier is evaluated within one test execution; a single
sample is not a random choice of a word or a digit.

### Exact twelve mutation controls

| Mutation | Required assertion failure |
| --- | --- |
| `touch-replaces-interior` | `boundaryTouchIsInsufficientTest` |
| `ordinal-erased` | `repeatedFactorValuesLoseOccurrenceTest` |
| `inherited-cut-ignored` | `parentIrreducibilityIsNecessaryTest` |
| `factor-prefix-offset-ignored` | `globalToLocalReconstructionTest` |
| `incidence-action-omitted` | `affineTermsAreNecessaryTest` |
| `digit-forcing-omitted` | `affineTermsAreNecessaryTest` |
| `track-swap-sign-ignored` | `trackSwapCovarianceTest` |
| `packet-residual-erased` | `finiteActualPacketSupportTest` |
| `perron-equations-ignored` | `positiveWrongRowDeadEndTest` |
| `first-digit-only` | `perronStrictCarrierSuccessorTest` |
| `diagonal-descendants-omitted` | `fixedRowEscapeDepthTwoTest` |
| `repeated-factors-deduplicated-in-mass` | `descendantMassMultiplicityTest` |

The new mutations respectively erase the residual in a packet label,
replace the image-scaling equations with positivity, restrict all digit
choices to `(0,0)`, discard coincident children, and sum distinct factor
values instead of occurrences. Every mutation reaches its specified
`QNT508` assertion failure. An out-of-range access, type/parse failure,
missing test, timeout or infrastructure failure earns no rejection receipt.

## 4. Provenance and replay

`tools/check_c4_occurrence_quint.py` pins Quint **0.33.1**, the TypeScript
backend and seed **20261110**. It records the model and runner hashes and
Git revision, checks the exact ordered test inventory, and typechecks an
immutable private model snapshot. Each mutation now also runs from an
immutable snapshot whose bytes are rechecked. The model, runner and Git
revision must still match at the end. Receipt schema
`psc-c4-occurrence-quint-v3` includes all earlier and new declared domains.

The successful local development receipt records:

```text
model  a50f4b2eb8c72dd01bfb033f7f8b43f791403369be7667e5ee4f9dd277b06f0f
runner e5b4f0a95823af0dbf2c2d1520b4be254f3be9e04da6731a02cecf0f47005fe7
HEAD   35b4d4101d36288f41f7cb04851f4bf98e0092c5
worktree_dirty: true
source_and_revision_recheck: unchanged
C4_OCCURRENCE_QUINT_ACCEPTED 28 tests; 12 mutations
```

From the repository root:

```sh
python3 tools/check_c4_occurrence_quint.py --output /tmp/c4-finite-carrier-dual-quint
```

From `kernel/`, using its locked environment:

```sh
pixi run --locked mojo run -I . tests/test_c4_finite_carrier.mojo
pixi run --locked mojo run -I . tests/test_c4_two_generation_rank.mojo
```

The runner contains only execution/provenance checks; the mathematical
predicates execute in Quint. The native tests use exact small integer rows
and populations, within the existing kernel arithmetic budgets. None of
these finite controls enumerates all substitutions or represents every
Perron length row.

## 5. Scope retained

Finite support comes from a supplied finite carrier of actual words. It
does not produce global reachable-state finiteness. Interior seriality
uses the exact common positive image scale; it does not prove productivity.
The actual cycle is non-PIP and is no counterexample to C4. A repeated
packet label is not evidence of a shared legal limit or two compatible
recognizable hierarchies.

Mass uses complete ordered lists, including repeated factors and further
inflation of diagonals. Fixed-row escape refutes a **supplied** common
nonzero row under the formal algebraic hypotheses; it does not construct
such a row from phase-flatness. Uniform productive forced crossings,
the common legal limit, general C4, global G1, Concentration and PSC remain
open. No governed claim status changes on the strength of these controls.
