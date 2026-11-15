# C4 address lookup and affine transport: bounded controls

This note records the independent executable controls accompanying the
[literature stop/go](c4-address-transport-literature-2026-11-10.md),
[global-address lookup](c4-occurrence-addresses-2026-11-10.md), and
[occurrence transport](c4-occurrence-transport-2026-11-10.md).
They check explicitly finite domains and actual canonical-kernel fixtures.
They do not prove uniform C4 productivity or classify a Pisot corpus.

**Local status:** the source-bound Quint runner passed all **20 tests** and
all **7 deliberate mutations** below. That receipt records dirty worktree
sources over `main@666e701d7cffde398e1265dd4ee95becf54fef53`; it is not an
exact-head PR acceptance receipt. Native regression assertions are written
and their fixture arithmetic was independently checked using the existing
`reference/psc_research/bpa.py` oracle. **These development checks do not
replace hosted canonical Mojo execution or the new compiled Lean bank.
Exact-head acceptance requires the implementation PR's recorded receipts.**

## Exact finite domains

| Domain | Size and scope |
| --- | --- |
| Binary words of length 2–4 | 28 words; the original newborn controls use all 16 ordered strict balanced parents in this set. |
| Nonerasing binary substitutions with image length 1–2 | Six possible images for each of two letters, hence 36 substitutions and 576 strict-parent/substitution inputs. |
| Positive integer length rows | All nine rows in `{1,2,3}²`; these are geometric controls, not representations of all Perron vectors. |
| Generic ordered chunk lookup | Seven binary chunks of length 0–2, including the empty word; all 400 ordered chunk lists of length 0–3. Their flattened words contain 1,620 in-range global indices in total. Empty and repeated chunks are included. |
| Complete balanced reductions | All 99 ordered balanced pairs among the 31 binary words of length 0–4, including the empty pair. |
| Affine and track-swap transport | All six nonempty binary source words of length 1–2 on each track, all 36 substitutions above, every valid source index and every valid image digit: 1,296 word-pair/substitution inputs and **10,400 actual address/digit choices**. Unbalanced word pairs and non-PIP substitutions are included. |

The model asserts the domain counts. Each `run` evaluates its finite
quantifiers deterministically. `--max-samples=1` therefore means one
execution of the entire stated finite predicate, not one randomly selected
word or address.

## Exact 20-test inventory

The first ten tests are retained from the previous accepted occurrence
bridge; the remaining ten check this address/transport extension.

| Test in `proof/quint/C4OccurrenceBridge.qnt` | Assertion |
| --- | --- |
| `domainCountTest` | Original word, image, length-row and 576-input counts. |
| `allSingletonsGiveNewbornTest` | Every singleton factor from each bounded strict-parent substitution gives an actual interior newborn on one adjacent side. |
| `alignedLetterIsSingletonTest` | Equal selected letters after equal aligned Parikh prefixes delimit a singleton in the complete reduction. |
| `interiorOverlapKeepsOrdinalTest` | Strict physical interior overlap selects the same actual factor ordinal. |
| `boundaryTouchIsInsufficientTest` | Endpoint contact alone can join distinct factor ordinals. |
| `repeatedFactorValuesLoseOccurrenceTest` | Equal factor values at different positions remain different occurrences. |
| `erasureAndSingletonParentControlsTest` | Erasure and a singleton parent do not supply the strict interior newborn conclusion. |
| `parentIrreducibilityIsNecessaryTest` | A reducible parent's interior cut can be inherited. |
| `bothNewbornSidesTest` | Explicit initial/final singleton fixtures require the left/right adjacent synchronization choices. |
| `existentialRouteAllowsAvoidingCycleTest` | An abstract finite graph can have a productive existential route and an avoiding cycle; it is not a realizable PIP graph. |
| `lookupDomainCountTest` | Counts all 400 chunk lists, their 1,620 valid global indices and the 99 balanced pairs. |
| `globalToLocalReconstructionTest` | Every valid flattened index has one containing ordinal; its local index, literal letter, prefix and reconstructed whole word agree. |
| `exteriorAddressRejectedTest` | Negative, endpoint and beyond-end indices select no chunk. The negative case concerns the integer model; Lean indices are natural numbers. |
| `balancedFactorLookupTest` | Generic lookup in both tracks of each complete balanced reduction agrees with its zero-return factor ordinal. |
| `transportDomainCountTest` | Counts the 1,296 word-pair/substitution inputs and 10,400 valid address/digit choices. |
| `literalAffineSquareTest` | Actual inflated positions and selected letters reconstruct the literal prefixes and satisfy `r_next = M r + digit_forcing`. |
| `balancedPrefixTrimmingTest` | Removing the same actual balanced factor prefix preserves the residual for both positions in the selected common child. |
| `trackSwapCovarianceTest` | Swapping tracks, source indices and digits negates the complete affine update and agrees with the swapped literal prefixes. |
| `affineTermsAreNecessaryTest` | Explicit nonzero fixtures require both incidence action and digit forcing. |
| `sameLetterSplitStaysSplitTest` | Valid image digits selecting the same letter can land in distinct balanced children; their affine identity still does not make them a common-child transition. |

The generic lookup model uses a finite interval search, independently of
Lean's recursive `locate`. The transport model counts literal prefixes and
constructs incidence columns from substitution images. The Python runner
only checks execution and provenance; it contains no mathematical kernel.

## Exact seven mutation controls

A mutant is credited only when its listed test reaches the expected
assertion failure (`QNT508`). A parse/type error, missing test, download
failure, timeout or process failure does not count as mathematical rejection.

| Mutation name | Change | Required failing test |
| --- | --- | --- |
| `touch-replaces-interior` | Weaken one strict interior inequality to endpoint contact. | `boundaryTouchIsInsufficientTest` |
| `ordinal-erased` | Replace every selected factor ordinal with zero. | `repeatedFactorValuesLoseOccurrenceTest` |
| `inherited-cut-ignored` | Declare every cut noninherited. | `parentIrreducibilityIsNecessaryTest` |
| `factor-prefix-offset-ignored` | Use the global index as the local index. | `globalToLocalReconstructionTest` |
| `incidence-action-omitted` | Replace `M r + forcing` with `r + forcing`. | `affineTermsAreNecessaryTest` |
| `digit-forcing-omitted` | Replace `M r + forcing` with `M r`. | `affineTermsAreNecessaryTest` |
| `track-swap-sign-ignored` | Retain the residual under track swap. | `trackSwapCovarianceTest` |

## Canonical Mojo fixtures

`kernel/tests/test_target_packets.mojo` now calls two additional tests:
`test_repeated_factor_ordinals_and_address_mutations` and
`test_orientation_sign_and_forcing_mutations`. They invoke the existing
`build_packets`, `make_root`, `descendant`, `verify_packet` and `replay_edge`
implementations. No second production packet implementation is introduced.

All displayed letters and indices are zero-based. The substitution is
`0 → 1, 1 → 02, 2 → 202`. Its actual normalized parent `021 / 102`
inflates to `120202 / 021202`, with complete cuts `[0,3,4,5,6]`.
The first raw child is `120 / 021`, whose normalized orientation has sign
`−1`. The repeated singleton `2 / 2` occurs at ordinals **1** and **3**.

| Selected descendant | Top source/digit | Bottom source/digit | Global positions | Local positions | Factor ordinal |
| --- | --- | --- | --- | --- | --- |
| First `2 / 2` | `(1,2)` | `(2,0)` | `(3,3)` | `(0,0)` | 1 |
| Repeated `2 / 2` | `(2,1)` | `(2,2)` | `(5,5)` | `(0,0)` | 3 |

Both singleton packets have equal letters and zero residual, but replacing
one factor ID, ordinal or source/global/local address with the other's
data must fail literal replay. Choosing digits `(2,2)` from source indices
`(1,2)` gives the same selected letter at global positions `(3,5)`; both
digits are valid, but `descendant` must reject the split. A root index at
the word's length and an image digit at its image's length are also rejected.

Two orientation cases avoid a zero-residual or equal-index blind spot:

| Source indices; digits | Child positions | Selected letters | Physical residual | Child sign |
| --- | --- | --- | --- | --- |
| `(1,0)`; `(0,1)` | `(1,1)` | `(2,2)` | `(-1,1,0)` | `−1` |
| `(1,1)`; `(0,0)` | `(1,2)` | `(2,1)` | `(-1,1,-1)` | `−1` |

A complete physical swap exchanges both addresses and letters and negates
the residual. The unequal-index case must also exchange packet key positions
`(1,2) → (2,1)`. Keeping the unswapped key indices must fail replay even
after the other fields are correctly swapped. The equal-index case has
nonzero digit forcing `(-1,0,0)`; deleting it from the stored edge must fail
`replay_edge`.

## Provenance and replay

The runner pins Quint **0.33.1**, the TypeScript backend and seed **20261110**.
It reads one source snapshot, records the model/runner SHA-256 and Git HEAD,
typechecks an immutable private copy, verifies the exact ordered 20-test
inventory, and checks each mutant's single declared assertion. Before
accepting, it rechecks model bytes, runner bytes and Git HEAD. Receipt schema
`psc-c4-occurrence-quint-v2` reports whether the source worktree is dirty.

The successful local snapshot has:

```text
model  a3193227f8fca872e994c4aaa3da39cfa0d1be647a8169529a4907759a553cee
runner 0b826b4c15a0ab040ee367fdd4c2ed1894b7937b0a06949fccd10dfa5a026e6b
HEAD   666e701d7cffde398e1265dd4ee95becf54fef53
worktree_dirty: true
C4_OCCURRENCE_QUINT_ACCEPTED 20 tests; 7 mutations
```

From the repository root:

```sh
python3 tools/check_c4_occurrence_quint.py --output /tmp/c4-address-transport-quint
```

From `kernel/`, using its locked environment:

```sh
pixi run --locked mojo run -I . tests/test_target_packets.mojo
```

The dedicated C4 workflow runs both commands on the PR checkout. Acceptance
must identify that exact head and the completed jobs; the local dirty receipt
cannot replace them or the compiled new-module axiom audit.

## Scope boundary

The Lean finite-path result supplies a coherent chosen address history for
finite reachability. Its existential digit relation does not preserve an
external prescribed digit/state transcript by itself. The separate fixed
digit constructor and normalization-frame theorems state their own stronger
one-step properties. Raw addressed paths do not supply production graph IDs,
interning completeness or an infinite-path lifting theorem.

Formal `Packet.Diagonal` means equal letters and zero residual. Production
`target_packets.success` additionally uses an interior left factor boundary
and its configured target/synchronization filter. They are not identified by
these controls. The newborn theorem handles an initial singleton through
the adjacent `SyncMinus` boundary when needed. The supplied-`StrictSystem`
adapter excludes diagonal routes conditionally; it does not establish that
an arbitrary PIP forced crossing has a productive route.
