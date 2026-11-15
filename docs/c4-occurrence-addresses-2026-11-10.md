# C4: global positions to actual factor occurrences

**Baseline:** `main@666e701d7cffde398e1265dd4ee95becf54fef53`, after
[PR #533](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/533).
The preceding [targeted literature stop/go](c4-address-transport-literature-2026-11-10.md)
approved this finite-word refinement before its proof code was written.

The new source is
[`PscVerif.OccurrenceAddress`](../proof/PscVerif/PscVerif/OccurrenceAddress.lean).
It constructs an actual selected factor occurrence from an in-range global
letter index. This discharges the prelocated-occurrence premise of the
[previous common-factor theorem](c4-concrete-occurrence-2026-11-10.md): callers
can now supply positions in the two complete words, rather than supply the
factor ordinal, selected letter and local decomposition themselves.

## Exact theorem interface

| Declaration | Input | Conclusion |
| --- | --- | --- |
| `locate` | Ordered chunks `ws`, global natural index `n` | Executable optional pair `(factor ordinal, local index)`; empty chunks are skipped. |
| `locate_eq_some_iff` | A proposed result `(j,k)` | The result is equivalent to an actual chunk at ordinal `j`, `k` strictly within that chunk, and `n = prefixLength ws j + k`. |
| `locate_eq_none_iff` | Any global index | Lookup fails exactly when `ws.flatten.length ≤ n`. |
| `lookup`, `lookupTrack` | A proof that the global position is in range | Total executable lookup; no fallback occurrence is returned. |
| `locate_unique`, `TrackAddress.unique` | Two valid decompositions of the same global position | Both the ordinal and local index agree; the selected object at that ordinal also agrees. |
| `locate_prefix`, `TrackAddress.prefix_eq` | A valid address | The global prefix is exactly the concatenation of preceding chunks and the local prefix. |
| `locate_letter`, `TrackAddress.selected` | A valid address | Lookup selects the actual letter at the original global position. |
| `locateTrack` | A global index in a ternary track concatenation | The existing `OccurrenceNewborn.FactorOccurrence`, including its actual ordinal and literal prefix/letter/suffix split. |
| `locateTrack_start`, `locateTrack_finish` | Any real length row | The constructed occurrence has the original tile's physical start and end. No positivity hypothesis is needed for these identities. |
| `redTop`, `redBot` | A balanced word pair and an in-range position on one track | A concrete occurrence in the complete `Reduction.red`, using `red_top` or `red_bot` to establish completeness. |
| `red_common_factor_lookup` | Two valid global positions, positive tile lengths and strictly intersecting physical interiors | Their computed occurrences have the same factor ordinal and the same factor value. |
| `locateSubst` | An in-range position in a substituted word | An actual source occurrence and a valid within-image digit, with exact global-index, prefix and selected-letter reconstruction. |
| `locate_subst_position` | A valid source index and valid image digit | The forward inflated position resolves back to precisely that source index and digit. |

The list layer is generic over alphabets and over the objects whose tracks
are concatenated. It needs neither decidable letter equality nor nonempty
chunks. The adapter into the existing physical occurrence structure is
ternary because that structure uses `Fin 3` and a real three-letter length
row.

## Derivation and occurrence identity

For an ordered list of chunks `ws`, define

\[
 L(j)=\sum_{t<j}|ws_t|.
\]

The algorithm examines the first chunk. A position inside it returns
ordinal zero; otherwise it subtracts that chunk's length, recursively
resolves the remaining list, and increments the returned ordinal. This
recursion decreases the list even for an empty chunk.

The exact lookup specification proves that the selected local index is
strictly inside its actual chunk and that `n = L(j) + k`. Consequently a
position on a chunk boundary belongs to the following nonempty chunk. The
exterior endpoint at the entire word's length has no selected letter.
Repeated equal chunks do not become interchangeable: their different
ordinals have different preceding lengths, and the same global position
cannot satisfy two different valid ordinal/local-index decompositions.

The proof reconstructs the original chunk list as its first `j` chunks,
the selected chunk, and the remaining chunks. Flattening this decomposition
gives the exact prefix identity

\[
 \operatorname{take}_n(\operatorname{flatten}(ws))
 =\operatorname{flatten}(\operatorname{take}_j(ws))
   \mathbin{+\!+}\operatorname{take}_k(ws_j).
\]

This is a literal word equality, stronger than equality of letter counts
or physical lengths. The selected-letter theorem similarly preserves the
letter at the numerical global position. Applying physical length to the
prefix identity gives the physical start identity used by the existing
factor-containment theorem.

For a balanced pair `(u,v)`, `red_top` and `red_bot` already prove that the
complete reduction concatenates to `u` and `v`. The new total adapters use
those equalities to construct each selected occurrence. The previous
`red_common_factor` theorem can then compare their physical interiors and
deduce a common ordinal. Thus the new theorem removes the caller's need to
guess or assume a containing factor. It retains the genuine geometric
condition: the tile interiors must strictly intersect. Endpoint contact
does not establish a common factor occurrence.

## Substitution addresses

Apply the same list lookup to the chunks `w.map s`. Its returned ordinal
is the source-letter index, its factor is that actual source letter, and
its local index is the digit in that letter's substituted image. The
result includes

\[
 n=|s(w[0:i])|+p,
 \qquad
 s(w)[0:n]=s(w[0:i])\mathbin{+\!+}s(w_i)[0:p].
\]

`locate_subst_position` proves the converse lookup identity for every
valid source index and digit. These assertions allow erasing images away
from the selected digit: a valid digit already establishes that its own
image is nonempty. Nonerasure remains required by the earlier
interior-newborn result, where it provides additional length information.
It is not silently imposed on this finite address identity or the affine
finite-reachability lift.

This source/digit address and the reduced-factor address resolve the same
global position. Their prefixes and selected letters therefore refer to
the same actual descendant. The affine transport module can use these
identities to relate digit transitions to concrete reduced occurrences;
an arbitrary algebraic packet tuple is still not automatically such an
occurrence.

## Verification and boundary

The full production target `lake build PscVerif.OccurrenceAddress` compiled
successfully against the pinned project toolchain. The generic lookup and
substitution portions were also checked in narrow helpers; the complete new
module body was checked with the unchanged accepted physical definitions
and proofs copied into a narrow helper, without stubs or added axioms. The
integrated PR verification additionally records the complete proof-bank
build and compiled axiom audit. Three finite Lean controls distinguish
repeated equal chunks, empty chunks, and the last valid position from the
exterior endpoint. They supplement the universal proofs rather than
replace them.

The result settles finite global-address lookup, uniqueness, reconstruction
and physical start preservation. It also gives exact source/digit lookup
for a single substitution step. It does not prove completeness of every
packet edge, consistent lifting of arbitrary quotient paths, productive
paths from forced crossings, global G1 extraction or general C4. Those
remain separate obligations.
