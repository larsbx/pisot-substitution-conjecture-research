# Forward-carrier verification refinement: pre-code addendum

Decision: **proceed with a checked refinement of the existing finite
carrier predicate, using unique irreducible factorization**. This note
was written before `FastForwardCarrier.lean`. It supplements the
[three-primary-source stop/go decision](c4-forward-carrier-literature-2026-11-12.md)
without changing its mathematical claim or acceptance requirements.

## Why the direct checker needs refinement

The proposed native packets in
[`fixture0.json`](../evidence/c4-forward-carrier-2026-11-12/fixture0.json)
and [`fixture1.json`](../evidence/c4-forward-carrier-2026-11-12/fixture1.json)
are much larger than the generic controls. The recorded sizes are:

| Fixture | Normalized states | Ordered states | Maximum word length | Total track letters |
| --- | ---: | ---: | ---: | ---: |
| `1/021/001` | 97 | 192 | 35,437 | 886,556 |
| `1/012/001` | 261 | 520 | 4,872 | 337,020 |

The first required a length budget of 100,000; the second closed within
10,000. These are native proposal data, not Lean acceptance. Directly
evaluating `Reduction.redAux` repeatedly appends growing prefixes and
tests their permutation equality. Recomputing that reduction for every
long parent is an unsuitable concrete proof strategy. Literal `Fin 3`
constructors for every letter also create avoidable elaboration work.

## Refinement contract

The existing
[`Reduction.red_unique`](../proof/PscVerif/PscVerif/Reduction.lean)
already proves that a list of nonempty irreducible balanced pairs is the
actual reduction whenever its top and bottom tracks concatenate to the
two source words. Use this theorem rather than executing `redAux`.

An indexed packet provides ordered state words, complete ordered rows of
child indices, and indices witnessing every ordered swap seed. Check:

1. every state is an `IsBlock`, using the streaming checker below;
2. each noncoincident parent's decoded child tracks concatenate exactly
   to the literal substitution of its top and bottom words;
3. each coincidence has an empty terminal row;
4. every unequal ordered letter pair decodes at its seed index to the
   actual swap seed.

All row indices have type `Fin n`. The state lookup may use the existing
balanced-table interface; no table injectivity or discovery assumption
is needed for a finite closed upper bound. The checker establishes
literal row equality with `red` through `red_unique`, then recovers the
original `ForwardCarrier.Valid` proposition. Its original checker
equality can therefore be proved by refinement without reducing the
slow checker on these inputs.

## Streaming irreducibility obligation

Read the two tracks together with three integer counters. After each
letter pair `(a,b)`, add one to coordinate `a` and subtract one from
coordinate `b`. Reject unequal ending positions. Reject a zero counter
vector at every positive proper prefix, and require zero at the final
endpoint. Require a nonempty top track.

The proof invariant relates the counters to exact letter counts. For an
initial counter vector `d` and remaining words `u,v`, use

```text
for every c, d[c] + count(c,u) = count(c,v).
```

Removing the next letters updates `d` by their signed unit vectors.
Induction proves final balance, equal track lengths and the absence of
all positive proper balanced prefixes. At zero initial counters this
is exactly the existing `IsBlock` proposition. This soundness theorem
must be proved; an optimized Boolean scan without this refinement is
not evidence.

For a fixed three-letter alphabet, scanning uses a constant number of
counter operations per letter. All state scans and literal row
concatenation comparisons take `O(L + L_image)` arithmetic/letter
operations, with `O(E log n)` lookup overhead if a balanced state table
is used. Here `L` is total state-track length, `L_image` is the total
length of substituted nonterminal tracks, and `E` is the number of
indexed child occurrences. Integer bit costs and proof-kernel overhead
remain; no elapsed-time or complete acceptance claim follows from this
operation count.

Compact string literals may decode only `0`, `1`, and `2` to typed
letters. Any invalid word must fail the entire proposed decoding; an
empty fallback cannot pass seed coverage. Decoding must be shared or
attached to individual word constants, not repeated for the whole
corpus on every indexed lookup. Decoder definitions remain ordinary
kernel computation. Use neither `native_decide`, a new axiom, a stub,
nor an unchecked external result.

## Source and control boundaries

The three sources in the original decision continue to provide the
relevant mathematical boundary: finite factor closure is distinct from
coincidence productivity, the literal balance relation is fixed, and
spectral conclusions need additional hypotheses. This refinement adds
no new dynamical theorem. Its key local input is the already proved
uniqueness of the complete irreducible factorization.

Controls must reject an unbalanced endpoint, unequal track lengths, a
proper balanced prefix, and a row with an omitted factor or incorrect
literal concatenation. A balanced but reducible whole substituted pair
must not be accepted as one irreducible child. Empty coincidence rows
and genuine singleton coincidences remain valid. Seed coverage and the
Thue–Morse finite/nonproductive distinction remain in force.

Row-range checks may reuse the existing `checkAt`/`checkRange` pattern
from `ArchivedPayload`, allowing kernel proofs to be split without
changing their conjunction. All concrete row checks, generic refinement
proofs, exact source bindings and compiled axiom audits still require
acceptance. The original states-only module remains unchanged while its
separate compilation runs. No G1 or termination status is promoted by
this design decision.

## Concrete payload interface

`FastForwardCarrier.decodeWord` returns `Option Word`, and `word` takes
the empty fallback. Generate separate per-word or per-state constants,
then a shared array of references. Each `Packet n` contains:

```text
state : Fin n -> (Word x Word)
rows  : Fin n -> List (Fin n)
seed  : Fin 3 -> Fin 3 -> Fin n
```

Only the six unequal letter pairs constrain `seed`; its diagonal values
may use any valid state index. Emit row indices with explicit proofs of
their bounds. Every listed state, even an unreachable extra state, must
pass the nonempty irreducible-block check, so a failed word decoder
cannot disappear behind the finite-superset allowance.

The aggregation interface is:

```text
p.checkRange sigma start count = true
p.checkRange_append sigma start a b firstRange secondRange
p.valid_of_range sigma seedProof completeRangeProof : p.Valid sigma
p.finite_bpaStatesNC sigma validityProof
```

The resulting `forward_valid` and `forward_check` theorems recover the
original states-only specification for `List.ofFn p.state`. These are
proofs from the refinement, not instructions to evaluate the original
slow checker. The packet may use literal substitution functions and
import the lightweight generic module only. Identification with the
named fixture definitions, and composition with validated strict
exclusion, remain separate consumers.

## Discriminating packet controls

[`FastForwardCarrierControls.lean`](../proof/PscVerif/PscVerif/FastForwardCarrierControls.lean)
uses the constant substitution `sigma(a) = [0,1]`. Its complete positive
packet contains the six ordered swap seeds plus `([0],[0])` and
`([1],[1])`. Each seed's actual ordered row is `[6,7,6,7]`; both
coincidences are terminal. This calibrates the full validity and
finiteness consumers without a Pisot claim.

The seven-state negative packet replaces the two singleton coincidences
by one pair `([0,1,0,1],[0,1,0,1])` and gives every seed the singleton
row `[6]`. All six seed rows pass literal concatenation and the seed
binding passes. The last row is correctly empty because its tracks are
equal. Nevertheless that last pair has a proper balanced prefix, so its
block check fails and the complete range is rejected. This isolates why
every child state must be checked: accepting only the six parent rows
would incorrectly identify a reducible factor as the actual reduction.

Additional controls remove a factor, collapse repeated occurrences to
support, add an occurrence, and reorder the same child multiset. An
identity-substitution packet accepts its own ordered child but rejects
the track-swapped child. Reusing the constant substitution's rows for
the identity substitution also fails literal source checking.

## Focused development status

The generic fast module passed the pinned Lean `v4.34.0-rc2` focused
compiler at source SHA-256
`fc6f17114b7c38513b8b05f7c406df7b05a0ac53880aa73b5caa93bcfd3159af`.
Attempt 1 failed on two Boolean-lemma names; replacing
`Bool.and_eq_true.mp` with the pinned
`Bool.and_eq_true_iff.mp` yielded attempt 2, exit zero in approximately
3.4 seconds. The original failed receipt is preserved. The streaming
proof, compact decoder controls, indexed factorization proof and range
aggregation all compiled; no `native_decide`, new axiom or placeholder
was used.

The separate packet-control module also passed the pinned focused
compiler, unchanged, at source SHA-256
`5a1fe7b40c3336cfa8df07045e27d560b63de8747b761c0001772691e0c39e47`.
Its first attempt exited zero in 8.253 seconds with no diagnostics. All
eleven control theorems compiled, including the complete positive
finiteness consumer and the reducible-child rejection whose six parent
rows separately pass.

These development compilations have a separate successful scoped
transitive-axiom audit. It inspected 172 owned declarations and 96
theorem declarations, including generated helpers, across
`ForwardCarrier`, `FastForwardCarrier`, and `FastForwardCarrierControls`.
All 50 source-listed proofs, including the private counter helper, were
reached. Only `propext`, `Classical.choice`, and `Quot.sound` were allowed;
no local or unexpected axiom occurred. Exact source and object hashes
were checked before and after the 10.287-second successful run.

The final staged whitespace check then found one extra blank line at
the end of this module. Removing exactly that newline left every
declaration and its location unchanged. The cleaned source,
`fba7b08223e333d9380ff1e090ad85cad6aadbe8eadd1a2dde8d6b92bfcf0689`,
passed a fresh focused compile in 13.462 seconds. A new scoped audit
bound that source and its new object, again reached all 50 source
proofs across 172 declarations, and exited zero in 2.255 seconds.
The original source snapshots, failed whitespace check and both audit
runs remain preserved.

This scoped audit uses cached dependencies and excludes both concrete
data modules and the named wrapper. It is not complete isolated
acceptance or acceptance of either named carrier. The generated data
require their own recorded outcomes. The generic mathematical content
is unchanged; current claim status remains unchanged. The
[evidence packet](../evidence/c4-forward-carrier-2026-11-12/README.md)
records the successful and unsuccessful attempts separately.
