# Forward-carrier kernel encoding repair

Pre-code decision: **preserve the reviewed carrier predicate and replace
only its generated data representation**. This is a performance repair
under the existing [forward-carrier refinement decision](c4-forward-carrier-fast-addendum-2026-11-12.md),
not a new dynamical construction or a stronger mathematical claim.

## Observed problem

The preserved development record has unsuccessful concrete Lean checks
and a definitions-only timeout. Native carrier closure and a generated
source file do not establish successful Lean checking. The new diagnostic
also distinguishes frontend instrumentation failures from proof failures.

The generated state and row array accessors currently simplify the whole
array expression to establish an index bound. The bound is already
definitionally the `Fin` index's own proof. Use that proof directly.

More substantially, each generated word currently asks the kernel to
decode a long UTF-8 string before checking the carrier. The intended
streaming scan is not a guarantee about the cost of string conversion in
kernel reduction. A preliminary isolated probe of the unchanged decoder
took 8.408 seconds for 100 letters; larger probes and complete carrier
checks require their own terminal receipts.

## Lossless replacement

Partition each literal top and bottom word into successive chunks of at
most 32 letters. Intern equal chunks in first-occurrence order, traversing
states in their existing order and each top track before its bottom
track. Emit each distinct chunk once as a typed `List (Fin 3)` literal.
Represent a state word by flattening its ordered list of chunk references.
The canonical Mojo exporter performs this representation change.

This changes no letter, state order, child index, seed, substitution,
resource budget, or carrier-checking proposition. The chunk decoder has
no string fallback: each emitted letter is explicitly checked to be in
`{0,1,2}` before source emission. The existing generic string decoder and
its invalid-digit controls remain available and unchanged.

An independent count over the original packets gives 229 distinct
32-letter-or-shorter chunks containing 5,034 letters for fixture 0, and
491 chunks containing 10,695 letters for fixture 1. The complete words
still contain 886,556 and 337,020 track letters. Sharing changes the
representation; it does not shrink the mathematical objects being checked.

## Acceptance and controls

The changed exporter must reproduce the two original JSON packets
byte-for-byte. Its Lean output must reproduce the committed generated
modules. Independent reconstruction of every generated chunk reference
must give the complete original ordered top and bottom tracks, with
malformed letters, unknown references, missing chunks and incorrect
flattening refused. The normal native/oracle controls remain required.

All original kernel row checks, seed checks, refinement consumers and
axiom restrictions remain in place. Only a terminal compilation of both
concrete modules and their consumers can establish formal acceptance.
Cached-dependency development builds are reported separately from the
complete isolated gate. No governed claim status changes through this
encoding repair.

## Initial repair replay

The rebuilt pinned Mojo exporter regenerated both original JSON packets
byte-for-byte. The SHA-256 digests remain
`1f0e32301807023239a7d8eabdbbabf71d60c9956a96ccbc8f25b7bc8358d04f`
and `65a78cba7b94e5b48e06e4f6617eb96e4f43f623e61b68ab97cb07dbd472fe0e`.
The newly generated Lean files use the same state and child ordering.

The focused Python suite passed 182 tests. Its 14 new controls reconstruct
every state word from the actual generated source and reject six kinds of
corruption for each fixture: empty chunks, nonternary letters, omitted
chunks, unknown references, missing flattening and reordered references.
Every refusal test establishes the complete valid baseline before its
rejection catcher. These results concern representation and finite native
replay; they do not confer Lean acceptance.

Isolated representation probes subsequently checked typed literal list
lengths of 1,000 and 10,000 in 4.485 and 14.287 seconds, while the original
1,000-letter string decoder probe reached its 91.309-second timeout.
The unchanged generic scan on a real irreducible 10,946-letter word,
represented by shared 32-letter typed chunks, passed in 52.922 seconds.
These probes motivate complete replay; they are not a time bound or a
substitute for either full carrier certificate.

Cold cached-dependency imports also matter: the first actual fixture-1
development compilation reported 161 seconds in its import stage. Earlier
new 150/180-second diagnostic stops did not localize a declaration cost,
and the first marker experiment had an `IO`/`BaseIO` instrumentation error.
Those unsuccessful probes remain diagnostic history, not mathematical
counterexamples or successful proof checks.

## Explicit proof-only definitions

The first actual fixture-1 compilation of the typed-chunk source terminated
with compiler return code `-9` (SIGKILL) after 1,576.880 seconds. Its sampled
maximum resident memory was 4,353,761,280 bytes. Neither the local time guard
nor the memory guard fired, so the cause of the signal is unconfirmed. The
source remained unchanged, no object was produced, and the log reported no
Lean proof error. This failed replay is retained; it is not formal acceptance.

The next representation-only change explicitly marks the generated closed
data definitions, and their named `checkedStates` consumer, `noncomputable`.
In the pinned Lean v4.34.0-rc2 compiler source
(`Lean/Elab/PreDefinition/Basic.lean`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`), `shouldGenCodeFor` skips native
code generation for a definition whose explicit modifier is noncomputable.
An enclosing `noncomputable section` alone does not implement that rule.
The ordinary transparent kernel definition is still added and checked before
this compilation decision. The generic Boolean checker and every
`decide +kernel` obligation stay unchanged.

This removes unused native compilation of proof-only payloads; it does not
establish a measured speedup or guarantee a successful replay. Bounded
Init-only prefix comparisons ended before producing objects and had unequal
post-import budgets, so they do not establish a comparative timing result.
The regenerated literal words, original packet bytes, and refusal controls
must be checked again, followed by new terminal concrete Lean compilations.
Earlier native checks remain evidence for their earlier exact sources only.

The rebuilt exporter reproduced both original JSON packets byte-for-byte.
Removing only the new explicit modifiers and explanatory comment from its
Lean output reproduces the previous typed-chunk modules exactly. The new
source digests are
`019856bf4e01550382be9e2607d28a126b36da66c0533929c550e26a2c171d1a`
for fixture 0 and
`4d1d3a9a1d16b04536ec12dba5e1e55a86b2a37d5dd27cc75a5d8b9661500844`
for fixture 1. The complete focused suite then passed 186 tests in 59.648
seconds, including removal controls for the required chunk and state
declaration modifiers. Concrete Lean acceptance is still pending.
