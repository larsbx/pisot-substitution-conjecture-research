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

## Shared checked indices and singleton row checks

The explicit-noncomputable fixture-1 replay then reached its fixed local
resident-memory guard. The runner sent SIGTERM and recorded return code
`-15`, stop reason `rss_guard`, elapsed time 1,463.923 seconds, and sampled
maximum resident memory 4,087,095,296 bytes. The source was unchanged and
no object was produced. This controlled stop is distinct from the earlier
unexplained SIGKILL; neither result establishes a Lean proof error or
formal acceptance.

A separate Init-only probe extracted the actual fixture-1 `RowsArray`
declaration. Its 4,386 literal child references repeatedly elaborated
checked `Fin 520` bounds, and it reached a 90.101-second timeout without
an object. A second probe shared its 518 used indices as explicitly
checked noncomputable constants and compiled in 5.458 seconds. Expanding
those aliases reproduces the original row declaration byte-for-byte.
This supports sharing repeated checked bounds; it does not establish the
earlier full-run kill's cause or a controlled end-to-end speedup, and it
does not confer carrier acceptance.

The canonical emitter now declares every `fixtureNIndexK : Fin n` once
using the original explicit `⟨K, by decide⟩` bound. Rows and ordered seed
branches reference those constants. It emits all indices from zero to
`n - 1`, including indices not used in a row, so this inventory is complete
and independently checkable. No modulo coercion, default index, unchecked
bound, or changed row occurrence is introduced. Expanding the emitted
aliases reproduces both prior row and seed definitions exactly.

The unchanged `Packet.checkRange` obligations are also divided into
singleton rows for both fixtures. Their proofs are combined by the
existing `checkRange_append` and `valid_of_range` theorems. No whole-range
`decide` is added after that composition. This limits the work bundled in
one kernel obligation without weakening the carrier predicate; its full
resource behavior remains subject to replay.

The freshly rebuilt exporter again reproduced both original JSON packets
byte-for-byte. Its new Lean source digests are
`9194992968eca8ec61de9c8d3c0d1a0a78adabe166adc770240591b18c45b991`
for fixture 0 and
`7770595c93011209cad16d9e0f8acc670f9e24b8aa3dbc74429555f442d84d07`
for fixture 1. Independent controls must require complete checked-index
inventories, original row occurrences and ordered seeds, and complete
singleton range coverage. The new actual replay remains a separate gate.

The fresh complete native gate passed in 65.908 seconds, including 230
tests in 61.04 seconds. Its 44 added controls reconstruct all row occurrences
and the six ordered seed witnesses from the actual aliases, check the
original explicit bounds and state order, require every singleton range,
and reject corrupted aliases, rows, seeds and range coverage. Both native
JSON and Lean outputs regenerated byte-for-byte, and the source and binary
snapshots stayed unchanged throughout that gate. These receipts establish
the exact finite representation and native replay scope, not Lean acceptance.

Future focused runs record `-Dtrace.Kernel=true` to identify completed
kernel declarations. A small Init control verified that this reports
declaration names without printing payload bodies. Direct file output
buffered the traces; `stdbuf -oL -eL` exposed completed boundaries during
the run and produced the identical control object. That wrapper and the
exact command are recorded explicitly. A completed-declaration trace
does not identify an unfinished declaration with certainty.

## Separate literal modules with Init imports

An Init-only probe then compiled the exact 1,536 current fixture-1 data
declarations in 39.513 seconds with sampled maximum resident memory
780,099,584 bytes. It included the literal chunks, states, checked indices,
rows and seed selector, but no substitution, packet, row predicates or
carrier theorem. This proves only that the extracted data can be checked
in that smaller import context; it does not establish the cause of the
larger-module resource behavior or a controlled end-to-end speedup.

The current full fixture-1 diagnostic run was deliberately stopped before
the module split. Its terminal receipt records `controlled_stop`, reason
`requested_stop`, SIGTERM `-15`, 590.831 seconds, sampled maximum resident
memory 3,485,392,896 bytes, unchanged source and no object. It is a retained
cancellation receipt, not a failed proof or accepted certificate.

The canonical `--lean-data` mode now emits
`NamedForwardCarrierWords0.lean` and `NamedForwardCarrierWords1.lean` with
only `import Init`. They contain the same data declarations under the same
`Psc.GeneratedForwardCarrier` namespace and options. The existing `--lean`
mode emits the corresponding checker module with explicit imports of its
own Words module and `FastForwardCarrier`. The substitution, packet,
seed predicate proof, singleton row proofs, aggregation and conclusions
stay in that checker. Direct byte comparisons establish that every moved
data declaration and every retained proof declaration is unchanged.

The JSON mode remains byte-identical for both original packets. The split
sources have the following SHA-256 digests:

| Source | SHA-256 |
| --- | --- |
| `NamedForwardCarrierWords0.lean` | `6583596c0d3d21a11a3e283954ec4c8ad72572969155e406bb2cd6f6baceb72a` |
| `NamedForwardCarrierWords1.lean` | `a44fee6794080f4f0cde90167c862476b6022115a7e3120078dff042c153702b` |
| `NamedForwardCarrierData0.lean` | `5026901eb6a7f9c2500f38f7835aa96a235c6eb0e5722da1084a45fb83b2b905` |
| `NamedForwardCarrierData1.lean` | `a49d8fa4146b534cff95259beab31a06903088184676704c239eb11b98cc4c0a` |

The actual generated Words modules must compile separately with exact
source/object receipts before a checker replay. The checker receipt binds
the imported Words object as well as the checker source. Independent
reconstruction follows only the explicit expected fixture import and
checks the same complete literal contract across both source files.

For subsequent focused runs, `-j 2 -DElab.async=false` keeps declaration and
kernel checking synchronous while allowing a second worker to complete
frontend reporting tasks. A tiny control verified all six completed
declaration names were visible before a later two-second IO wait finished;
it produced the same object as the one-worker control. This improves the
diagnostic reporting in that control without supplying a new mathematical
premise or establishing a performance comparison for the carrier modules.

The two actual generated Words modules subsequently compiled serially with
exit code zero and unchanged sources. Their terminal receipts are:

| Module | Elapsed seconds | Maximum sampled resident bytes | Object SHA-256 |
| --- | ---: | ---: | --- |
| `NamedForwardCarrierWords0` | 35.010 | 741,531,648 | `26922864e4a01f5b0004387deea57c3a9bdc51ba7a4cddb70656d4e461f23fa7` |
| `NamedForwardCarrierWords1` | 35.024 | 744,415,232 | `a812f56bf162e515d1641b6f01cbfb412d1b428fcaffe898dd4ba5b2cc08c67a` |

These are checks of the actual generated payload modules, beyond the
earlier extracted prefix probe. They still do not establish the carrier
predicates, which remain in the separate checker modules.

The fresh full native split-data gate then passed in 110.236 seconds,
including 258 tests in 101.12 seconds. Both original JSON packets and all
four Lean modules regenerated byte-for-byte while the source and binary
snapshots stayed fixed. The added controls reject wrong, duplicate or
missing payload imports, fixture substitutions and namespace mismatches,
before reconstructing the complete literal contract across the two modules.
The actual checker replay is recorded separately, with its exact imported
Words object bound in the start receipt.
