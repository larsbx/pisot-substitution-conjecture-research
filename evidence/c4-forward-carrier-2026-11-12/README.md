# Two named forward balanced-pair carriers

This packet records canonical Mojo construction and independent literal
replay of finite forward carriers for `1/021/001` and `1/012/001`. It
also records development compilation of the generic Lean specification,
its streaming refinement, and discriminating packet controls. Concrete
Lean acceptance and complete named-chain acceptance are separate gates.

The change is based on `2f7c058fdd50ff65fbcf00543bece49913d47ad5`
(PR #565). Local runs use that base plus the source bytes identified in
their receipts; they are not represented as hosted checks of a later
publication commit. The publication's parent already contains the
private-proof audit repair from PR #560.

## Constructed carriers

| Literal substitution | Normalized states | Exported ordered states | Maximum state-word length | Ordered child occurrences | Repeated occurrences beyond row support | Terminal states |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `1/021/001` | 97 | 192 | 35,437 | 5,652 | 4,456 | 2 |
| `1/012/001` | 261 | 520 | 4,872 | 4,386 | 1,350 | 2 |

Both exports contain all six ordered swap seeds. The canonical builder
works up to track swap; the exporter includes both ordered orientations
and each diagonal once. It reconstructs every complete ordered child
row for the literal substitution. Repetition counts above are
`sum(len(row) - len(set(row)))`; no factor occurrence is discarded.
The displayed state counts describe these exports, not a theorem that
every valid finite upper bound has that size.

The normalized-state budget was 20,000. Fixture 1 closed within a word
length budget of 10,000. Fixture 0 refused that budget, emitted no
certificate, and then closed with the explicitly larger budget of
100,000. The refusal is inconclusive; it is not evidence of infinitude.
The replay additionally forces the state-budget refusal at one
normalized state and checks its distinct diagnostic.

The complete raw packets are [fixture0.json](fixture0.json) and
[fixture1.json](fixture1.json). Their SHA-256 digests are respectively
`1f0e32301807023239a7d8eabdbbabf71d60c9956a96ccbc8f25b7bc8358d04f`
and
`65a78cba7b94e5b48e06e4f6617eb96e4f43f623e61b68ab97cb07dbd472fe0e`.

## Work shown

### Assumptions and hypotheses

The generic `ForwardCarrier.Valid` proposition requires all actual
ordered swap seeds and closure under actual `ChildNC` children of each
listed noncoincident pair. A finite closed superset suffices; discovery
history, injectivity and exact minimality are unnecessary.

The indexed three-letter refinement additionally checks that every
listed pair is a nonempty irreducible balanced block, including any
unreachable extra state. Each noncoincident row must concatenate to both
complete substituted tracks. Coincidence rows must be empty. Explicit
`Fin n` bounds prevent out-of-range indices from being interpreted
modulo the state count.

The named consumers bind the generated substitution functions to the
canonical fixture definitions by literal definitional equality.
Termination consumers retain the original archive's `p.Valid` premise
and membership in the actual ordered seeds or their `ChildNC`
descendants. Forward closure and strict-system exclusion remain
independent inputs.

### Derivation / reduction

The finite-list specification gives closure along every finite
`ChildNC` path by induction, hence finite seed-generated reachability.
The fast checker scans the two words with three unbounded integer
counters. Zero displacement occurs only at the final positive prefix;
the proved invariant supplies actual `IsBlock`.

Complete literal row concatenations, together with irreducibility of
every indexed child, satisfy the existing `Reduction.red_unique`
theorem. Thus supplied rows are the complete actual reductions,
including occurrence order and multiplicity. The refinement derives
the original states-only checker equality without evaluating its slow
growing-prefix reduction on the long concrete words.

The [pre-code source decision](../../docs/c4-forward-carrier-literature-2026-11-12.md),
[pre-code refinement addendum](../../docs/c4-forward-carrier-fast-addendum-2026-11-12.md),
and [derivation and named API](../../docs/c4-forward-carrier.md) record the
literature boundary, proof obligations and precise theorem scope.

### Evidence and replay

The pinned Mojo compiler built the new native controls and exporter.
The final native/oracle replay reproduced both JSON packets and both
generated Lean modules byte for byte, checked both budget refusals,
ran the independent oracle under `python -O`, and passed **168 tests**.
This replay used explicitly supplied binaries, whose earlier build
receipts bind their sources and compiler; it does not claim a fresh
Pixi build. The new CI workflow performs the locked build itself.

The independent Python checker implements its own prefix-count cuts.
It rejects duplicate JSON keys, Boolean-as-integer fields, malformed
words, wrong literal substitutions, incomplete rows, missing seeds,
wrong orientations and inconsistent metadata. It permits a finite
closed superset and a consistent reindexing. CLI failure remains
atomic under normal Python and `-O`.

The generic checker, fast refinement and eleven packet-control theorems
have successful focused development compilations with the pinned Lean
`v4.34.0-rc2`. These use cached dependencies and are not a replacement
for the unchanged isolated repository gate.

A separate scoped compiled transitive-axiom audit passed for those
three modules: **172 owned declarations, 96 theorem declarations
including generated helpers, and all 50 source-listed proofs**. It
reached the private counter helper and found no local or unexpected
axiom; the allowlist was `propext`, `Classical.choice`, and `Quot.sound`.
The initial audit exited zero in 10.287 seconds. After a final
whitespace-only source cleanup, a fresh compile and a second audit
bound the cleaned source; the audit again passed all 172 declarations
and 50 source proofs in 2.255 seconds. Both audit runs are preserved.
Their scope excludes both generated data modules and the named wrapper.

The first concrete fixture-1 attempt used plain `decide` and was
deliberately stopped after 298.718 seconds to test the repository's
existing `decide +kernel` mode. It produced no accepted object.
The second attempt used `decide +kernel` and ended with SIGKILL
(return code -9) after 296.223 seconds, again without an output object
or Lean error text. The owned resource guard did not fire, and no
cgroup event counters were exposed to attribute the kill. Neither
attempt is a successful check or a proof counterexample.

Diagnostics then removed all concrete theorem checks. A definitions-only
prefix still reached a 90-second bound with asynchronous elaboration
disabled. An initial 2 GB diagnostic RSS ceiling had been below the
observed cached import baseline and caused an explicit refusal; the
calibrated run used 4.25 GB and did not hit that limit. The exact
header/substitution-only derivative passed in 4.270 seconds. Its
explicitly flushed markers confirm that this small boundary is cheap;
the earlier unflushed markers cannot identify the expensive declaration.
No speculative optimization or concrete acceptance is inferred.

The source inventory contains **2,974 named Lean proofs**, including
161 declarations in the six new modules. This is an inventory, not
compiled acceptance. The 126 governed claims and 411 source openings
are unchanged. All 57 proof-bank regression tests and the six focused
source/governance checks passed.

#### Inherited CI failure and narrow repair

The parent #564 overlap Lean run
[`43345576693`](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43345576693)
finished with a source proof failure at
`NamedStrictExclusion.lean:42`. Its residual goal was the reversed
membership conjunction for `K 1 ∩ K 0`; the supplied `and_comm` simp
argument was reported unused. Toolchain provisioning had succeeded.

The original archived-payload run
[`43345576753`](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43345576753)
subsequently failed on the identical source obligation. Its canonical
payload construction/import controls and independent original-graph
replay had passed. No additional source error appeared in the fetched
log, but neither complete build nor concrete geometric import was
accepted. This later observation is preserved separately from the
earlier parent-failure package.

This branch changes the three reversed cases to rewrite
`Set.inter_comm` before simplifying the same original zero-offset
root. No hypothesis, root identity, substitution or quantified claim
changes. The parent branch is not rewritten by this change. Its raw
failure log and exact-head source are preserved with the development
history; full repaired-chain acceptance is still required.

The exact repaired `intersection_eq_archivedRoot` theorem, extracted
with the real `ArchivedGraphRefinement` definitions and no stand-ins,
passed the pinned focused compiler in 2.621 seconds with no diagnostics.
An earlier launch used a working directory outside the input root and
was rejected before elaboration; that launch is preserved separately.
The successful probe verifies this theorem, not the full
`NamedStrictExclusion` module or its transitive axiom audit.

One bounded check also revisited the unchanged generic
`FiniteProductivity.lean` from #565. Its direct dependency was present,
but the run reached 90.363 seconds with an empty log and no object;
the owned runner terminated it. The sampled major faults and low user
CPU support import I/O pressure, without establishing either proof
acceptance or a source failure. Its source is unchanged in this branch.

### Negative controls

The generic controls distinguish missing seeds, missing outgoing
children, normalized-only carriers, allowed duplicate/superset entries,
and finite nonproductive Thue–Morse. The fast controls reject unequal
lengths, unbalanced endpoints, proper balanced prefixes and malformed
digits. A reducible-child packet passes its seed binding and all six
parent concatenation rows but fails the complete block check.

Additional checked row mutations omit, collapse, add or reorder factor
occurrences, swap a child's orientation, or use the wrong literal
substitution. Genuine singleton coincidences and complete ordered
positive packets are accepted. Native controls and Python mutations
provide separate executable checks.

### Non-claims / remaining gaps

Concrete generated checks, the extended named consumer chain, and the
complete isolated compilation and transitive-axiom audit still require
their actual terminal receipts. The parent strict-exclusion protocol
also requires its original seven-obligation concrete archive replays;
older six-obligation transcripts do not satisfy that gate.

This work does not establish finiteness from arbitrary unlisted
balanced blocks, universal G1, general C4, pure discrete spectrum or
PSC. Finite closure alone does not establish productivity. Claim
statuses are unchanged; independent human review remains separate
validation debt.

## Reproduction

From a checkout with the locked Pixi environment and Python test
dependency available:

```sh
bash kernel/check_forward_carrier.sh /tmp/psc-forward-carrier-replay
python3 tools/make_proof_bank.py --check
python3 -m pytest -o addopts= -q tests/test_proof_bank.py
./tools/check_lean.sh
```

The replay directory must be absent or empty. The native gate writes
raw stdout/stderr, source and binary hashes, refusal records and a
terminal JSON receipt. Its `lean_kernel_acceptance` field remains
false even when all native, oracle and source-reproduction steps pass.

## Preserved execution history

[`verification.json`](verification.json) summarizes each validation
scope, while [`source-hashes.json`](source-hashes.json) binds the candidate
code independently of the base commit. The raw build and generation
receipts, both native replays, successful and unsuccessful Lean runs,
diagnostics, source checks, scoped axiom audit, and parent CI failure
investigation are preserved in
[`development-history.tar.gz`](development-history.tar.gz).

[`history-index.json`](history-index.json) records every archive member's
size and SHA-256. Compression changes only the container; original member
bytes are retained. Compiler outputs inside the archive are evidence of
their recorded runs, not a replacement for rebuilding with the pinned
toolchain. Extraction for inspection is:

```sh
mkdir /tmp/psc-forward-history
tar -xzf development-history.tar.gz -C /tmp/psc-forward-history
```

The top-level `SHA256SUMS` pins every file in this packet with paths
relative to this directory. Failed and incomplete attempts remain in
the history and receive no acceptance credit.
