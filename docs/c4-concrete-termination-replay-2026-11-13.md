# Replay concrete named termination

The original archived-payload replay now requires two additional conclusions:
coincidence termination for each ordered swap seed, and for every actual
`ChildNC` descendant of those seeds. It checks both literal substitutions,
`1/021/001` and `1/012/001`, separately.

## Work shown

### Assumptions and hypotheses

This integrates the existing contracts in
[`NamedForwardCarrier.lean`](../proof/PscVerif/PscVerif/NamedForwardCarrier.lean).
The original packet proves its own `Valid` proposition, and the named forward
carrier supplies checked finiteness for that same literal substitution. The
emitted endpoint retains only membership in the ordered seeds or in
`bpaStatesNC`; it asks the caller for neither packet validity nor finiteness.

The existing [finite-productivity review](c4-finite-productivity-literature-2026-11-12.md)
and [forward-carrier review](c4-forward-carrier-literature-2026-11-12.md) cover
these contracts. This is their concrete replay integration, with no new
invariant or mathematical route.

### Derivation / reduction

The canonical
[`c4_archived_lean_export.mojo`](../kernel/c4_archived_lean_export.mojo)
imports the named forward-carrier consumer and emits `seed_terminates` and
`reachable_terminates` by applying the packet's corresponding theorem to its
actual generated `valid` proof.

The [replay audit](../tools/replay_archived_payload_lean.py) requires the seven
previous semantic proofs and both new endpoints. Lean checks their exact
types against the literal fixture index, then audits every generated
declaration's transitive axioms. The receipt binds the forward-checker,
finite-productivity, generated data and named-consumer source hashes as well
as the original archive sources. The original payload format is unchanged.

### Evidence and replay

The focused Python suite passes 12 tests. Its synthetic compiler outcomes
test orchestration only; they do not constitute a Lean proof receipt.
The exporter also built with Mojo `1.1.0.dev2026090805`, and both native
exports exited successfully with one declaration of each new endpoint.
Their generated-source SHA-256 digests are:

| Fixture | Generated Lean source SHA-256 |
| --- | --- |
| `1/021/001` | `9aab0a1ab11bf4279330a5ccd6467b7a260ffcafa7936a6e27809ac3d86d3138` |
| `1/012/001` | `3a7102b3ec4c4eef381c45d9400c785f2c461cf8ebf2732f9b9d16718328f9dc` |

An initial bare compiler invocation failed to locate `std` because its
environment was not activated. Supplying that installed environment's
`MODULAR_HOME` corrected the invocation; it was not a source-code repair.

```sh
python3 -m unittest discover -s tests -p test_archived_payload_lean_replay.py -v
(cd kernel && pixi run --locked mojo build -I . c4_archived_lean_export.mojo -o /tmp/c4-archived-termination-export)
./tools/check_lean.sh --archived-packets /tmp/c4-archived-termination-export /tmp/c4-archived-termination-replay
```

Use a fresh output directory. Compiled acceptance requires the complete
isolated gate, both concrete generated carrier modules, both concrete archived
imports, exact endpoint type checks, and the axiom audit. A source change or a
successful exporter build alone supplies none of those proof results.

### Negative controls

The parser rejects the old seven-proof transcript and either omitted endpoint,
including transcripts with adjusted declaration totals. All earlier proof,
data-family, source, completion and nonstandard-axiom refusals remain required.

The harmless wrong-type fixture declares each endpoint with the correct input
binders but concludes `True`. Each endpoint use compiles in a separate audit
module and must fail with its own type mismatch. Missing identifiers, an
earlier obligation's failure, and a successful compiler exit receive no
negative-control credit.

### Non-claims / remaining gaps

The concrete nine-proof replay requires its own successful terminal receipt.
Earlier seven-proof receipts remain historical evidence for their original
scope and are not relabeled. These endpoints cover seed-generated states for
the two named substitutions; they establish no arbitrary unlisted-block
claim, universal G1, general C4, pure discrete spectrum, or PSC. Independent
human review remains separate validation debt.
