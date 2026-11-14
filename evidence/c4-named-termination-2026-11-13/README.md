# Named consumer repair and acceptance evidence

This packet records the next concrete blocker in the two named forward-carrier
termination consumers and the tested selector repair. The complete repaired
production module, isolated compiled audit and original-archive replay still
require successful terminal evidence.

The mathematical scope and replay commands are in
[the acceptance note](../../docs/c4-named-termination-acceptance-2026-11-13.md).
All 126 governed claim statuses remain unchanged.

## Exact source identities

The three hosted runs below belong to
`6021f042056d3cb0f9717d2488144339721c2071`, attempt 1. PR #568 was subsequently
merged into the #560 integration branch as
`1ce54efeff586ecda2ec1bd11a2f9c6617b2fb87`. Both commits have tree
`3355716258114a4f5353b10233fa1fa79bb34bbd`; each receipt retains its actual
producing revision. A shared tree is not a hosted verdict for another commit.

The repaired `proof/PscVerif/PscVerif/NamedForwardCarrier.lean` has SHA-256
`c825c41da424572c4014ecf2e1f6a80457f9265409c4fde6daf7f3cccd5137e7`.
Its only proof change replaces the two broad `change` conversions with explicit
named-wrapper and finite-vector selector simplification. The theorem statement,
generic checker, both carrier modules, both literal-data modules, original JSON
packets and recursion settings remain unchanged.

## Retained outcomes

| Evidence | Actual outcome and scope |
| --- | --- |
| [Hosted native replay](hosted-native-6021f042/README.md), [run 43435276378](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43435276378) | **Passed.** The independently inspected artifact binds all 763 native input files and 55 manifest files; 258 tests passed. Both original JSON packets and all four generated Lean sources reproduce byte for byte. This gate makes no Lean acceptance claim. |
| [Hosted archived-payload gate](hosted-archive-failed-6021f042/README.md), [run 43435276766](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43435276766) | **Failed.** Lake reports both complete carrier modules built, then `NamedForwardCarrier.lean:77:4` reaches maximum recursion depth. The full compiled audit and subsequent concrete archive imports were not reached. |
| [Hosted full Lean gate](hosted-fulllean-failed-6021f042/README.md), [run 43435276869](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43435276869) | **Failed.** Both carrier modules are reported built before the same named-consumer recursion error. Neither formal failure is relabeled as a timeout or a successful project build. |
| [Focused consumer probes](consumer-selector-probe/README.md) | The original conversion reproduces the recursion error. Both a local recursion-limit variant and the selected explicit-selector variant compile and pass their focused axiom audits. The selected variant uses the default recursion limit. |
| [Local fixture-0 run](local-fixture0-sigkill-1ce54efe/README.md) | **SIGKILL, no object.** The process ended after 1,095.917 seconds, with 166 of 192 row checks complete and no recorded guard trigger. The signal's cause is unconfirmed; the original run and post-run input checks are retained. |
| [Prepared nine-endpoint inspector](prepared-inspector/ADAPTATION.md) | **21 protocol tests passed.** Source/receipt/refusal tests use explicitly synthetic audit rows and object placeholders. No complete hosted artifact or mathematical result is accepted by those tests. |
| [Source integration and governance](source-checks/README.md) | All seven actual commands exit zero, including 57 proof-bank tests, proof-bank consistency, vendored pins, generated ledgers and claim governance. All 1,960 bound source files remain unchanged during execution and log review. |

The hosted formal artifacts retain raw provider metadata and build logs, but
not compiled carrier objects or a complete formal-source hash inventory. Their
individual module-build messages are reported at that scope.

The consumer probes import the actual successful fixture-1 object and preserve
the literal substitution table. Their unused fixture-0 carrier slot is empty,
avoiding an import of the absent local Data0 object. The two successful variants
audit the transported theorem and imported forward-check theorem with only
`propext`, `Classical.choice` and `Quot.sound`. They record unchanged local
source/object inputs and direct cached dependency boundaries. Transitive cached
external objects remain an explicit trust input. These are focused probes,
not a build of the two-fixture production module or the isolated project.

The local fixture-0 outcome is kept separately from the hosted successful
module-build messages. A prepared row-splitting fallback was left unapplied:
the observed hosted blocker occurs later, in the named consumer conversion.

## Inspector preparation is source-specific

`prepared-inspector/source-metadata-6021f042.json` binds the old, exact
`6021f042` source. It is retained preparation evidence, not metadata for the
repaired publication. A future successful repaired run needs fresh metadata
derived from its own clean checkout, full revision and tree; the old metadata
must not be relabeled or supplied as acceptance for that new source.

The successor requires all nine semantic proofs, both termination endpoints'
own intended wrong-type controls, 35 unique metadata source paths, the exact
25-path replay manifest and 41 explicit declarations in five modules. The
candidate-derived proof bank still controls the complete compiled audit.
The original run/job/attempt, clean-checkout, native mutations, original graph,
oracle and final replay-summary requirements remain in force. GitHub artifact
identity and downloaded ZIP digest require their separately retained provider
records.

To replay the preparation tests, provide a clean checkout of the metadata's
exact commit through `PSC_INSPECTOR_CANDIDATE_ROOT`, then run:

```sh
python3 prepared-inspector/test_prepared_inspector.py
```

## Source-validation receipt correction

The first source-check wrapper expected a numeric pytest summary. The
repository's quiet default combined with the command's quiet option suppressed
that summary, so the wrapper marked its aggregate result failed despite all
seven commands exiting zero. A separate strict review verified exactly 57 pass
symbols followed by `[100%]`, the successful pytest exit and every original
record hash. The original wrapper receipt remains unchanged alongside the
review; no mathematical test failure is rewritten. Neither the source checks
nor their review invoked Lean or the native gate.

## Integrity and replay

The [scoped archive review](archive-review/README.md) verifies the five hosted
and diagnostic archives above, their nested manifests and ZIP copies, the
prepared inspector and all 4,181 historical tracked evidence files. Its scope
excludes the subsequently packaged source-check archive and parent inventory;
those have their own integrity checks. The retained unified diff keeps its
required blank context markers byte for byte. A path-specific Git attribute
treats those trailing markers as evidence data.

The top-level `SHA256SUMS` covers every other file in this packet using relative
paths. Check it from this directory:

```sh
sha256sum --check SHA256SUMS
```

Each compressed evidence group retains original record bytes and its own
internal manifest. Extract each archive into a separate empty directory and
check that directory's `SHA256SUMS`. The prepared inspector's manifest can be
checked from its own directory. Raw UTC timestamps are preserved in receipts;
elapsed diagnostic timings are not controlled performance comparisons.

The native gate's 763 recorded inputs were rehashed after the selector repair
and are unchanged. The named consumer is outside that native input manifest;
the native pass does not validate its proof. Complete acceptance still requires
the repaired production consumer, full isolated compiled axiom audit and both
original archives' nine-endpoint replay at their actual producing revision.

The intended result concerns the two literal substitutions' ordered swap seeds
and actual `ChildNC` descendants: finite reachability and an available
coincidence-reaching path from every reached state. It does not assert that
every possible path terminates, a uniform path-length bound, termination for
arbitrary unlisted starting blocks, or general C4/PDS/PSC.
