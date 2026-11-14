# Acceptance of the two named termination consumers

## Production follow-up — November 14

The explicit transport at `84f7b2b70adbd632c0e0cc06cbd246aee2020f70`
subsequently compiled both actual generated carriers, but its
[full Lean run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43568767809)
failed at the fixture-1 local selector equality (`NamedForwardCarrier.lean:76:83`).
The broad checker conversion was avoided; reducing the full selected state-list
wrapper still exceeded the default recursion allowance. That run remains a
failure, without a complete audit or termination acceptance.

The successor proves the local state equalities with the pinned generic
`Matrix.cons_val_zero` and `Matrix.cons_val_one` lemmas instead of `rfl` on
the concrete tables. It also raises `maxRecDepth` to `200000` only for
`check_checkedStates`, matching the existing generated checker allowance. This is an elaboration resource setting, not a new premise,
axiom, checker bypass or altered theorem statement. The complete successor
acceptance remains pending at publication. Earlier claims below about default
recursion settings describe the preceding attempts, not this successor.

The selector-only repair recorded below was published in PR #569 at
`52614a3b5a7199b1d17cb7a0b435da71e1e80569`. Its
[full Lean run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43492499736)
and [original-archive run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43492499714)
both compiled the two actual generated carriers, then failed at
`NamedForwardCarrier.lean:77:10` with maximum recursion depth. The preceding
focused probe's empty unused fixture-0 slot did not establish production
acceptance. The inherited failure at the #560 source remains a failure.

The follow-up proof transports each existing `fixtureNForwardCheck` through
the literal substitution equality and a local equality selecting its actual
carrier. `congrArg₂` and equality transitivity make that transport explicit.
It preserves both production carriers, theorem statements, generated checker
proofs, the declaration inventory and default consumer recursion settings.
No new mathematical contract or axiom is introduced.

Actual two-fixture production compilation, the complete isolated compiled
audit and both original archives' nine-endpoint replay remain required.
The [current next-steps note](psc-next-steps-2026-11-14.md) distinguishes the
completed mathematical components from these outstanding acceptance gates.
The remainder of this note preserves the earlier source and probe history.

This continuation verifies the existing concrete forward-carrier and
archived-payload composition for `1/021/001` and `1/012/001`. It introduces
no new mathematical predicate. The forward-carrier and finite-productivity
literature decisions remain the design gates for this contract.

## Source identity and scope

PR #568 was merged into the #560 integration branch as
`1ce54efeff586ecda2ec1bd11a2f9c6617b2fb87`. That merge and the producing
head `6021f042056d3cb0f9717d2488144339721c2071` have the identical tree
`3355716258114a4f5353b10233fa1fa79bb34bbd`. Evidence retains the actual
commit that produced it; identical trees do not manufacture a CI verdict
for a different commit.

The intended closed endpoints, separately for each literal substitution,
are termination with coincidence for every ordered unequal-letter swap
seed and for every member of its actual `bpaStatesNC` set. The existing
predicate means finite actual `ChildNC` reachability and existence of a
coincidence-reaching path from every reached state. It supplies neither
termination of every possible path nor a uniform path-length bound.

The formal composition preserves four distinct obligations:

1. The original ordered carrier contains all six ordered swap seeds.
2. Its checker verifies every block and both complete ordered child-track
   concatenations, giving finite actual forward reachability.
3. The valid original inverse-overlap archive supplies strict-system
   exclusion for the same literal substitution.
4. `FiniteProductivity.terminates_of_finite_reachable` combines exclusion
   and finiteness for every reached block. The actual generated archive
   applies its own validity proof, leaving only seed or descendant
   membership as the caller's premise.

The inverse archive is not used to construct forward finiteness. Literal
definitional identities bind the two substitutions; incidence-matrix
equality and normalization are not substitutes for that binding.

## Hosted native replay

The forward-carrier workflow at `6021f042` completed successfully. Its
downloaded artifact was checked against the provider's SHA-256 digest,
then independently inspected against the exact clean source checkout.

The inspection verifies all 55 artifact-manifest files and all 763 source
hashes, the locked native builds and binary identities, both unchanged
original JSON packets, and all four generated Lean sources. The full gate
took 45.918731 seconds; its 258 tests passed in 32.56 seconds. A fresh
optimized Python oracle replay agrees with the hosted oracle receipts
after accounting for the local input-path fields.

This native result certifies the replay and literal-data contract at its
recorded scope. Complete Lean compilation and the isolated compiled
axiom audit retain their own terminal acceptance requirements.

The consumer repair below changes none of the native gate's 763 input
files; all their recorded hashes were checked again. The named consumer
proof is outside that native manifest, so native success is not claimed
as validation of the repaired Lean proof.

## Observed formal failures and consumer repair

Both formal workflows at the same exact source subsequently failed at
`NamedForwardCarrier.lean:77:4`, with `maximum recursion depth has been
reached`. The failing step was the fixture-1 `change` in
`check_checkedStates`, after `fin_cases fixture`.

| Hosted run at `6021f042`, attempt 1 | Data0 build reported | Data1 build reported | Final outcome |
| --- | ---: | ---: | --- |
| Archived payload, `43435276766` | 1,100 seconds | 684 seconds | Consumer recursion error; build exit 1 |
| Full Lean, `43435276869` | 986 seconds | 558 seconds | Same consumer recursion error; build exit 1 |

These are the module-build results reported by Lake in the retained
original logs. Neither artifact retains the compiled carrier objects,
and neither run reached a complete compiled axiom audit. The archived
run also did not reach its later concrete original-packet imports.
Neither failure is attributed to a timeout.

The production repair replaces only the two broad `change` conversions
with explicit simplification of `check`, `checkedStates`, `substitution`
and the appropriate finite-vector selector lemmas. Each branch then
applies its existing `fixtureNForwardCheck` theorem. The original
`ForwardCarrier.check`, generated states and packet predicates are not
unfolded by that simplification. The theorem statement, carrier data,
original packets, generic checker and recursion settings are unchanged.

A focused probe against the actual successful Data1 object reproduced
the error and compared two repairs:

| Probe | Result | Elapsed seconds |
| --- | --- | ---: |
| Original `change`, default recursion setting | Intended recursion error; exit 1; no object | 34.361 |
| Theorem-local `maxRecDepth 200000` | Compiled and passed its axiom audit | 14.235 |
| Explicit selectors, default recursion setting | Compiled and passed its axiom audit | 12.623 |

The selector repair was selected. Both successful probes audit the
transported theorem and imported forward-check theorem, with only
`propext`, `Classical.choice` and `Quot.sound`. The failed baseline also
refuses Lean's error-recovery `sorryAx`. These sequential diagnostic
timings have changing cache state and are not a controlled performance
comparison.

The probe preserves the literal substitution table and actual fixture-1
carrier, using an empty unused fixture-0 slot to avoid importing the
absent local Data0 object. It is a focused cached-dependency reproducer,
not compilation of the production two-fixture module. The existing
`fin_cases` production branches were independently reviewed against the
pinned `Matrix.cons_val_zero` and `Matrix.cons_val_one` equations; actual
production and isolated-chain replay remain required.

A separate local Data0 run at merge `1ce54efe` ended with SIGKILL after
1,095.917 seconds, without an object or recorded guard trigger. It had
completed 166 of 192 row checks; its sampled peak was 3,338,407,936 bytes.
All recorded inputs remained unchanged, and the cause of the signal is
unconfirmed. That local outcome is not replaced by the hosted module
build messages. A prepared row-splitting fallback was left unapplied
because the hosted runs had already compiled both original carriers and
identified the later consumer conversion as their actual blocker.

Original provider records, artifacts, logs, diagnostic sources, objects
and scope boundaries are retained in the
[acceptance evidence packet](../evidence/c4-named-termination-2026-11-13/README.md).

## Complete hosted evidence inspection

The prepared nine-proof inspector extends the previously retained
seven-proof strict-exclusion inspector. It requires both
`seed_terminates` and `reachable_terminates` in addition to `valid`,
`accepted`, `typed_accepted`, `domain_iff`, `roots_null`, `ancestors_null`
and `no_strict_system`.

The additional checks require each termination endpoint's own refusal
flag, exact isolated wrong-type source and intended diagnostic. An
earlier failed obligation cannot earn credit for a later unchecked one.
The inspector also binds 35 unique metadata source paths, the producer's
exact 25-path replay manifest, and 41 explicit declarations across five
modules: 37 theorems and four definitions. The full compiled audit still
requires every named proof in the candidate-derived proof bank; no fixed
compiled declaration count replaces that check.

The predecessor's exact run, job, attempt, head, clean-checkout, original
graph, native mutation, oracle transcript, final replay-summary and
artifact-stability checks are retained. The provider's artifact identity
and original ZIP digest are separate required provenance evidence.
Artifact source code is never executed by the inspector.

All 21 focused inspector tests pass, including omitted paths,
declarations and endpoints, old seven-proof transcripts, incorrect
endpoint controls, and unsuccessful or nonterminal hosted runs. These
tests exercise the evidence protocol with explicitly synthetic inputs;
they do not supply a compiled theorem or a successful hosted verdict.

## Replay

From the exact recorded source checkout, use the canonical native gate:

```sh
bash kernel/check_forward_carrier.sh /tmp/psc-forward-fresh
```

For complete project acceptance, provision the repository's locked Mojo
and pinned Lean toolchains, build the canonical archived exporter, and
run the unchanged isolated gate:

```sh
(cd kernel && pixi run --locked mojo build -I . c4_archived_lean_export.mojo -o /tmp/psc-archived-export)
./tools/check_lean.sh --archived-packets /tmp/psc-archived-export /tmp/psc-archived-fresh
```

The full gate starts with an isolated source/configuration workspace,
builds the project, audits the compiled library, and then checks both
actual original archives at all nine exact semantic types. A focused
replay against cached dependencies has a different evidentiary scope.

## Remaining acceptance boundary

The earlier complete fixture-1 checker and focused literal/axiom audit
remain recorded at their original cached-dependency scope. The original
formal runs at `6021f042` remain failures. The repaired production
consumer, complete isolated compiled audit and both original archives'
nine-endpoint replay require fresh successful terminal records. A
passing focused reproducer and source inventory do not discharge those
remaining gates.

All 126 governed claim statuses remain unchanged. This work covers the
two named fixtures and their actual seed descendants. Arbitrary unlisted
starting blocks, universal G1, general C4, PDS and PSC are outside these
acceptance claims. Independent human review remains separate validation
debt.
