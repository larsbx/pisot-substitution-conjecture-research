# Focused compilation and literal audit for fixture 1

**The complete generated forward carrier for `1/012/001` compiled, and
its focused literal-type and transitive-axiom audit passed.** This is
source-bound evidence with recorded cached dependencies. It is not the
full isolated project gate and does not establish termination.

## Exact source and terminal compilation

The checked source is from commit
`d21b4cb8e72e585317bcf5b26b2e4085cb2efad6`, tree
`377945fb52acf441129b0b400838a77c230d8497`. The actual source and imported
payload bytes stayed unchanged across compilation and publication.

`concrete-carrier-compilation.tar.gz` retains the generated source,
compiled object, complete log, sampled resource history, original start
and terminal receipts, and the source/object handoff to the later audit.

| Field | Observed result |
| --- | --- |
| Actual module | `PscVerif.NamedForwardCarrierData1` |
| Compiler | Lean `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Return code | 0 |
| Elapsed | 1,521.163314 seconds, approximately 25 minutes 21 seconds |
| Maximum sampled RSS | 3,721,379,840 bytes |
| Guards | Neither the 3,600-second nor 4 GB guard fired |
| Source stability | Unchanged |
| Terminal UTC | 2026-11-13 13:20:27 |

The trace records all 520 singleton row checks and their kernel auxiliary
proofs, followed by successful aggregation, `Valid`, `ForwardCheck`,
`Finite`, and object serialization. The profiler attributes approximately
1,450 seconds to kernel type checking; kernel type checking of the final
range aggregation took 165 milliseconds. These are observations of this run, not a controlled
comparison with previous attempts or a prediction for fixture 0.

| Compilation identity | SHA-256 |
| --- | --- |
| Actual checker source | `a49d8fa4146b534cff95259beab31a06903088184676704c239eb11b98cc4c0a` |
| Produced checker object | `d7bd11bd5e09f37385c782cda982791c0fd3a5b13224d6b319280109b2099a41` |
| Terminal receipt | `f58daaf3eb3f14ae6c5f107f1d426b7db4de8d4489f671f2d5171d645279c241` |

## Closed literal conclusions and axiom audit

`literal-type-axiom-audit.tar.gz` contains the independent focused audit,
its reproducible runner, object, complete log, input hashes and terminal
receipt. Its sole source import is the successful fixture-1 checker.
It demands three closed conclusions with the literal substitution
`![[1], [0, 1, 2], [0, 0, 1]] : Fin 3 → List (Fin 3)` in their types:

1. The actual generated packet satisfies `Packet.Valid`.
2. The original `Psc.ForwardCarrier.check` on the actual generated state
   list equals `true`.
3. The actual `Psc.Descendants.bpaStatesNC` set is finite, through the
   existing checked-packet refinement theorem.

No validity or finiteness premise is supplied by a caller. The audit
also verifies that the named strict-exclusion module is absent; no
termination conclusion is tested or claimed here.

The audit ran only after the successful terminal compilation and exact
object handoff. It exited zero in **23.111822 seconds**, produced its
object, and retained all 37 recorded inputs unchanged. Those inputs cover
the complete 13-module local source/object closure, compiler, selected
core inputs and dependency manifest. External cached objects were not
all independently hashed, and the receipt explicitly records
`full_isolated_acceptance: false`.

All six required transitive-axiom records were present:

| Literal audit conclusion and corresponding generated theorem | Axioms |
| --- | --- |
| Packet validity; `fixture1Valid` | `propext`, `Quot.sound` |
| Forward-check equality; `fixture1ForwardCheck` | `propext`, `Classical.choice`, `Quot.sound` |
| Finite descendants; `fixture1Finite` | `propext`, `Classical.choice`, `Quot.sound` |

Both the compiled audit and its output parser reject nonstandard axioms.

| Audit identity | SHA-256 |
| --- | --- |
| Exact literal audit source | `9819ee56fc0b80b9a9695c5635df4a7c585ac3f5062d2d75e12464e665e892a5` |
| Audit object | `4695c80863d4ec1b5991b3bffa032dac0a87e57f3fde0de1b10ab4e8599572d7` |
| Audit receipt | `adb247ef1ca502e33b7471887dbc73580f02258d0348264070d65fe062ef6245` |
| Input manifest | `7db35395b22b7506e1ec400ea22fed912d4e36d5130143ffbe97920f3a0d6a96` |
| Complete audit log | `3ba72268d380b751db4ca1b6de74461fdb588ef0da946d92e8e3acbee2295721` |

## Remaining project gates

Fixture 0's actual data module compiled earlier, but its complete carrier
checker has not been run locally in this continuation. Both-fixture named
termination consumers, the original archive imports with all nine exact
endpoints, and the full isolated build and compiled audit remain pending.
All 126 governed statuses remain unchanged.

The full Lean workflow's allowance is increased from 30 to 180 minutes
because this single focused serial carrier already used over 25 minutes,
while that workflow builds both carriers and the full proof bank. Every
build and audit command is retained. This is a time-budget decision based
on observed work; it does not attribute earlier runner shutdowns to a
timeout or predict hosted runtime. The archived-payload workflow retains
its existing 240-minute allowance.
