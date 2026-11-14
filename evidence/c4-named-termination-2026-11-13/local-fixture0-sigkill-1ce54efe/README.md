# Local fixture-0 replay terminated by SIGKILL

This packet preserves the unsuccessful focused local replay at source
`1ce54efeff586ecda2ec1bd11a2f9c6617b2fb87`, tree
`3355716258114a4f5353b10233fa1fa79bb34bbd`. The exact generated checker is
unchanged from `6021f042` and has SHA-256
`5026901eb6a7f9c2500f38f7835aa96a235c6eb0e5722da1084a45fb83b2b905`.

| Recorded item | Outcome |
| --- | --- |
| Actual module | `PscVerif.NamedForwardCarrierData0` |
| Compiler return code | `-9`, SIGKILL |
| Elapsed seconds | 1,095.916761 |
| Maximum sampled RSS | 3,338,407,936 bytes |
| Recorded stop reason | None; neither monitor guard fired |
| Configured guards | 5,400 seconds; 4,000,000,000 resident bytes |
| Sampling interval | 5 seconds |
| Last completed row | Zero-based row 165, including its auxiliary proof |
| Total completed row checks | 166 of 192 |
| Output object | Absent |
| Source bytes | Unchanged |
| Terminal UTC | 2026-11-13 15:28:42 |

The cause of the signal is unconfirmed. A sampled peak is not a measured
continuous maximum. The next source obligation is row 166, with 13,065
letters on each track and 122 child occurrences; that location does not
establish why the process was killed. No Lean proof diagnostic was emitted.

The post-run check found all 13 recorded local source/object inputs,
19 cached external boundary objects, compiler and dependency manifest
unchanged. The successful fixture-1 object also remained unchanged.
This was a focused run with cached dependencies, with no isolated
acceptance claim. The staged fixture-0 audit was not launched because no
successful object handoff existed.

`local-failure-evidence.tar.gz` contains the exact checker source, original
start and terminal receipts, complete log, sampled resources, copied
watchdog, preflight and post-run input verification. The archive's SHA-256
is `b7ef74efffc703a46196c30a4281024d109d0a2bc748db475406c8e9eba3aa8d`.

Two separate hosted runs at `6021f042` reported successful compilation of
this same checker source, then failed later in the named consumer. Those
records retain their own source identity and scope in the sibling hosted
failure packets. They do not change this local run's unsuccessful outcome.
No generated row, checking proposition or compiler guard was changed.
