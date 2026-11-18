# Forward-carrier encoding and termination replay evidence

This packet records a representation repair and the completed native checks.
**It does not currently supply complete Lean carrier or termination acceptance.**
The original two carrier packets and all older evidence remain unchanged.

## Source and scope

The implementation starts from PR #560 at
`beb6de118093e7a2e29f89e1607757e2baf3f5e3`, tree
`9ec2e0ce2f8ed1637cdcb81a04a696b25d7fa9f4`. The local native replay ran with
the proposed worktree changes present. Its recorded `revision` is that base,
not a claim that the base contained this repair. Its `SOURCES.sha256` binds
the actual tested source bytes; the before/after worktree records retain this
distinction. Publication must preserve and compare those source hashes.

The canonical Mojo exporter shares typed word chunks of at most 32 letters.
It preserves the literal substitutions, ordered words, state order, complete
child rows, seed indices and carrier predicates. The archived exporter also
emits the two existing seed/descendant termination consumers, using the
original packet's actual validity proof. Its replay now demands nine exact
semantic proof types rather than the earlier seven.

Design and boundaries:

- [Encoding repair](../../docs/c4-forward-carrier-kernel-encoding-2026-11-13.md).
- [Concrete termination replay](../../docs/c4-concrete-termination-replay-2026-11-13.md).

## Completed native replay

`native-replay.tar.gz` is a deterministic archive of the complete output of
the unchanged `kernel/check_forward_carrier.sh` orchestration. It includes
the two emitted packets, generated Lean sources, compiler metadata, binary
digests, command logs, exact source hashes and terminal receipt.

| Check | Recorded outcome |
| --- | --- |
| Native finite-carrier controls | Passed |
| Both original JSON packets | Reproduced byte for byte |
| Both proposed Lean modules | Reproduced byte for byte |
| Independent literal carrier oracle | Passed |
| Oracle and encoding suite | 182 passed |
| Length and state budget controls | Both refused with empty certificate output |
| Source stability during replay | All recorded source hashes unchanged |
| Complete native replay | Exit 0, 76.918355 seconds |

The gate used supplied binaries built earlier in this session. It truthfully
records `binaries_built_by_this_gate: false`; the separate source-bound build
receipts identify the compiler, commands, input hashes and resulting binary
hashes. A subsequent source-bound rebuild reproduced the exporter digest
used by the completed gate exactly. The compiler's installed package metadata
matches the repository's locked Mojo `1.1.0.dev2026090805` package. The package
archive itself was not rehashed by this gate.

| Artifact | SHA-256 |
| --- | --- |
| Forward exporter binary | `5eba90f82fa782a073866a53590fcac0f155f78d2cf1b2d5ca184ec28bf87e99` |
| Native test binary | `619c4db5563cf9d496bb09f98379077b31e48b00b511fb65c4c961712e2f914f` |
| Extended archived exporter binary | `a0597e04bca1d73ed7af456a6bba50d31ba9f6b1d7f7b2a8868c414386d6af7f` |
| Fixture 0 JSON | `1f0e32301807023239a7d8eabdbbabf71d60c9956a96ccbc8f25b7bc8358d04f` |
| Fixture 1 JSON | `65a78cba7b94e5b48e06e4f6617eb96e4f43f623e61b68ab97cb07dbd472fe0e` |

The final endpoint protocol suite separately passed 12 tests. Those tests
include synthetic compiler responses to exercise orchestration; they are not
Lean proof receipts. The extended archived exporter built successfully and
emitted both actual source fixtures. Compiling those sources and auditing
their nine semantic conclusions remains required.

## Diagnostic probes

`decode-bench.tar.gz` and `scan-bench.tar.gz` retain their exact Lean sources,
logs and terminal JSON receipts. They use Lean `4.34.0-rc2`, ordinary
`decide +kernel`, and no new axiom. They are small development probes, not
the complete original carriers or an isolated proof-bank gate.

| Probe | Outcome | Elapsed seconds |
| --- | --- | ---: |
| Unchanged string decoder, length of 100 letters | Passed | 8.408 |
| Unchanged string decoder, length of 1,000 letters | 90-second timeout; no acceptance | 91.309 |
| Typed literal list, length of 1,000 letters | Passed | 4.485 |
| Typed literal list, length of 10,000 letters | Passed | 14.287 |
| Unchanged streaming block check, 102-letter original pair in typed chunks | Passed | 5.387 |
| Unchanged streaming block check, 1,318-letter original pair in typed chunks | Passed | 7.531 |
| Unchanged streaming block check, 10,946-letter original pair in typed chunks | Passed | 52.922 |

These timings include different startup/cache conditions and concurrent work.
They motivate the representation repair; they are not a controlled overall
speedup measurement. The separate full carrier-1 run spent 161 seconds in
imports before checking its declarations. Silent, bounded diagnostic runs
cannot therefore locate a theorem failure or identify `simpa` as their cause.
The retained frontend diagnostic history distinguishes instrumentation errors,
owned time limits and deliberate stops from mathematical rejection.

## Reproduction

Verify this packet's checksum manifest, then extract each archive into a new
directory. Archives contain relative paths only. The native archive's own
`SHA256SUMS` verifies its original raw outputs after extraction.

```sh
bash kernel/check_forward_carrier.sh /tmp/psc-forward-replay-fresh
python3 -m unittest discover -s tests -p test_archived_payload_lean_replay.py -v
./tools/check_lean.sh
(cd kernel && pixi run --locked mojo build -I . c4_archived_lean_export.mojo -o /tmp/psc-archived-export)
./tools/check_lean.sh --archived-packets /tmp/psc-archived-export /tmp/psc-archived-replay-fresh
```

The two full isolated gates still require their own successful terminal
receipts. Native replay, source inventory and cached-dependency development
checks supply only their recorded scopes. No result here promotes universal
G1, general C4, PDS or PSC; all 126 governed claim statuses remain unchanged.
