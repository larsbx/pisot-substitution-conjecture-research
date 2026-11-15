# Fresh source-isolated Lean acceptance

The replacement-environment run on November 15, 2026 completed successfully
in 205.878 seconds. This is a fresh producing run, separate from the
historical cached run before the earlier workspace loss.

`attempt-3.log` is the unedited combined process output and
`attempt-3-result.json` records the successful exit. `receipt.json` binds
the output, source snapshot and acceptance tooling by SHA-256.
`source-bindings.json` is extracted from the successful source snapshot;
its 128 entries were checked against both the isolated and working project
after dependency cloning, upstream-cache retrieval, local compilation and
audit execution. The reconstructed new Lean module and audit match their
recorded pre-loss SHA-256 digests exactly.

The gate cloned pinned upstream dependencies into an empty temporary
workspace. It requested 25 explicit upstream module roots, whose source
hash closure contained 2,165 cached upstream artifacts. It compiled all
20 local library modules in the new module's transitive dependency closure
from source and then ran the fresh standalone audit. No local project
`.olean` artifact was reused. Lean/Lake were checked against the pinned
4.34.0-rc2 release.

The audit inspected 167 declarations, including 114 theorems, in the
generic prefix helper and the new upper-cycle module. All eight independent
endpoint types and all 24 rejection controls passed. Every owned
declaration's transitive axiom closure was restricted to `propext`,
`Classical.choice` and `Quot.sound`. `audit.log` contains the exact audit
receipt rows extracted from the successful raw log; it is not the synthetic
fixture used by the parser tests.

The audit covers the eight literal cycle paths for every `n >= 7`, their
genuine ordered reversals, and the strict path/original-prefix result under
positive lengths, positive inflation and exact substitution scaling. It
does not supply upper-region recurrence classification, arbitrary-source
entry, excluded small-parameter cases, universal BH #139 or the full PSC.

## Replay

With the repository's pinned Lean/Lake toolchain available:

```sh
bash tools/check_class_a_plus_upper_cycles.sh
python3 tools/check_class_a_plus_upper_audit.py \
  evidence/class-a-plus-upper-cycles-2026-11-15/lean-fresh/audit.log
```

If the default temporary filesystem has less than 12 GiB free, set
`TMPDIR` to a workspace filesystem with adequate free space before running
the gate. The gate still creates an empty private directory there and
removes only that directory afterwards. The successful run used this
setting because the environment's default `/tmp` is a 4.9 GiB tmpfs.

## Preserved failures and parser control

Attempt 1 failed before the gate because `/usr/bin/time` was unavailable;
its exit code was 127. Attempt 2 reached the source snapshot and dependency
discovery but refused before downloads because the default temporary
filesystem failed the unchanged 12 GiB free-space guard. Their raw logs
remain beside the successful run. Attempt 3 used workspace temporary
storage and required no Lean source change.

The parser's command-line input preserves bytes before UTF-8 decoding,
so carriage returns cannot be normalized into accepted output. After the
fresh kernel pass, a further review found that Python's `splitlines()`
recognizes Unicode and control-character row boundaries. The reader now
requires LF-only complete lines, including a final LF; extra empty ASCII
LF lines remain intentionally permitted. Its focused suite passed 51
tests, including subprocess controls for carriage return, U+2028, vertical
tab and the missing final LF.

`audit-parser-at-build.py` preserves the exact reader used by the successful
fresh gate. `parser-revalidation.json` records the stricter current reader's
successful replay on the unchanged audit bytes and confirms that those
bytes occur contiguously in the producing raw log. `receipt.json` retains
the source bindings at fresh acceptance as well as the current tooling
bindings. No second Lean compile is claimed for this parser hardening.
Synthetic parser fixtures validate the receipt reader; the successful
producing Lean process and its source bindings supply the proof acceptance
evidence.

Lean linter warnings are retained verbatim in the raw log. They did not
prevent compilation or the endpoint and axiom audits; no warning was
silenced by changing the restored sources.
