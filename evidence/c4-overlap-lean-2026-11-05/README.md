# Overlap Lean verification evidence

Baseline: main `ea870c846f6575e51aaa78ef4659e533da636b0a` (merged PR #496).

The new module is `proof/PscVerif/PscVerif/OverlapContraction.lean`. It is part
of the root library, generated Proof Bank inventory, and complete local
declaration/axiom audit. See the interface note for exact theorem hypotheses.

The generic layer is not a Lean replay of the 18 concrete native packets.
Those data and their geometric refinement remain unbound.

The module compiles with the pinned compiler. The full isolated
`./tools/check_lean.sh` run exited zero. Its fresh audit reached all **88 named
proofs**, including the **20 new overlap proofs**, and accepted **355 local
declarations / 201 theorem declarations** (including generated helpers).
Every axiom dependency belongs to `{propext, Classical.choice, Quot.sound}`.
The completion receipt is `PSC_AUDIT_COMPLETE 355 201` (tab-separated in the
raw log).

`isolated-audit.log` retains the complete checker output;
`module-build.log` retains the focused module build;
`local-validation.json` records the source fingerprint, compiler/dependency
pins, scope and local runtime adaptation. Proof Bank, ledger, math catalogue,
claim-governance and vendored-source checks also passed. Hosted exact-head
acceptance remains a separate result; no hosted pass is claimed here.

## Local host runtime adaptation

This Work host exposes the current executable at `/proc/self/exe` but not at
the numeric PID path used by Lean's application-path lookup inside its PID
namespace. The official compiler therefore needs a local `readlink` adapter
to locate its installation. `host-proc-path.c` is the complete adapter source;
its SHA-256 is
`97246ffaa7eaa0ba843adfd189227c324092ad4de9651052fed8959fe440250b`.
It rewrites only the current process's `/proc/<getpid()>/exe` lookup to
`/proc/self/exe`, and otherwise calls the original function. It changes no
proof, compiler source, dependency source or axiom policy. This is an additional
local runtime trust input, not part of the normal hosted CI environment.

The local invocation compiles this adapter as a shared library and runs the
unchanged checker with that library in `LD_PRELOAD` and Elan on PATH. The
isolated checker still rejects caller compiled caches, verifies dependency
sources, compiles the local project afresh, and audits all local declarations.
The checked-in focused CI workflow uses the standard commands without the
adapter. Neither environment's result is substituted for the other.
