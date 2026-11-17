# Literal seam replay — local acceptance, 17 November 2026

Base: `main@2d831230c9b5a2f7b21165df6756532b3f598e37` (merge of #601).
This packet records the audit continuation's finite literal replay. Its
[mathematical and implementation contract](../../docs/c4-literal-seam-replay-2026-11-17.md)
and [current audit crosswalk](../../docs/psc-audit-continuation-2026-11-17.md)
preserve all universal non-claims.

## Results

| Check | Local result |
| --- | --- |
| New literal seam replay | Exit 0; 48 specimen/power comparisons, 14 mutation or input refusals, final contract receipt reached. |
| Existing seam-spectrum regression | Exit 0; original cycle tables, positive minus-one correction, subdivision and algebraic-multiplicity controls retained. |
| Existing periodic-overlap regression | Exit 0; 20 literal twice-power comparisons and occurrence/negative controls retained. |
| `bash tools/verify_all.sh provenance` | Exit 0; source hashes, vendoring, generated inventories, Markdown integrity and claim governance passed. |
| Four Markdown-link checks | Executed directly as Python functions; passed after staging the new files. |

The commands and exit codes are in [manifest.json](manifest.json); the
three Mojo logs contain their reached contract receipts. The manifest
binds the canonical implementation/test files and runtime lock by SHA-256.
It does not claim a full Mojo-suite, fresh Lean, Quint or hosted CI run.

## Runtime and replay

The cached executable reports `Mojo 1.1.0.dev2026090805 (34562fa1)`.
The compiler and standard-library package archives match the Linux entries
of `kernel/pixi.lock`. The compiler package digest is
`0d71889abb0887e2fa8a556c1081af4026034cdf98d27ad05b57cb096d7ad4f6`;
the Mojo package digest is
`c73cf02c19b7de5774f8f6275b0b9eb4b656558f7d10f27d3508374fa0559d28`.
Installed `bin/mojo` and `lib/mojo/std.mojoc` were also checked against the
compiler archive's path hashes. The local invocation supplied the cached
runtime's `MODULAR_HOME`; no compiler source or lock changes were made.
The harmless Crashpad warning remains in the logs rather than being
silently removed.

The normal repository replay is:

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_literal_seam_replay.mojo
pixi run --locked mojo run -I . -I tests tests/test_one_track_seam_spectrum.mojo
pixi run --locked mojo run -I . -I tests tests/test_periodic_overlap_returns.mojo
cd ..
bash tools/verify_all.sh provenance
```

An attempted `python3 -m pytest` invocation could not start because this
runtime has no `pytest` module. No pytest pass is claimed. The four
parameter-free Markdown-link checks were instead executed directly; the
generated proof-bank consistency check is included in the successful
provenance profile. The broader Python test suite was not run.

## Acceptance boundary

The new constructor inherits the original-image length-six gate, accepts
only unit PIP3 sources, caps every expanded image at 100,000 letters, and
caps each returned population. Arithmetic-scope refusal, partial word
expansion and record-cap exhaustion return no inventory. Replay helpers
check occurrences relative to the constructor's expanded words; they do
not authenticate arbitrary external inventories.

All four declared controls are productive and have no aligned
nonproductive sink. The comparison authenticates their endpoint and seam
identities and retains the conditional spectrum's evidence boundary. It
does not prove uniform C4, A1′, BH, rank one or PSC. No governed claim or
historical receipt is changed.
