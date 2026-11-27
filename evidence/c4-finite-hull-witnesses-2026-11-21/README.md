# Source-bound acceptance of the finite automaton hull interpretation

Baseline: main `fbaa2ef1867e191f160cc3dbf9b8e26e10af45a7` after PR #647.
The [derivation and scope](../../docs/c4-finite-hull-witnesses-2026-11-21.md)
explain the result and the retained spectral obligations.

## Accepted local checks

- **60 project modules** in the targeted dependency closure were freshly
  compiled from repository sources in an initially empty project-output
  directory. No earlier project `.olean` was reused for this acceptance.
- All four audit fixtures passed: the existing family, zero-fibre and
  finite-automaton audits, and the new actual-hull witness audit.
- The new audit checks **26 declarations, 25 theorem constants, 22 named
  source proofs, 20 independent endpoint types/owners, and 48 refusal
  controls**. Recursive axiom closure permits only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Both new modules compile without warnings. Inherited compiler warnings
  from unchanged baseline modules are retained in `project-build.log`
  and `lean-receipt.json`.
- The native Mojo certificate check passed, including the complete control
  and output tables, all nine source/target pairs, reverse orientation,
  malformed-input refusals, the reduced-graph obstruction and 151-bit
  exact integer recipes.

The Lean compiler is pinned `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. The Mathlib revision is
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`. All nine external dependency
revisions and tracked source trees were checked; their existing compiled
artifacts were reused. The direct compiler invocation used the exact
project options `-DautoImplicit=false -Dpp.unicode.fun=true` and explicit
import paths containing only the fresh project outputs and those external
packages. This records a local source replay, not execution of the full
isolated shell gate or hosted acceptance.

## Receipts

`lean-receipt.json` binds all 60 compiled module sources and all four audit
fixtures by SHA-256. `build-receipts.json` retains each exact command,
exit status, duration and original local log locator. `project-build.log`
combines every project module's status and any compiler output. The four
named audit logs are preserved separately. `configuration-sha256.json`
binds the three Lean/Lake configuration files.

`native-receipt.json` records the exact Mojo compiler, command, source
digests and log digest; `native.log` preserves its contract receipts.
The native check is a concrete replay of the vendored engine. The actual
hull semantics are proved by the Lean modules, rather than inferred from
that native test alone.

The first local invocation of the existing family audit lacked a freshly
compiled audit-only dependency, `C4ParameterFamilyControls`. Its diagnostic
is retained under `diagnostics/`. The dependency was then compiled from
the unchanged baseline source and all four audits were replayed
successfully. This was a local replay-manifest omission, not a failed
mathematical assertion or a relaxed acceptance condition.

## Reproduction

From the repository root:

```sh
tools/check_c4_parameter_family.sh
```

From `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_family_tile_automaton.mojo
```

Hosted CI and full-repository acceptance remain separate observations.
The new proofs establish universal zero-fibre witnesses and dense
eventual coincidence for equal full images; they do not claim the
invariant-measure `L2` spectral conclusion.
