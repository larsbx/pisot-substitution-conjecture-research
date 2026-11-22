# Finite tile-chain certificate acceptance

Source baseline: `f5ca04063db75722e7736cfbad36629b7cd36d35`. Source hashes and
exact toolchain identities are in the two JSON receipts.

- Native Mojo 1.1.0.dev2026090805 passed the concrete DFA, signed-output,
  integer-recipe and negative controls. `native-receipt.json` records the
  extracted compiler invocation; the normal pinned-environment replay is
  `pixi run --locked mojo run -I . tests/test_family_tile_automaton.mojo`
  from `kernel/`. A first bare compiler invocation lacked its standard
  library path; the recorded successful invocation sets the package paths.
- Fresh local Lean compilation passed for both new modules and their
  baseline word dependency. The combined audit checked 164 declarations,
  103 theorem constants, 44 source-named proofs, 10 endpoint types/owners
  and 20 refusal controls. Only the three standard axioms were admitted.
- Local Lean reused pinned dependency artifacts; this is scoped evidence,
  not the fresh hosted or full-repository acceptance gate.
- `tools/check_c4_parameter_family.sh` is the independent source-isolated
  hosted replay entrypoint, including the new audit.

The implementation is a finite-control automaton with unbounded exact integer
output. Actual-hull interpretation and spectral closure remain separate.
