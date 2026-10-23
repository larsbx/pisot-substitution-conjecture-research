# Exact class-A gap sign component

Base main: d2c3aa8. The finite regime fits already exist on main; this packet
implements step (b) from docs/class-a-gap-uniformity-stopgo-2026-10-23.md.

- `native.log` / `native.exit`: full native regression, eight PSC foundational
  margin calibrations, 81 bilinear decisions and 225 coefficient fixtures.
- `oracle.log`: independent Fraction audit of all coefficients, unisolvent
  polynomial identity checks and bilinear false-acceptance controls.
- `validation.log`: local Python regression/link/proof-bank/policy checks.
- `provenance.log`: local provenance and claim-governance checks.
- `source-digests.json`: local kernel, oracle and lock input hashes.
- `replay.sh`: fresh full locked Pixi build/run, independent audit and receipt
  comparisons. Hosted CI performs the same fresh native/audit comparisons.

Local native execution used the existing minimal lock-matched
Mojo 1.1.0.dev2026090805 (34562fa1) runtime, not a full Pixi installation.
Set MODULAR_MAX_PACKAGE_ROOT and MODULAR_MOJO_MAX_PACKAGE_ROOT to that
runtime root, and MODULAR_MOJO_MAX_IMPORT_PATH to its lib/mojo; then build
with bin/mojo build -I kernel kernel/tests/test_class_a_gap_sign.mojo.
The optional crash reporter is absent; its build warning is not a proof
receipt. The input degrees are bounded by 8, depth by 12 and visited cells
by 8191; exhausted search refuses rather than returning a partial proof.

No full repository Mojo/Lean/TLA+ replay, independent human review, whole-line
class-A gap-five certificate or universal boundary-hitting closure is claimed.
The margin checker is a sound sufficient test with conservative refusals.
