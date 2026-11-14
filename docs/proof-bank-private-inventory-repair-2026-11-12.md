# Private proof inventory regression repair

## Scope

The private-name reconciliation test must accept legitimate private proofs
already present in the copied project, while requiring every injected fixture
proof and every production proof in the complete compiled-audit inventory.
This repairs the existing test contract. It introduces no mathematical result
or new acceptance rule and needs no new theorem-design literature gate.

The repair is based on PR #560 at
`d6d6ba2331bc119282a9b18170053c4eb24a9346`. The affected test file has identical
Git blob `85a2c81c8c42198fd4e597774138a29c34b0dcfd` at PR #564 head
`16dd825648d1a1bcdba9038e079463a9bebbaf3d`, so the same regression is inherited
by the stacked packing and strict-exclusion work.

## Cause and correction

`test_private_proofs_reconcile_by_source_name_and_module_without_collapsing_counts`
copies the entire Lean project, then adds two private proofs per synthetic
module. Its old assertion counted every private proof in that combined tree
but expected only the injected two or four proofs. PR #560 adds three genuine
private helpers in `StrictCutCount` and `NamedCutCount`, so the assertion fails
with `5 != 2` or `7 != 4`.

The corrected test records the original private inventory after adding the
root imports and before injecting the fixture proofs. This preserves source
line identities even if the root module itself contains private declarations.
It requires exactly the two expected `(module, source name)` identities per
synthetic module and compares all other private records with the unchanged
original inventory. The complete audit still receives the full production
and fixture inventory. No production declaration is filtered from that audit.

The negative control independently omits each injected proof, including
same-named proofs in different modules, and one original production private
proof. Each incomplete transcript must be refused even after its terminal
counts are adjusted to match the remaining records. Thus the repair checks
identity completeness rather than accepting a matching aggregate count.

## Observed evidence

At the exact PR #560 head above:

- [C4 overlap Lean verification, run 43308193930](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43308193930)
  checked out that revision, built `StrictCutCount` and `NamedCutCount`,
  completed 9,025 build jobs, and audited 6,646 declarations including 4,865
  theorems. The log reports all named proofs reached.
- [Original archived payload Lean import, run 43308193694](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43308193694)
  passed the full build, compiled audit, and both concrete fixture replays.
  These receipts belong to the protocol at #560; they do not certify #564's
  later `no_strict_system` obligation.
- [PSC research checks, run 43308194104](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43308194104)
  failed only its `python-tests` job among the returned job set. That job
  reports the two private-count failures, 2,122 passing tests, 13 skips, and
  28 passing subtests. Its `lean-proofs` and `mojo-kernel` jobs passed.
- [Canonical Pisot polynomial kernels, run 43308193959](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43308193959)
  passed its exact equivalence and benchmark steps, then failed the repository
  verification step on the same two Python assertions.

The failure is in a regression-test assumption exposed by new private
declarations. Neither hosted failure is evidence that the new Lean proofs or
the polynomial kernels failed.

## Local replay

From the repository root, with the project's Python test dependencies available:

```sh
python3 -m pytest -o addopts= -q tests/test_proof_bank.py
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
python3 tools/vendoring/check_vendored_sync.py
python3 tools/check_markdown_source.py
python3 tools/check_manuscript_source.py
PYTHONPATH=tools python3 -m claim_governance.cli --root .
git diff --check
```

Before the repair, the focused command with `-k private_proofs_reconcile`
reproduced both hosted failures: **2 failed, 55 deselected**. The local Python
environment initially lacked pytest; the actual test replay used the existing
pytest 9.2.0 installation via `PYTHONPATH`. This is a test dependency selection,
not a change to the repository's proof or acceptance policy.

The post-repair run of the complete `tests/test_proof_bank.py` file passed:
**57 passed, 1 warning in 27.94 seconds** after the source-line robustness
adjustment (the initial repair also passed all 57 tests). The warning is an existing external
AnyIO pytest-plugin deprecation. All six listed source/governance commands
also exited zero: the proof bank retained 126 claims, 2,705 named Lean proofs
and 411 source openings; 32 generated ledger surfaces were current; vendored
pins, Markdown integrity, manuscript integrity and all claim-governance checks
passed. `git diff --check` passed.

A passing local test does not retroactively change either historical workflow
result. Hosted verification at the repair revision remains a separate required
observation. The active #564 full Lean and concrete-payload run is unaffected
by this test-only repair.
