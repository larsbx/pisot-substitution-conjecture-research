# Uniform seed-carrier certificate for the minus residual

Parent: `00c0cb86a2d9902a3e1beaf4163bff2a326a7a9e`. Date: 2026-10-20 UTC.

## Result and exact scope

For every integer a>=2,b>=1, all real canonical swap seeds and every real
occurrence child before terminal coincidence remain in the sealed 145-label
carrier. All these labels have |wx+wc+wy|<=1. This proves the seed-qualified
CycleSum premise on this residual domain. The ranked descent then gives
scoped boundary hitting. Universal #139/#84, aligned coincidence and PSC
remain open. This does not reinstate the false seed-free RC premise.

The proof is an induction, not a parameter census. Exact Perron identities
establish 0<X,Y<1, 10X>7Y and 10-10X>3Y for X=beta-r-2,Y=10/beta.
Every child sum is enumerated within a bound derived from interior geometry;
|s'|<=1 is not assumed. Canonical Mojo checks exact Farkas certificates for
all excluded seeds/children. Independent Fraction vertex enumeration agrees:
9 seeds included, 3 nonreal; 12,255 child candidates partition into 1,218
carrier targets, 9,034 strict-geometry exclusions, 2,003 guard exclusions.
There are 1,287 source/segment pairs and two equal-letter zero terminals.
Distinct-letter zero states are expanded. Full derivation: research note §14.

## Replay

Available local compiler: Mojo 1.1.0 (8189361e). From `kernel/`, with the
repository-pinned environment available:

```sh
export MODULAR_TELEMETRY_ENABLED=false MODULAR_CRASH_REPORTING_ENABLED=false
pixi run mojo run -I . tests/test_class_d_minus_seed_cover.mojo
pixi run mojo run -I . class_d_minus_seed_cover.mojo > ../seed-cover.log
```

From the repository root:

```sh
python oracles/python/class_d_minus_seed_cover.py --mojo-log seed-cover.log > seed-cover.json
CLASS_D_SEED_COVER_REPORT=seed-cover.json CLASS_D_SEED_COVER_MOJO_LOG=seed-cover.log python -m pytest -q tests/test_class_d_minus_seed_cover.py
python tools/make_ledger.py --check
python tools/make_proof_bank.py --check
PYTHONPATH=tools python -m claim_governance.cli --root .
TLA_TOOLS=/path/to/tla2tools.jar bash proof/tla/check.sh
```

`mojo-test.log` includes the uniform certificate, a removed-child-target
refusal, a coarse-geometry seed refusal, and reached claim receipts.
`mojo-driver.log` and `python-calibration.json` agree on the entire tally.
The workflow always preserves logs/JSON, including unresolved obligations.

`python-tests.log` records the focused seed-cover, ledger, shared-cycle,
high-sum and research-policy regressions. The optional pytest TLC mutation
check skips when TLA_TOOLS is unset; all 17 models pass in `tla.log` under the
explicit JAR invocation. The open ledger now establishes the three scoped
minus claims, while universal #139 and the PSC assembly remain unestablished.
`governance.log` records source integrity, vendoring, generated surfaces and
full claim governance. Pinned source hashes are in `source-sha256.json`.

## Negative controls and exploratory provenance

`coarse-box-obligations.json` is a deliberately unsuccessful run:

```sh
python oracles/python/class_d_minus_seed_cover.py --coarse > coarse.json
# Expected exit status: 1; 149 unresolved relaxed obligations.
```

There are 148 child obligations at 19 outside labels, plus one seed. These
rational box witnesses are not actual substitution counterexamples. The
correlated inequalities remove them. `direct-norm-refusal.log` preserves the
failed direct symbolic sign search; exact Perron polynomial identities avoid
its sign-changing auxiliary polynomial without changing the domain.

`exploratory-seed-graphs.json` preserves the five complete exact graphs at
(2,1),(3,1),(2,8),(8,1),(8,8). Their 137/139 states all lie in the carrier.
They motivated the induction but supply no universal quantifier. The earlier
six-edge incompatibility and higher-sum formal-cycle packets are unchanged.

## Validation limits

Local execution uses the available Mojo release, not the pinned nightly.
The previously documented pinned pixi download/tunnel failure is unresolved;
no environment pin has been changed. GitHub jobs on the parent were still
queued. Pinned CI and independent human review remain required validation
work, so this PR is not represented as merge-ready or independently reviewed.
The mathematical claim is restricted to the exact seed graph and residual
parameter domain; no full non-unit realization hypothesis is supplied.
