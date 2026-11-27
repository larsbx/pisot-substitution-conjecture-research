# Local acceptance receipts: zero-fibre witness increment

The mathematical result and its formal boundary are in
[the review note](../../docs/c4-zero-fibre-witness-review-2026-11-21.md).
The candidate proves a full-history zero-fibre characterization and
genuine exact common-shift witnesses for constructed seam and interior
orbits. It does **not** close the universal witness obligation in Lean.

## Revisions and provenance

- Candidate base: PR #643 head
  `7a5025ed7b8104413477ea7fbd15b52206e0959c`.
- Baseline tree: `371684de70999cef922b4ce0b7f4e34f3a931692`.
- Inspected main: `7de25513b127d6e72709354d95c39e3d5273e2db`.
- Lean: `4.34.0-rc2`, compiler commit
  `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Mathlib: `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.
- Explicit project compiler options:
  `-DautoImplicit=false -Dpp.unicode.fun=true`.

[provenance.json](provenance.json) records compiler binary SHA-256 values,
configuration hashes, all nine dependency revisions, and their clean
tracked working trees. External dependency `.olean` files were reused.
Their source revisions were checked, but those external packages were
not rebuilt or re-downloaded in this session.

[github-final-observation.json](github-final-observation.json) records
the final read-only GitHub inspection; [github-observation.json](github-observation.json)
retains the earlier observation. The workflow query returns the first page of
pull-request-triggered runs. The exact #643 family run `44932455316`
was queued at the recorded observation. Local acceptance is not hosted
acceptance. This candidate has not been published.

## Recorded acceptance scope

| Check | Exact #643 baseline | New candidate |
| --- | ---: | ---: |
| Project modules compiled from source | 49 | 7 |
| Audit fixtures compiled | 1 | 1 |
| Owned modules inspected by scoped audit | 23 | 7 |
| Owned declarations audited | 1,053 | 49 |
| Owned theorem constants audited | 905 | 45 |
| Independently spelled public endpoint types and owners | 35 | 38 |
| Wrong-type / missing-name refusal controls | 70 | 76 |
| Initial/final source SHA-256 guards | Passed | Passed |
| Allowed recursive axiom dependencies | `propext`, `Classical.choice`, `Quot.sound` | Same |

The baseline project closure was compiled from an empty project output
directory in an isolated worktree at the exact PR head. The candidate
modules were compiled into a fresh output directory against that freshly
rebuilt baseline. Lean resolves a module namespace from one import root;
the candidate output therefore links the fresh baseline artifacts into
the same namespace. No old development overlay or pre-existing project
artifact was used by the final strict replay.

The audit fixture checks all declarations owned by the listed modules,
not just the public endpoints. Its endpoint checks independently expand
the witness quantifiers, verify literal parameter guards and module
ownership, and reject deliberately wrong or missing declarations.
Standard axiom closure does not erase theorem hypotheses: the universal
anchor statement is still only an equivalence, not a proved instance.

## Files

- `baseline/`: final strict compiler receipts, source digests, import
  graph, complete audit output and per-module compiler logs.
- `candidate/`: final strict receipts and source digests for the seven
  new modules and `C4ZeroFibreWitnessAudit.lean`, plus complete audit
  output and compiler logs.
- `baseline/EndpointAxioms.lean` and `baseline/EndpointAxioms.log`: extra
  endpoint type/axiom queries from the initial fresh baseline replay.
  The final strict replay produced byte-identical baseline artifacts;
  `baseline/option-parity.json` records that comparison for all 50 files.
- `checks/`: generated proof-bank and dependency-pin checks for both the
  baseline and candidate, plus final shell syntax/patch hygiene checks.
- `diagnostics/`: the retained candidate import-root failure and its
  explanation. It was a replay-path issue; no proof source was changed
  to repair it.
- `SHA256SUMS`: hashes of the archived evidence files, with paths relative
  to this directory.
- `candidate-reviewed-source-sha256.json`: hashes of all new or modified
  non-evidence files in the review increment, including the proofs,
  documentation and generated proof bank.

The archived compiler receipts retain the absolute executor paths at
which the run occurred. They are provenance records. The source-replay
commands below are the portable entry points. The baseline and candidate
drivers under their respective directories preserve the exact recorded
compiler orchestration; their path constants require adjustment outside
this executor.

An initial direct-compiler run used default Lean options. The final
strict replay above repeated the baseline and candidate with both
configured project options explicitly set. The initial baseline's 50
artifacts and the final strict baseline's 50 artifacts were all
byte-identical; all eight candidate artifacts were also byte-identical
between its two runs. The candidate acceptance summary records that
comparison. Counts in the table refer to the final strict runs.

## Reproduction

Apply the local review patch after checking out the exact PR #643 head.
Use the toolchain named in `proof/PscVerif/lean-toolchain` and dependencies
from `proof/PscVerif/lake-manifest.json`.

The full isolated repository gate, extended by this candidate, is:

```sh
tools/check_c4_parameter_family.sh
```

It provisions an isolated audit workspace, verifies pins, builds the
family and candidate dependency closure, runs both audit fixtures, and
checks their receipt counts. **That complete shell gate was not run in
this executor**, which has no `elan` command. The recorded local result
is the fresh project-source replay using the pinned Lean binary directly
and explicitly supplied import paths. No hosted or repository-wide
acceptance is inferred from it.

For a provisioned local Lake checkout, the focused replay is:

```sh
python3 tools/make_proof_bank.py --check
python3 tools/make_proof_bank.py --pins-only --require-packages
cd proof/PscVerif
lake --no-cache build PscVerif.C4ParameterFamilySolenoid PscVerif.C4ParameterFamilyControls PscVerif.UniversalClosureReduction PscVerif.PeriodicPartnerRealizationModels PscVerif.C4ParameterFamilyZeroFibreWitnesses PscVerif.C4ParameterFamilyZeroFibreControls PscVerif.C4ParameterFamilyInteriorZero
lake --no-cache env lean -DautoImplicit=false -Dpp.unicode.fun=true C4ParameterFamilyAudit.lean
lake --no-cache env lean -DautoImplicit=false -Dpp.unicode.fun=true C4ZeroFibreWitnessAudit.lean
```

Expected final receipt lines include:

```text
PSC_PARAMETER_FAMILY_DECLARATIONS  23  1053  905
PSC_PARAMETER_FAMILY_AUDIT_COMPLETE  35  70
PSC_ZERO_FIBRE_DECLARATIONS  7  49  45
PSC_ZERO_FIBRE_AUDIT_COMPLETE  38  76
```

The actual logs use tab separators. The updated gate checks those
separators and exact counts. The candidate proof-bank check reports 132
claims, 6,500 named Lean proofs and 544 source openings. Those are
repository inventory counts; only the scoped closure in the table was
recompiled here.

To check the archived receipt bytes:

```sh
cd evidence/c4-zero-fibre-witnesses-2026-11-21
sha256sum -c SHA256SUMS
```

No claim status was promoted by this increment. The family retains its
separate written spectral proof, and the remaining Lean interfaces are
listed in the review and spectral notes.
