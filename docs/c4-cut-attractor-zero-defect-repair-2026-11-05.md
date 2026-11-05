# PR #499: zero-source-defect acceptance repair

Software regression repair against `8ae99ecdb0334564f57daec4314ff1848667d18d`.
Review locator: [zero-defect finding](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/499#discussion_r4479742857).
No merge or mathematical claim-status promotion is part of this correction.

## Work shown

### Assumptions and hypotheses

The executable input is a finite ordered child-closed set of nonempty,
irreducible, noncoincident balanced pairs over `{0,1,2}`, and a nonerasing
three-letter substitution. These finite routines accept controls outside the
irreducible-Pisot regime. Passing a control does not supply the hypotheses of
the cut-attractor manuscript's geometric arguments. This is a regression repair
of the existing contract, so no new theorem-facing diagnostic is introduced.

### Derivation / reduction

Let `tau` be the square of `012/120/201`. Its first two images are
`012120201` and `120201012`. From seed `(012,120)` the ordered closure has
three states and child matrix with every entry equal to 3. At interior cut 3
in the first parent state, `i = i' = 0`, `Q = 012`, `Q' = 120`, and
`d = p(Q) = p(Q') = (1,1,1)`. Both source prefixes are empty, but the source
letters are 0 and 1. Thus zero source defect does not imply parent coincidence.

The check now compares `(p(u[:i]), u[i])` with `(p(v[:i']), v[i'])`. Equality
of both the prefix address and source letter identifies the same parent tile;
prefix equality alone does not. This does not assert the converse about all
physical-coordinate coincidences for rationally dependent length vectors.

`validate_strict_closure` first validates all states, then recomputes the full
ordered irreducible factorisation of each inflation. Every supplied row entry,
cut position and complete child pair must match the corresponding occurrence,
including the initial cut. Missing/extra occurrences, forged indices, reordered
children and coincident factors raise. The cut-edge and lattice-recursion
entry points both run this check. It imposes no sink-SCC or seed-reachability
condition. The Python oracle reconstructs factors independently and checks
closure membership, optionally comparing supplied child rows. The oracle has
no supplied cut-position field: its cuts are always reconstructed.

### Evidence and replay

Before the implementation change, the newly added powered-control regression
failed in canonical Mojo with `zero source defect at an interior cut: the parent
tiles coincide`; the independent Python oracle failed its nonzero-defect
assertion on `(0,0,0) != (0,0,0)`. After the repair both accept 24 interior
edges, exactly six with zero source defect and different source letters.
The first edge has translation `(1,1,1)`, source indices `(0,0)` and image
offsets `(3,3)`. Eighteen edges use a shifted top source letter.

The original controls retain 12/6 interior edges, 8/6 shifted-source counts,
their child matrices, and exact `PN = MP`. Direct inflation and multiplicity-one
cut-lattice recursion agree through depth 3 for both original controls and the
powered control. Existing first-pair masks, hub checks, 54 configurations,
endpoint-collapse counts and bounded strong-coincidence witnesses still pass.

Local validation passed:

| Check | Result |
| --- | --- |
| Canonical cut-attractor regression | Pass, including powered positive control and malformed-closure refusals |
| Canonical H1 census regression | Pass, full 4,554 specimens and all pinned tables |
| Canonical cut-pair reduction | Pass |
| Canonical endpoint core | All 10 tests pass |
| Three focused Python oracle files | 17 tests pass |
| Proof bank, ledger, catalogue | Generated-source checks pass |
| Claim governance, vendoring, Markdown integrity, polyglot envelope, corpus refinement | Pass |

Replay from the repository root:

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_cut_attractor.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_h1_census.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_cut_pair_reduction.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_endpoint_core.mojo)
python3 -m pytest -o addopts= -q tests/test_c4_cut_attractor_oracle.py tests/test_h1_census_oracle.py tests/test_c4_cut_pair_reduction_oracle.py
python3 tools/make_proof_bank.py --check
python3 tools/make_ledger.py --check
python3 tools/make_math_catalogue.py --check
python3 tools/vendoring/check_vendored_sync.py
python3 tools/check_markdown_source.py
python3 tools/polyglot_envelope/render.py --check
python3 tools/corpus_refinement.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
```

Local native runs used the compiler and standard library already installed from
the versions pinned in `kernel/pixi.lock`: Mojo `1.1.0.dev2026090805 (34562fa1)`.
This is a minimal compiler installation, not a complete locked Pixi environment.
The focused workflow added by this repair uses the locked Pixi environment and
checks out and verifies the exact PR head. Hosted receipts must be checked
separately; local success is not a hosted success claim. The old inspected
head's hosted workflows were still queued when rechecked in this session.

### Negative controls

The canonical tests reject 14 mutations of a supplied valid closure: missing
row/cut tables, a missing occurrence, a forged cut, negative/out-of-range child
indices, reordered children, a forged initial cut, unbalanced/reducible states,
out-of-alphabet letters, duplicate states, an extra occurrence and an empty
state. They also reject an empty closure, genuine same-start/same-letter parent
coincidence, and a supplied unit-PIP swap closure that hides coincident factors.
Both cut-edge enumeration and cut-lattice recursion must raise for each case.

The reordered-child control preserves `PN = MP`; acceptance based only on
aggregate incidence would therefore miss it. The independent oracle separately
rejects missing child states, malformed states, incomplete/extra/reordered rows,
invalid indices, true coincidences and an exhausted state cap. Existing strict
seed, state-cap and bounded-search refusal controls remain in place. Exhausted
search is still inconclusive; this repair does not change budget semantics.

### Non-claims / remaining gaps

The H1 implementation, its Anderson-Putnam oracle, both census test files,
the H1 manuscript and `claim_governance.toml` are unchanged from the inspected
head. The replayed dimension histogram remains `{3:3102, 4:552, 5:720, 7:180}`;
the unimodular histogram remains `{3:1740, 4:396, 5:408, 7:84}`. Both full
determinant-by-dimension and endpoint-by-dimension tables still match their
existing pins; the canonical test also checks all nine eventual-range shapes.

This verifies finite software behavior and preservation of the reported census
tables. It does not independently prove that the census computes the stated
cohomological invariant, validate the cut-attractor's limit/interior arguments,
certify a spectrum, or discharge a universal PSC obligation. The mathematical
arguments and their independent review status remain separate and unchanged.
