# Family spectral inputs and universal-route control: verification record

## Publication-time status

The independent integrated local audit passed with **8 owned modules,
618 constants, 547 theorem constants, 11 exact endpoints and 22 rejected
controls**. All accepted endpoint axiom closures contain only `propext`,
`Classical.choice` and `Quot.sound`. The arithmetic, general factor adapter
and composed family source have explicit successful local compiler receipts.

These local runs use the recorded cached dependency environment. **The new
revision's hosted source-isolated result is pending at publication.** The PR
description records later hosted results without rewriting this initial packet.
Successful predecessor receipts are preserved at their own scope in
[parent-acceptance.json](parent-acceptance.json).

The original private universal-control source build produced a matching proof
object and a complete profiler log, but its explicit terminal return was not
retained. [The observation receipt](local/universal-object-observation.json)
keeps that field null. Object existence is not substituted for a terminal
source-build receipt. The later integrated audit has its own explicit exit zero
and verifies both literal control endpoint types and all 35 owned constants.
The required hosted gate rebuilds the control from source along with the family.

## Mathematical scope

- For `sigma_k=(1,0 1^k 2,001)`, `k>=1`, the actual incidence is primitive,
  has irreducible rational characteristic polynomial, and has an irrational
  root above two with all other complex roots of modulus below one. A positive
  left eigenvector supplies the actual tile lengths.
- A general single-seed theorem identifies terminal-child termination with
  finite full-iterate factors and eventual singleton coincidence for every
  factor, under the stated finite-alphabet and irreducible-block premises.
- For `k>=2`, the family supplies the complete literal arithmetic and
  full-factor inputs of the published spectral criterion, without assumed
  finiteness, roots, productivity or archive validity.
- The binary non-Pisot control `0->00001,1->011` is productive on every block
  but has infinite actual seed reachability. The proof retains complete ordered
  child rows and their repeated occurrences. It is no counterexample inside PIP.

See the [family reconstruction](../../docs/c4-family-spectral-closure-2026-11-14.md)
and [universal closure review](../../docs/psc-universal-closure-review-2026-11-14.md).
The spectral implication and dynamical realization remain explicitly external
to Lean. All 126 governed claim statuses are unchanged.

## Exact evidence

[source-inputs.json](source-inputs.json) binds the nineteen directly reviewed
source/configuration inputs to SHA-256 values and records predecessor
`32015cfb9d0914cedc9867f3290ea4bcdbbbb3b7`. The generated proof bank additionally
binds all project proof inputs. Git supplies the committed packet's final source
revision and tree; the PR records those identifiers once publication assigns them.

| Receipt | Result |
| --- | --- |
| [Pisot compilation](local/pisot.json) | Exit zero; exact source unchanged |
| [Factor-adapter compilation](local/factors.json) | Exit zero; exact source unchanged |
| [Composed family compilation](local/bridge.json) | Exit zero; exact source unchanged |
| [Integrated endpoint audit](local/endpoint-audit.json) | Exit zero; all eight module sources unchanged |
| [Complete audit transcript](local/endpoint-audit.log) | 11 literal/polymorphic endpoints and 22 rejection controls |
| [Source/governance checks](local/checks.json) | All recorded commands exit zero |

The proof-bank test command completed all **57 tests** successfully. The
regenerated inventory contains **126 claims, 3,822 named Lean proofs and 411
source openings**. Markdown source integrity, vendored pins, whitespace and
all six claim-governance checks passed. Inventory counts do not promote any
mathematical claim.

## Rejected controls and historical diagnostics

The runtime type recognizer refuses a wrong-typed theorem and an absent
declaration for each endpoint. The polymorphic equivalence uses a rigid expected
universe and requires matching universe arity. Literal words and ordered seeds
are independently spelled out in the expected types.

The actual expanded shell parser rejects the earlier successful nine-endpoint
receipt: [stale-receipt refusal](diagnostics/nine-endpoint/stale-nine-endpoint-refusal.json).
That earlier audit source and result remain in the same diagnostic directory.
Local failed elaborations and the universal profiler record are retained under
`diagnostics/`; none is credited as successful source acceptance.

Mathematical controls retain the false stronger statements: zero cannot inherit
the root-above-two endpoint; immediate coincidence fails at family parameter two;
finite factors alone do not give productivity; full and terminal reachable sets
need not coincide; and productivity alone does not give finiteness outside PIP.

## Replay

From the repository root:

```sh
./tools/setup_lean.sh
./tools/check_c4_parameter_family.sh
./tools/check_lean.sh
python tools/make_proof_bank.py --check
python -m pytest -q tests/test_proof_bank.py
PYTHONPATH=tools python -m claim_governance.cli --root .
```

The focused gate prepares a fresh source/configuration-only workspace, verifies
the pinned compiler and dependencies, compiles the full required closure, and
executes a fresh audit. It requires each of the eleven endpoint names exactly
once, all eight owned modules and exactly one `11 / 22` completion record.
The unchanged full-library gate independently checks the entire project.

The [SHA256SUMS](SHA256SUMS) manifest verifies all files in this packet other
than the manifest itself; run `sha256sum -c SHA256SUMS` from this directory.
