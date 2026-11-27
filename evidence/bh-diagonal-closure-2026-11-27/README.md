# Three-band literal closure and finite BPA: verification record

**Status:** the source-isolated local gate passed on 27 November 2026.
The new uniform Lean endpoints establish actual arithmetic on `4<=r<=k`
and literal closure with finite balanced-pair termination on
`12<=r<=k<=r+2`. Hosted acceptance and independent human review are separate
validation states. The general Pisot Substitution Conjecture remains open.

This packet continues the unchanged
[residual evidence packet](../bh-diagonal-residual-2026-11-27/README.md).
The source base is `f0b3348265b0050ca28e0b51a7527e8b0c1224f0`, with integrated
main `366430a5d3b1adb29bbe092166a9a70f362ba408`. `revision.txt` records the
pre-continuation commit and tree; the before/after SHA-256 bindings, rather
than that older commit alone, identify the sources actually verified.

## Mathematical scope

The literal substitution is `sigma=(1,01^k2,0^r1)` on three letters. The
root `beta` lies in `(k,k+1)` and satisfies `beta^3-k*beta^2-2*beta-r=0`.
The positive lengths are `(1,beta,1+r/beta)`. All packets retain both
letters and the complete integral displacement vector.

| Endpoint | Exact scope and conclusion | Boundary |
| --- | --- | --- |
| `BHHigherDeterminantPisot.primitive_irreducible_pisot` | Every natural `4<=r<=k`: actual incidence is primitive, its rational characteristic polynomial is irreducible, its expanding root exists, and every other complex root has norm below one; actual positive lengths scale correctly | Arithmetic alone does not establish coincidence |
| `BHDiagonalAllSources.three_band_all_source_exit` | Every natural `12<=r<=k<=r+2`: every strict full integral typed source has a finite actual interior path to equal letters and full zero displacement | No common numerical depth bound for the infinite collection of sources |
| `BHThreeBandClosure.family_closure` | The same three bands: one constructed root supports actual arithmetic, ordered original-occurrence paths, all-pairs left strong coincidence and exclusion of finite strict systems | No dynamical spectrum is built in Lean |
| `BHPisotFiniteBPA.terminates_of_pisot_all_source_exit` | Generic three-letter implication from actual irreducible Pisot arithmetic, positive image-scaling lengths and exits from every strict packet to finite BPA termination with coincidence for every irreducible balanced seed | The generic all-source exit premise remains a premise |
| `BHThreeBandBPA.all_blocks_full_factor_coincidence` | Every natural `12<=r<=k<=r+2`, every irreducible balanced seed: the full collection of irreducible factors in all substituted iterates is finite, and each factor eventually produces a literal singleton coincidence | The family specialization has no supplied carrier, certificate or termination premise |

The [closure derivation](../../docs/bh-diagonal-closure-2026-11-27.md)
explains the completed classification, outer descent, signed progress,
third-level actual entry, contraction carrier and full-factor assembly.
The [spectral-transfer note](../../docs/bh-three-band-spectral-transfer-2026-11-27.md)
checks the published balanced-pair criterion and combines these bands with
the earlier small-parameter certificates and bivariate canonical-seed
argument. Its full-domain pure discrete **tiling-flow** conclusion remains
a written application of external theorems, not a new Lean spectral theorem
or an assertion about a constant-roof symbolic shift.

## Fresh Lean build and audit

The gate rebuilt the selected project dependency closure from an isolated,
byte-matched source copy with no inherited local project objects. Pinned
upstream dependency source bytes were checked before and after; their
compiled cache was reused. This was not a fresh build of all Mathlib or all
PSC modules.

`lean-summary.json` and `lean-audit.log` record:

- 18 explicitly listed modules;
- 44 explicitly checked public endpoints, including the exact capstone
  signatures and the inherited counterexamples;
- 401 recursively audited compiled declarations, including 365 theorem
  constants;
- only `propext`, `Classical.choice` and `Quot.sound` in the recursive axiom
  closures; no `sorryAx` or additional local axiom.

These are audit inventory counts. They include preserved contraction proofs
and generated declarations, and are not counts of newly discovered results.
The inherited residual, literal and near-diagonal audits also passed.

Tool versions in `versions.log` are Lean `4.34.0-rc2`, Mojo
`1.1.0.dev2026090805` and Python `3.12.14`. Mathlib remains pinned at
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09` by the checked Lake manifest.

## Exact native replay and independent oracle

The canonical Mojo residual replay used parameters
`r=12,13,15,16,18,20,32`. Its records contain 7,899 strict-disk integer
pairs and 23,697 complete full-packet paths to equal-letter zero. A further
792 original-occurrence edges check the axis and exceptional blocks. The
longest observed complete path has 113 edges.

The independent Python oracle reconstructs the finite graph using rational
root brackets and agrees with every one of the 10,679 exported state
records. The surrounding finite square contains uncovered states, recorded
as such; all sampled strict-disk pairs are covered. The oracle checks four
negative-control tests. These finite computations exercise the executable
contracts; Lean supplies the universal parameter quantifiers.

The third-level native test checks 6,069 strict source packets across
`(r,k)=(12,12),(12,13),(12,14),(16,16),(16,17),(16,18),(20,20),(20,21),(20,22)`.
It reconstructs the two original occurrence triples and checks all three
literal inflation steps. The last-window, wrong-ordinal and contact
controls remain active. The third window need not occur in these sampled
valid packets for the test's separate last-window control to be exercised.

The residual graph caps are 10,000 states, 30,000 edges and 10,000 edges
per selected path. The oracle starts with a 96-bit rational root bracket
and refines uncertain signs up to its declared 768-bit cap. Uncertainty or
budget exhaustion refuses a verdict. No floating-point predicate is used.

The native export SHA-256 is
`325d8541ab37a3e90384afa239338269762a54afc008299759b2bfa6319ffca3`.
The independent oracle binds that exact export. Full paths are replayed;
this packet does not serialize every complete occurrence transcript.

## Source integrity and preserved failures

`source-bindings.json` and `source-bindings-after.json` are byte-identical
maps of all 8,211 tracked or unignored input files outside this output
directory. The map SHA-256 is
`76c50234f26c5c895728042de85ae2e6954944973bcd17ed362fa9f9eb478d81`.
The gate rejects missing inputs or source symlinks. It additionally checks
the complete isolated project source copy before the build, after the
build, after the Lean audits and after native replay. Evidence files in
this directory are excluded from source bindings and pinned separately by
`SHA256SUMS`.

`before-scope-record.tar.gz` preserves the entire first successful packet,
including its original checksums and 294 passing focused tests, byte-for-byte.
`before-scope-record.json` records the archive digest and the reason for
retaining it. The archive also preserves the earlier stale-inventory refusal
before Lean compilation and a vendoring CLI usage refusal followed by its
successful corrected invocation.

After that successful gate, a review found that the dependency ledger used
default same-scope edges for three differently scoped premises of
`ThreeBandFiniteBPA`. The correction records exactly three checked Lean
applications with their exact target scopes. Every other edge retains the
default scope rule. The family closure is now complete; the generic exit
premise and the general conjecture nodes remain open. The proof sources
were unchanged, and the complete source-isolated gate was repeated on the
corrected tree. `scope-record-correction/source-change-receipt.json` records
the precise source delta and its hashes.

The next invocation completed its Lean build and audit, then automatic
approval review stopped Mojo because it attempted an unauthorized telemetry
request. That partial run is preserved in `telemetry-interrupted.tar.gz`
and described in `telemetry-interrupted.json`; it is not credited as a
completed gate. The final gate sets the vendor-supported
`MODULAR_TELEMETRY_ENABLED=false` and
`MODULAR_CRASH_REPORTING_ENABLED=false` before invoking Mojo and records
them in `telemetry-policy.log`. No network policy or approval rule was
changed. The final source bindings include these gate settings and the
additional side-ledger entry; the earlier scope-correction hashes identify
the preceding metadata state. See the
[official FAQ](https://mojolang.static.modular.com/nightly/docs/faq/) and
[release setting](https://mojolang.static.modular.com/releases/v1.0.0/).

`extraction-source-validation.json` records the dependency extraction from
`GeometricFStrict` and `GeometricFPisot`. The original 33-line length block
and 267-line contraction block were moved byte-for-byte into smaller
modules, imported back by their old consumers. Their public names, theorem
bodies and remaining legacy content were preserved. An independently
checked characteristic-polynomial cast identity was added in the core
namespace. The new gate compiles and audits these smaller modules; it does
not claim a replay of the complete legacy application suite.

The retained counterexamples distinguish projected zero from full integral
zero, mixed-letter zero from coincidence, and centrality from strictness.
They also preserve the genuine nearest-rounding cycle, the failure of a
real-valued congruence substitute, and the expanding zero-hit example for
the finite-BPA bridge. Native checks refuse forged ranks, wrong ordinals,
altered first coordinates, false typed endpoints and exhausted budgets.

## Replay and repository checks

Prepare the repository-pinned Lean and Mojo toolchains, pinned Lake
dependencies and their cache, and Python with pytest. From the repository
root, choose an empty output directory:

```sh
PSC_DIAGONAL_CLOSURE_EVIDENCE_DIR=/tmp/psc-diagonal-closure-review \
  tools/check_bh_diagonal_closure.sh
```

Set `PSC_MOJO` if the locked Mojo installation is invoked through an
executable wrapper. The gate refuses a nonempty evidence directory, stale
proof inventory, changed dependency pins, copied-source mismatch,
unexpected project artifacts, incomplete audit receipts, native/oracle
disagreement or source changes during verification.

The successful completion marker is
`PSC_BH_DIAGONAL_CLOSURE_GATE_COMPLETE 18 44 401 365 8211` (tab-separated
in `gate-stdout.log`). After the scope-record correction, the focused proof-bank, ledger and
claim-governance suite passed **93 tests**, including all 12 new scope
regressions. Two optional TLC controls were skipped because `TLA_TOOLS` was
not installed. The initial interpreter invocation lacked pytest and is
preserved beside the successful run in the prepared pytest environment.
Removing an adapter, changing a target scope or making a mathematical
premise pending prevents complete family closure in the negative controls.

The final documentation, recorded-data, Markdown-source, catalogue and
claim-coverage suite passed **231 tests**. Proof-bank, ledger and catalogue
freshness, all six claim-governance checks, manuscript audit, Markdown source
integrity, vendored pins and whitespace checks passed. The final source
recheck found zero changed, added or removed inputs outside this evidence
directory. The receipts are in `final-artifact-tests.log` and
`final-consistency/`. The completed archive and checksum manifest receive
a final recorded-data check before publication.

Hosted CI acceptance must be assessed at the eventual published commit;
local pass receipts do not supply it.

General BH, residual A1-prime, general C4 and PSC keep their existing
status. This continuation records four narrower governed claims and does
not add a dependency edge that closes any general conjecture.
