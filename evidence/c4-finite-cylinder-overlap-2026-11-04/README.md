# Finite-cylinder overlap: reproducible evidence

This packet accompanies the [scoped verifier and derivation](../../docs/c4-finite-cylinder-overlap-verifier-2026-11-04.md)
and [literature gate](../../docs/c4-finite-cylinder-overlap-literature-gate-2026-11-04.md).
Its dependency is PR #494 at `6ee339c670e711eddc4bfbe43e8b0b9dbc2876ce`.
The completed occupancy bounds from that PR are not recalculated here.

## What a receipt means

The canonical implementation is Mojo. The independent Python verifier
reconstructs literal words and quotient classes by rational Gaussian
inversion, then checks every affine-box corner in the cubic number field.
It does not trust printed areas, covolumes, residue refinements or claims
of a positive strict-cut density.

`native-driver.stdout.txt` is the full finite certificate, not a summary.
`independent-report.json` records its independently checked bounds and the
necessary `U<2` screen. Every receipt records the command, explicit local
runtime overrides, start time, process exit and source revision.
`validation-manifest.json` records source and evidence digests, distinguishing
the validated executable source from later documentation/evidence commits.

The finite packet covers two productive non-unit controls, even depths
2,4,6, all 1,002 occurrence records, 283 nonempty slice hulls and 18 pair
bounds. The number of occurrences is unrelated to the 144 occupancy rows
of the prerequisite PR. The two counts describe different finite objects.

## Reproduction

From the repository root:

```bash
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_finite_cylinder_overlap.mojo)
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_cylinder_density.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_finite_cylinder_overlap.mojo) > /tmp/cylinder.txt
PSC_CYLINDER_NATIVE_OUTPUT=/tmp/cylinder.txt python tests/test_c4_finite_cylinder_overlap_oracle.py
python oracles/python/c4_finite_cylinder_overlap.py /tmp/cylinder.txt > /tmp/cylinder-report.json
python tools/make_proof_bank.py --check
PYTHONPATH=tools python -m claim_governance.cli --root .
python tools/check_markdown_source.py
python tools/vendoring/check_vendored_sync.py
```

The file `rejected-empty-strict-component.json` is intentionally invalid
mathematical input with valid syntax. It chooses a zero upper bound but
provides no strict words. The oracle's `--density-input` option must
refuse it with a nonzero exit; the adversarial regression checks that
behavior under `python -O` as well.

The focused workflow runs the canonical regressions and requires native
output for the independent check. A standalone Python run without
`PSC_CYLINDER_NATIVE_OUTPUT` explicitly skips that comparison. Passing
calibration tests with such a skip is not a native parity result.

The local replay uses the existing minimal installation of the pinned Mojo
compiler and its matching `MODULAR_HOME`. The exact version and commands
are recorded in this packet. This is distinct from a fresh hosted locked
Pixi environment. Local and hosted results must be read separately.

## Recorded local replay

Locally executed source revision: `af5f3de12ec3be391a2ed9666b520fdd074dc494`.
Published source revision: `150b92c6c2699232a400360cd4dfc73f064bbc4d`.
Both have exactly the Git tree `9756cbfcd02b44b17891a466d72c3bbb929d5c1c`;
publication through the connected interface changed commit metadata only.
`source-publication.json` records this equality, and the manifest separately
pins all relevant source-file digests. The subsequent evidence commit
changes no executable source. The compiler reported
`Mojo 1.1.0.dev2026090805 (34562fa1)`.

| Check | Recorded result |
| --- | --- |
| Native complete-cylinder regression | Exit 0; scoped contract receipt reached |
| Native literal-density regression | Exit 0; scoped contract receipt reached |
| Native driver | Exit 0; complete 1,316-line certificate |
| Independent Python regression | 36 tests passed, zero skips; native packet required |
| Independent packet verifier | 1,002 occurrences, 283 slices and 18 pair bounds checked |
| Optimized-Python empty-density input | Expected exit 1, no stdout; strict-state-count refusal |
| Proof-bank generation check | 124 claims, 68 named Lean proofs, 355 source openings; unchanged |
| Claim governance | All six configured audits passed |
| Vendored synchronization | All pinned packages matched |
| Markdown integrity and diff whitespace | Passed |

The minimal local runtime printed a Crashpad-handler warning during native
execution. Its full stderr is retained. Each native process nevertheless
exited zero and reached its reported output or test contract; the warning
is not suppressed or counted as a separate verification result.

These are local results. This packet does not claim a hosted workflow pass.
The final commit and any hosted status are recorded separately in the pull
request; receipt hashes bind this replay to the executable source above.

## Scope of the mathematical result

Complete residue separation gives empty lifted intersections for pairs
0–2 and 1–2 in `1/021/001`. Other recorded values are finite **upper**
bounds from certified slice rectangles. A positive upper bound says
nothing about positivity of the true overlap.

For pair 0–1, the zero-prefix cylinder persists at every even depth.
The compact sets both contain the origin, while a literal strong
coincidence supplies a null-overlap conclusion through the separate
written bridge. The same-incidence word-order control checks that these
finite residue distinctions are not recoverable from a matrix alone.

In the fixed physical normalization, every strict factor has length at
least two, so a true pair density is at most 1/2. The covolume is less
than four. Thus equation (11) necessarily requires `U<2`. This is a
reproducible numerical obstruction for any emitted positive bound at
or above two; it does not rule out sharper enclosures.

No actual strict Pisot component is supplied. The finite density tests
use literal complete factorization and common-depth target coverage;
the genuine constant-length strict fixture is explicitly non-Pisot,
and the phase-sensitive matrix example is explicitly synthetic. Neither
is passed into the Pisot geometric layer.

## Review and validation boundaries

Separate automated reviews examined the source literature, the common-box
proof, complete residue separation, the fixed-coordinate covolume, the
all-column density bound, the necessary `U<2` screen and Python refusal
paths. The review wording and exact source scope are recorded with the
final validation results. Automated reviews are not independent human
mathematical review.

The general compact-space counting and measure proofs remain written
dependencies. These finite receipts do not machine-verify Corollary M3,
prove a uniform enclosure rate, establish a hypothetical strict component,
or close general C4, G1, BH, A1', PDS or PSC. No governed status or Lean
proof count is promoted by this contribution. The pull request is a
proposal for review; no merge is authorized by these receipts.
