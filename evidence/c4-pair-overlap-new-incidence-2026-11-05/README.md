# Twelve-source paired-overlap certificate: evidence and replay

**Scope:** a canonical Mojo finite certificate and independent exact oracle
for all twelve substitutions
`11/{012,021,102,120,201,210}/{01,10}`. The source class has incidence
`[[0,1,1],[2,1,1],[0,1,0]]` and characteristic polynomial
`x^3-x^2-3x-2`. The general measure proof is written mathematics,
not a claim of Lean formal verification. Independent human review is pending.

## What is certified

The complete graphs contain **43,915 states and 253,395 occurrence edges**.
All three zero-offset distinct-letter roots are included for every source.
The native implementation authenticates the common box `[-8,8]^2`, all
block-12 prefixes, exact quotient membership and six typed inverse-chart
carriers. The computed carrier capacity is **178,002 per source**;
the separate operational state cap is 20,000 per source and is never hit.

Each complete graph has positive integer weights satisfying
`20 sum_edges w_target <= 125 w_source`, while `beta^2>63/10>125/20`.
The actual maximum weight is 15,995; the accepted budget is 1,000,000.
Every minimum row gap is 125. Together with the
[exact measure equation](../../docs/c4-finite-overlap-carrier-2026-11-05.md),
these finite inequalities prove all **36** distinct-letter lifted overlap
measures are zero for this finite class. The same proof gives the finite
upper bound `256*w_i*(125/126)^3072<1/10`.

The [strict-cut bridge](../../docs/c4-nonunit-madic-counting-bridge-2026-11-04.md)
then excludes finite fully strict child-closed systems of irreducible
noncoincident balanced pairs at its stated hypotheses. No bound on the
number of their states or their phase period is added. No arbitrary-failure
extraction theorem, general C4, G1, BH, A1', SC, tiling, PDS or PSC promotion
is supplied.

## Inspectable artifacts

- [receipt.json](receipt.json) records all twelve sources, graph totals,
  rejection counts, weights, sweep counts and certificate SHA-256 digests.
- [native-packet.txt.gz](native-packet.txt.gz) preserves the **complete**
  canonical native packet: every model/carrier record, state, weight and
  repeated occurrence edge. It is deterministic gzip (`mtime=0`).
- The source proof is
  [the finite-carrier and exact-measure note](../../docs/c4-finite-overlap-carrier-2026-11-05.md).
- The pre-implementation
  [literature gate](../../docs/c4-finite-overlap-carrier-literature-gate-2026-11-05.md)
  records the primary-source hypothesis check and narrowed GO decision.
- Process logs, command receipts and source hashes are archived alongside
  these files in the replay commit. The manifest distinguishes the tested
  source tree from its evidence-only archival commit.

The uncompressed packet has **2,900,153 bytes** and SHA-256
`c69df761aacbe9d4b2689634627e7bc55ba167c9f5695ced8dde663c820e6754`.
Its gzip SHA-256 is
`cd79d0beb2b4acff7d6b46bce827411e54c415106d1aab068361c1d014105456`.
The oracle's complete record comparison checks more than either digest:
it independently reconstructs and checks every supplied record.

## Replay

From the repository root, with the locked kernel environment and pytest:

```bash
cd kernel
pixi run --locked mojo run -I . tests/test_c4_pair_overlap_new_incidence.mojo
pixi run --locked mojo run -I . c4_pair_overlap_new_incidence.mojo > /tmp/new-incidence-native.txt
cd ..
PSC_NEW_INCIDENCE_NATIVE_OUTPUT=/tmp/new-incidence-native.txt python -m pytest --assert=plain -o addopts='' -q tests/test_c4_pair_overlap_new_incidence_oracle.py
python oracles/python/c4_pair_overlap_new_incidence.py --native /tmp/new-incidence-native.txt
```

The archived packet can be checked independently of a fresh native build:

```bash
gzip -dc evidence/c4-pair-overlap-new-incidence-2026-11-05/native-packet.txt.gz > /tmp/archived-new-incidence.txt
python oracles/python/c4_pair_overlap_new_incidence.py --native /tmp/archived-new-incidence.txt
```

The workflow
[`.github/workflows/c4-pair-overlap-new-incidence.yml`](../../.github/workflows/c4-pair-overlap-new-incidence.yml)
checks out the exact PR head, asserts its SHA, installs the locked Pixi
environment, reruns native tests and the full packet, and requires complete
oracle parity. A queued workflow is not reported as a pass.

## Independence and refusal controls

Mojo is canonical. It uses checked exact arithmetic, an adjugate quotient
test, streamed source-prefix construction, a complete prefix-hull recursion
and sparse checked integer carrier keys. The Python oracle instead uses
Fraction Gaussian elimination, exact cubic-field stable powers and literal
block-12 digit enumeration (178,973 digits per source). A second test
reconstructs all graph rows from cofactors and rescanned literal prefixes,
with independent rational interval pruning. No strong-coincidence witness
or pre-existing coincidence result is consumed by either certificate.

Controls cover omitted repeated edges, relabelled states, false chart and
carrier data, uncertain geometric boundaries, zero/false weights,
non-strict rates, incomplete native packets, duplicate rows and unsupported
source indices. State, weight and iteration caps raise an inconclusive
result. The actual same-occurrence diagonal subgraph `M^2` refuses the
spurious subcritical conclusion. Euclidean-only measure scaling fails its
calibration; the compact Haar factor is essential.

The stronger rate `124/20` failed to produce bounded weights for source
indices 3 and 6 (`11/021/10` and `11/120/01`). These failures are preserved
as inconclusive and reproduced by regressions; they are not counterexamples
to null overlap. The rate `125/20` succeeds on all twelve.

## Review and execution status

Separate AI-agent source reviews found no blocking defect in the written
F0--F5 proofs, the typed-strip scope, exact multiplicity equation, native
complete-graph authentication, or the independent oracle's mathematical
core. One review independently executed all twelve oracle constructions.
These are source/algorithm reviews, not independent human review or
formal proof receipts. The fixed `1/10` arithmetic lemma applies to the
driver's authenticated default radii, rate and weight budget; it is not
advertised for arbitrary constructor parameters.

Local native regression and driver runs passed with pinned Mojo
`1.1.0.dev2026090805 (34562fa1)`. The available local compiler installation
is distinct from a fresh hosted locked-Pixi environment. Its existing
Crashpad-handler warning is retained in stderr; both processes exited zero.
The independent full-packet comparison and adversarial oracle tests passed.
The replay manifest records the final exact-tree results; hosted CI status
is reported separately in the pull request.
