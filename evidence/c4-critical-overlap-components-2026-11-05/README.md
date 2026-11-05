# Complete overlap SCC obstruction: evidence and replay

**Scope:** a canonical Mojo certificate for the complete twelve-source
graphs already supplied by PR #497, plus independent exact reconstruction.
The associated [CE1–CE6 proof note](../../docs/c4-critical-overlap-components-2026-11-05.md)
specializes the classical Frobenius–Victory theorem to the exact overlap
measure equation. Its written mathematical proof and geometric input are
separate from these finite executable checks. Independent human review
remains pending; no general C4, G1, BH, A1', SC, PDS or PSC status changes.

## Certified finite result

The sources are `11/{012,021,102,120,201,210}/{01,10}`. The exact threshold
is `theta=beta^2`, where `beta^3-beta^2-3beta-2=0`, and its authenticated
minimal polynomial is `g(t)=t^3-7t^2+5t-4`.

| Quantity | Result |
| --- | ---: |
| Source substitutions / distinct-letter roots | 12 / 36 |
| Complete states / repeated occurrence edges | 43,915 / 253,395 |
| Canonical strongly connected components | 40,793 |
| Singleton exclusions by cubic minimal degree | 40,765 |
| Larger blocks with nonsingular `g(A)` over `F_101` | 28 |
| Largest block / accepted block budget | 622 / 768 |
| Unresolved blocks at the accepted budget | 0 |
| Coordinates proved zero | 43,915 |

Every diagonal SCC block excludes eigenvalue `theta`. Since the complete
matrix is block triangular after the SCC permutation, it also excludes
`theta`; the only solution of `T v=theta v` is zero. Under the authenticated
measure equation, all 36 lifted cross-letter overlaps are null. The
preceding strict-cut bridge gives its same scoped exclusion of finite
fully strict child-closed noncoincident balanced-pair systems.

This is an alternative certificate for the existing finite source class.
It consumes neither the earlier global positive weights nor any local
spectral witness for these sources. It does not classify every block as
subcritical. The proof's separate supercritical and critical propagation
rules are tested on explicit controls where modular exclusion alone is
insufficient. Their stronger linear-system scope is not claimed as extra
Pisot-source coverage.

## Inspectable artifacts

- [receipt.json](receipt.json) records every source, component inventory,
  larger-block rank and determinant residue, root flag and digest.
- [native-packet.txt.gz](native-packet.txt.gz) contains the complete native
  export: every state, repeated row target, SCC member, condensation edge,
  modular attempt and zero flag. The gzip timestamp is fixed at zero.
- [review.md](review.md) records the independent AI source reviews and
  the repaired mutable-cache authentication defect.
- [runtime-install.json](runtime-install.json) records package SHA-256
  checks and the package-declared prefix relocations for the local runtime.
- Command receipts, process logs and a source manifest are added in the
  evidence archival commit after exact-revision replay.

The native packet has **210,252 lines / 6,346,587 bytes**, with SHA-256
`3d3681a85a5b4f1bc4cca5839c5fe2ac37a91ab50b9014e947b984d020a4037d`.
The independent verifier compares the entire reconstructed record stream;
digest equality is an additional integrity check, not its only test.

## Replay

From the repository root with the locked kernel environment and pytest:

```bash
cd kernel
pixi run --locked mojo run -I . tests/test_c4_overlap_scc_obstruction.mojo
pixi run --locked mojo run -I . c4_overlap_scc_obstruction.mojo > /tmp/overlap-scc-native.txt
cd ..
PSC_OVERLAP_SCC_NATIVE_OUTPUT=/tmp/overlap-scc-native.txt python -m pytest --assert=plain -o addopts='' -q tests/test_c4_overlap_scc_obstruction_oracle.py
python oracles/python/c4_overlap_scc_obstruction.py --native /tmp/overlap-scc-native.txt
```

For independent authentication of the preserved packet:

```bash
gzip -dc evidence/c4-critical-overlap-components-2026-11-05/native-packet.txt.gz > /tmp/archived-overlap-scc.txt
python oracles/python/c4_overlap_scc_obstruction.py --native /tmp/archived-overlap-scc.txt
```

The [dedicated workflow](../../.github/workflows/c4-overlap-scc-obstruction.yml)
checks out and asserts the exact PR head, installs the pinned locked Pixi
environment, runs the native regression and full driver, requires native
packet parity and exact receipt equality, and checks governance/generated
surfaces. It preserves the complete native output as an artifact. A queued
workflow is not a passed check.

## Independence, authentication and refusals

Mojo uses vendored iterative Tarjan, prime-field arithmetic, sparse Horner
evaluation directly from repeated occurrence rows, and row elimination.
Python uses iterative Kosaraju, integer matrix powers before reduction,
and row elimination on the transpose. Small actual blocks also receive
integer Bareiss determinant and permutation-expansion cross-checks.
The inherited source builder's independent exact chart and complete word
enumeration supply every actual state and edge; no old weight computation
is called.

Source/report authentication reconstructs the complete graph and component
data. Corrupt states, deleted multiplicities, split/merged partitions,
false ranks or determinants, wrong scale metadata and changed zero labels
are refused. Python caches immutable snapshots and serialized analyses;
returned mutable graphs and reports cannot change the expected reference.

The controls retain these distinctions:

- A noncritical block can carry positive mass forced by a critical child.
- A supercritical ancestor forces itself and descendants zero; a critical
  ancestor forces strict descendants zero while it can remain allowed.
- Deleting an incoming equation can enlarge the feasible cone.
- An algebraic eigenvalue need not be the Perron eigenvalue. Both rational
  and actual-cubic signed-eigenvector examples are retained.
- The actual diagonal block `M^2` has a checked positive critical vector
  and must remain allowed without an additional forcing equation.
- `g([1])=-5` is singular modulo 5, an inconclusive bad-prime attempt.
- A nonminimal annihilator cannot justify the degree shortcut.
- Source 0 at matrix cap 4 and source 3 at cap 512 remain unresolved;
  the previous weight proof is never a hidden fallback.
- Missing, extra or corrupted packet records and optimized-Python
  attempts to bypass acceptance are refused.

The declared budgets are 20,000 graph states, 81 row occurrences,
20,000,000 component-pair normalization scans, block size 768 and primes
`[101,103,107]`. At the accepted budget, all 28 non-singleton blocks succeed
at 101. Singleton degree exclusions apply whether or not a self-edge is
present.

## Execution boundary

The native regression and driver passed on pinned Mojo
`1.1.0.dev2026090805 (34562fa1)`. All 29 independent/adversarial Python
tests passed with the full native packet supplied. The existing Crashpad
warning is preserved in stderr; native processes exit zero and the test
reaches its final contract receipt.

The local runtime was restored from the exact two packages pinned by
`kernel/pixi.lock`, with archive hashes verified and only the package's
declared text-prefix relocations applied. It is a minimal local compiler
installation, distinct from the full fresh locked Pixi environment used
by hosted CI. Exact-source replay and live hosted status are reported
separately; no hosted result is inferred from local execution.
