# Diagonal residual exit: local proof and replay evidence

**Status:** local verification of scoped Lean components and finite exact
certificates, supporting a uniform written proof. Independent human review
and hosted acceptance remain separate. The complete uniform classification
and all-source composition are not yet one compiled Lean endpoint.

Base: `main@8bf2a627913bb7a9eb2f05b0ed3f08c54dc647d7`, inspected on
27 November 2026. This packet accompanies the
[written derivation](../../docs/bh-diagonal-residual-exit-2026-11-27.md) and
[literature decision](../../docs/bh-diagonal-residual-stop-go-2026-11-27.md).

## Mathematical and formal scopes

For `sigma=(1,01^r2,0^r1)`, `r>=12`, the written proof classifies the
nonaxis residual pairs without a one-step energy decrease into
`±(N-1,N)` and `±(N+2,-N)` when `r=3N`. Two admissible edges lower their
energy. Axis packets use one or three edges; unit packets have a separate
labelled exit. The prior outer descent and third-level entry supply the
written all-source composition.

| Component | What Lean checks | Explicit boundary |
| --- | --- | --- |
| `BHNearDiagonalLiteral` | Generic actual run occurrences and strict full-packet updates; existing off-diagonal endpoint preserved | Generic digit realization does not choose a terminating policy |
| `BHDiagonalLiteral` | Diagonal coefficient inequalities, actual digit steps, zero-pair cleanup, four-edge terminal excursion | The saturated packet leaves the central window; mixed-letter zero is intermediate |
| `BHDiagonalDescent` | Both exceptional two-edge paths and strict final energy decrease for every `r=3N`, `N>=4` | Does not classify arbitrary input pairs |
| `BHDiagonalAxis` | Every positive residual-axis packet reaches labelled zero or a central packet of smaller energy | Full-family sign/orientation assembly remains in the written proof |
| `BHDiagonalClassification` | Completed-square identities and exclusion of a nonzero integer congruence under explicit arithmetic bridge hypotheses | Those hypotheses are not yet assembled from every actual family packet |
| `BHDiagonalCertificate` | A checked finite rank contract lifts to actual paths for every permitted first coordinate | Certificate existence is a premise, and the target is the small box |

The combined audit checks 18 named endpoints and all 214 compiled declarations
in those six modules, including 161 theorem constants. Recursive axiom
closures contain only `propext`, `Classical.choice` and `Quot.sound`.
The count includes the retained off-diagonal module; it is not a count of
214 newly proved mathematical theorems.

The exact endpoint examples retain arbitrary first coordinates, selected
digit admissibility, source centrality, and all congruence bridge hypotheses.
Formal controls reject the old near-diagonal scalar-window contract on this
band, projected zero as full zero, centrality of the saturated packet, and
label equality at the mixed zero. An exact rational arithmetic model shows
why the integer congruence variable cannot be replaced by a real variable.

## Native exact replay

The canonical module builds the complete pair graph on `[-r,r]^2`, using
exact cubic signs. It then verifies shortest ranks and selected edges to
the old small box. A rank of `-1` records failure to reach the box **inside
this restricted square**; it is not a coincidence counterexample.

| r | Square states | Edges | Strict-disk pairs | Uncovered disk | Uncovered square | Maximum rank to box | Replayed full packets | Longest labelled path |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 12 | 625 | 1,061 | 437 | 0 | 56 | 24 | 1,311 | 45 |
| 13 | 729 | 1,257 | 517 | 0 | 56 | 27 | 1,551 | 47 |
| 15 | 961 | 1,689 | 697 | 0 | 86 | 29 | 2,091 | 55 |
| 16 | 1,089 | 1,933 | 793 | 0 | 86 | 32 | 2,379 | 59 |
| 18 | 1,369 | 2,461 | 1,005 | 0 | 120 | 34 | 3,015 | 61 |
| 20 | 1,681 | 3,057 | 1,245 | 0 | 148 | 40 | 3,735 | 75 |
| 32 | 4,225 | 7,969 | 3,205 | 0 | 376 | 62 | 9,615 | 113 |

The disk is `z^2+y^2<r^2`. Its 7,899 pairs each receive three full-packet
replays: a verified cancellation representative and the exact leftmost and
rightmost valid first coordinates. The 23,697 paths keep the original
occurrence ordinals and complete integral displacement. The canonical
residual module stops at the small box; the existing small-box regression
helper supplies the checked suffix to labelled coincidence. Complete paths
are replayed, not all serialized as transcripts in this packet.

A separate complete digit scan finds 106 failures of one-step energy
descent. Exactly 12 are nonaxis cases: four each for `r=12,15,18`. The
axis and exceptional blocks receive 792 additional original-occurrence edge
checks. These seven sampled parameters support the uniform written proof;
they are not its all-parameter warrant.

Caps are 10,000 square states, 30,000 edges and 10,000 edges in a selected
path. Exhaustion refuses a verdict. Sign evaluation reuses one certified
root interval per parameter and falls back to the existing exact evaluator
when that interval cannot separate zero. No floating-point predicate is
used. A separate generic sign cache checks the interval digit enumeration
against a full integer scan at `r=12`.

## Independent oracle and refusals

`oracles/python/bh_diagonal_residual.py` independently brackets the positive
cubic root with Python integers and rational bounds. It uses the direct
polynomial `y*beta^2+(t-r*y)*beta+r*z` for admissibility, reconstructs the
entire finite graph, and compares every native rank and selected edge.
It also checks the local-minimum classification and short energy descents
on the sampled disks. All 10,679 exported state records agree.

Its root precision starts at 96 binary digits; uncertain signs refine up to
a declared 768-digit cap and then refuse. It does not import the native
Sturm--Tarski evaluator. Four pytest controls check exact coefficient signs,
the resonant cases, forged ranks/digits, incomplete coverage, duplicate
exports and unsupported parameters.

Native controls additionally reject forged terminal or uncovered ranks,
incorrect edge counts, nonintegral packet encoding, invalid source windows,
out-of-run or shifted ordinals, changed first coordinates, false typed
endpoints and exhausted budgets. The old center `x=z-r*y` fails at the
residual pair `r=12,z=7,y=8`; the new replay uses a valid cancellation
representative and exact window extremes.

## Reproduction and source binding

Use the repository-pinned Lean and Mojo toolchains. Prepare the pinned Lake
dependencies and their cache in `proof/PscVerif`, and install pytest in the
Python environment. Then run from the repository root:

```sh
PSC_DIAGONAL_EVIDENCE_DIR=/tmp/psc-diagonal-review \
  tools/check_bh_diagonal_residual.sh
```

The output directory must be empty. The gate copies only project sources and
configuration into a fresh temporary workspace, validates dependency pins,
reuses the checked upstream package cache, and rebuilds the affected project
closure. It runs the combined audit, the literal audit and the existing
off-diagonal audit, then the native test/export, independent oracle and
oracle controls. Source hashes are compared before and after execution.
This is not a fresh rebuild of all Mathlib or the entire PSC library.

The complete isolated gate passed with exit status zero. All 284 focused
repository tests also passed (oracle controls, proof bank, Markdown links,
recorded-data integrity, claim governance and Markdown-source controls).
The final gate receipts are in `isolated/`. Its source binding lists project,
kernel, gate, oracle and test inputs. Tool versions are Lean `4.34.0-rc2`,
Mojo `1.1.0.dev2026090805`, and Python `3.12.14`.

Earlier frozen-source native and oracle receipts are also retained at this
packet's top level. `baseline-native-test.log` is an earlier five-parameter
run of the **new residual algorithm**, assembled from the observed stdout
chunks. It is not a main-branch regression baseline or final-source receipt.
The two `*-unavailable-time.log` files record attempts that failed before
Mojo started because `/usr/bin/time` was unavailable; successful reruns used
Bash's builtin `time`. Historical receipts are not overwritten.

`SHA256SUMS` pins this packet. General BH, residual A1-prime, general C4 and
PSC retain their existing status. No hosted acceptance or independent human
review is inferred from these local checks.
