# Upper plus-Class-A central completion: local evidence

Date: November 23, 2026. This packet records local, unpublished proof work.
The [derivation and scope](../../docs/class-a-plus-upper-central-completion-2026-11-23.md)
state the theorem; `acceptance.json` records the final combined check result.

**Local acceptance passed:** 33 project modules rebuilt from an empty project
artifact tree, all six audit fixtures passed, all 349 source bindings were
rechecked, and 266 focused proof-bank/data-integrity tests passed.
The canonical executable and independent exact replay also passed.

## Revision binding

| Revision | Identity |
| --- | --- |
| Published merge baseline | `7bfcd8c15e845f148b3c0ee405ca839ae6039e2d` |
| Source-equivalent accepted baseline | `1bdaa34c63e6de97a0f17998c4f06887a18f099c` |
| Prior local entry review checkpoint | `5b8bd353f1934e67b8fbac518a9737eb7abf127d` |
| New local proof commit | `7c939df6f87b2636d2ab8d71f45dcf7df60d6071` |
| New local proof tree | `65c89c4adff9cf1bbb2113f9bd9fd0256f3ddb20` |
| Complete project source snapshot | 349 files |
| Snapshot SHA-256 | `8d1aaa3665ee341c5ea15a244198735290d18b20e85dc3acf21e6af9c8dd8222` |

`revision-binding.json` verifies every project source/configuration hash and
both gate/helper hashes against the new proof commit. The evidence commit
adds receipts without changing those tested proof sources. No hosted run
or publication was requested for this local candidate.

## Work shown

### Assumptions and hypotheses

The exact theorem scope is the literal plus words `x y^(n+d) x`, `c y^n x`,
`x y^(n+1) c`, with `n>=7,n+5<=d<=2n+11`. The strongest endpoint constructs
a bracketed cubic root and positive literal eigenlengths and then quantifies
over every strict full-integral typed packet. Central entry, literal
recurrence, bounded tail classification and signed cycle exit are proved
dependencies, not additional caller premises.

### Derivation / reduction

The proof constructs actual indexed central RUN edges, extracts the scalar
recurrence from the same complete packets, finds a repeated pair before
`(2B+1)^2`, and reconstructs the full signed cycle one step later. The
existing original-occurrence cycle exit then reaches typed zero. Entry
and central paths meet at the identical complete packet. Both original
marked tracks are recomposed over the entire concatenation.

The central bound is `(2B+1)^2+2n-1`, with
`B=(n+7)(|p|+|2p+q+r|+1)`. For arbitrary strict sources the bound is the
least-power entry budget `k+1` plus the central budget evaluated at the
actual reached central packet. The final identity is
`M^t*(-source.delta)=P_t-Q_t`, with actual original `MarkTrace` witnesses.

### Evidence and replay

Run the fresh-project gate from the root with pinned Lean/Lake on `PATH`:

```sh
PSC_CENTRAL_EVIDENCE_DIR=/tmp/psc-upper-central-fresh \
  tools/check_class_a_plus_upper_central_completion.sh
```

The gate verifies exact dependency pins and upstream source bytes before
and after, copies all project sources into a fresh workspace, refuses a
pre-existing project build directory, and rebuilds the local closure.
Only manifest-pinned upstream packages are cached; an alternate directory
may be specified with `PSC_CENTRAL_PACKAGES`. This does not claim to
rebuild all Mathlib artifacts.

The six fixtures cover the new completion, existing literal entry, y/c
two-edge controls, arithmetic entry, upper recurrence, and complete signed
cycle exits. The new fixture reports four owned modules, 127 declarations,
95 compiled theorem declarations, 13 independent expanded endpoint types
and 44 contract refusals. Generated auxiliary proofs are included in 95;
the source inventory adds 51 named proofs, from 6,969 to 7,020. Recursive
axioms are restricted to `propext`, `Classical.choice`, and `Quot.sound`.
New modules are warning-free; inherited lint warnings remain in raw logs.

The first isolated attempt is retained in `initial-isolated-attempt/`.
Its new proof chain and audit passed, then the next fixture refused a
missing entry-control object file. The gate had omitted the explicit
build target for the existing `ClassAPlusUpperEntryControls` module.
The corrected script adds that target and repeats the whole clean run.
`gate.sh` reproduces the first attempt's exact source hash, and its exit 1
is preserved rather than counted as complete acceptance.

The fresh canonical Mojo and independent oracle replay cover 818 central
sources and 4,728 edges, including 1,806 nearest steps. All 818 full records
agree. Maximum observed depths are 62 nearest and 93 total; the largest
composed prefix coordinate has 144 digits. These are finite measurements.

| Receipt | Result |
| --- | ---: |
| Native negative controls | 28 |
| Rejected independent transcript mutations | 15 |
| Explicit resource refusals | 3 |
| Focused Python regressions | 80 passed |
| Pair-count and full central bounds | Checked on 818 paths |
| Exact signed-cycle depth formula | Checked on 818 paths |
| Complete reversal | 818 sources and 4,728 edges |

The grid uses `n in {7,8,12,31}`, `J in {1,2,3,4,5,n+7}`, exactly central
`p,q in -2..2`, every admissible signed cycle height, and the two larger
pairs `(100,-83),(-100,83)`. Exact root refinement, word allocation and
path caps are 256, 50,000 and 256. `central-review-summary.json` preserves
runtime versions, commands, source hashes and output hashes;
`central-review-summary.md` gives the independent review. Their finite
central-replay scope and `all_source_entry:false` fields describe those
executions, separately from the new universal-within-family Lean theorem.

Raw streams use deterministic gzip (`mtime=0`); decompressed bytes are
unchanged. The native stdout SHA-256 is
`65acc78ac1e03747c254a2feb86fd1915d6941a67b99beffff7018130af2c3a6`,
matching the original documented native transcript. The independent JSONL
SHA-256 is `125a6720fe751493bc5c02a48861d93eb5a898699cec1a156fae063a4dd13698`.
These are different encodings. The verbatim summaries and independent
manifest name uncompressed artifacts; decompress before checking those
recorded hashes.

From the repository root, using fresh output paths:

```sh
mkdir -p /tmp/psc-upper-central-replay
gzip -dc evidence/class-a-plus-upper-central-completion-2026-11-23/central-native.txt.gz \
  > /tmp/psc-upper-central-replay/native.txt
gzip -dc evidence/class-a-plus-upper-central-completion-2026-11-23/independent/exact-transcripts.jsonl.gz \
  > /tmp/psc-upper-central-replay/exact-transcripts.jsonl
python3 oracles/python/class_a_plus_upper_recurrence.py \
  --native /tmp/psc-upper-central-replay/native.txt
python3 evidence/class-a-plus-upper-central-completion-2026-11-23/verify-central-extra-controls.py \
  --root . --native /tmp/psc-upper-central-replay/native.txt \
  --transcripts /tmp/psc-upper-central-replay/exact-transcripts.jsonl \
  --output /tmp/psc-upper-central-replay/extra-controls.json
python3 oracles/python/class_a_plus_upper_recurrence_independent.py \
  --output-dir /tmp/psc-upper-central-independent-fresh
PSC_UPPER_CENTRAL_NATIVE=/tmp/psc-upper-central-replay/native.txt \
  python3 -m pytest tests/test_class_a_plus_upper_recurrence.py \
  tests/test_class_a_plus_upper_recurrence_independent.py -q
```

To regenerate the canonical stream, run within `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_class_a_plus_upper_recurrence.mojo --emit
```

### Negative controls

The actual nearest selector at `n=7,J=1` cycles `W_4 -> -W_4 -> W_4`.
A productive alternative exit reaches zero in seven edges. Boundedness
and periodicity therefore are not treated as a zero hit.

For every `Family n 1 beta`, the new Lean control proves that central
`yy(1,2,-5)` has transformed initial pair `(1,1)` but is not any complete
`W` packet. Its actual `(1,1)` edge reaches `yy(-1,-3,6)`; premature
reconstruction is rejected by independent replay too.

Both initial coordinates are necessary: at `n=7,J=1`, central
`yy(0,1000,-917)` selects `(4,1)` and reaches central `yy(83,83,-339)`.
The full reserve is 1,176; a first-coordinate-only reserve would be 14
and is already exceeded after one edge.

The synthetic half tie still fails strict rounding. The literal family
uses cubic exclusion instead. The existing y/c `(0,1,0)` theorem is
freshly recompiled and still requires `(n+2,0)` then `(1,2)`. No reversal
is counted as an edge and no LAST `c` is accepted as RUN `y`.

The replay also rejects wrong parameters/types, altered full offsets,
illegal indices, false local prefixes, noncomposable joins, incomplete
paths and continuation beyond its first zero/cycle cutoff. The Lean
existence theorem does not promise that earliest-cutoff policy.

### Non-claims / remaining gaps

Literal entry-to-central-to-zero is closed in Lean at the displayed
parameter and strict integral source scope. Universal BH, residual
A1-prime, general C4, unrelated family bindings and new spectral
conclusions remain separate. Smaller upper members retain their finite
swap-seed scope. Governed claim statuses are unchanged. These local
checks do not establish hosted acceptance, a whole-repository clean build
or independent human review. No modifications have been published.
