# Class-D target-aware cover and descending paths — 2026-10-14

Base: PR #263 at `cb48214b08fb618959ae0c7c3728e69195e3ddee`.
Both earlier class-D packets remain unchanged.

`certificate.json` is a proposed 145-state table for the minus `b=0`, `a>=2`
line. Each row contains an integral offset, rank, successor row and affine
whole-image occurrence indices. `parametric-oracle.json` records actual local
verification of universal polynomial and affine obligations: positive interior
geometry, nine swap-seed occurrences, complete child closure (18,779 candidate
integers), and rank descent with maximum four. This is stronger than bounded
sampling, but the executing implementation is an independent Python oracle.
**The family result remains conditional pending canonical Mojo replay.**

`finite-oracle.json` separately records exact field-graph comparisons for
minus `a=2..8` and plus `a=4..8`, cap 20,000 per graph, no RNG, all completed
uncapped. Minus graphs have a common 779-edge lower graph on 145 labels; every
label hits by rank four even though 486 edges from positive ranks do not
descend. Plus sizes are 746,726,718,718,718 with half-depth six. These data
alone exhaust neither infinite branch. The positive branch remains open.

The mathematical proof of the checker contract, parametric length formulas,
negative controls and conditional corollary are in the existing family note
`docs/p1b-boundary-hitting-progress-2026-10-08.md` §4i. The table was proposed
from exact bounded graphs, then its infinite-domain obligations were checked
separately; fitting alone has no authority. In particular, a proposed index
`9-a` passes `a=2..8` yet fails later, and the parametric checker rejects it.

Reproduce from the repository root:

```sh
python oracles/python/class_d_minus_certificate.py
python oracles/python/class_d_target_spine_probe.py
python -m pytest -q tests/test_class_d_minus_certificate.py
```

Canonical replay (NOT RUN LOCALLY): a local pixi installation was attempted;
`pixi install --locked` failed fetching the pinned conda-forge protobuf package
with a tunnel error. The locked Mojo environment is unavailable.

```sh
cd kernel
mojo run -I . class_d_minus_certificate.mojo
mojo run -I . tests/test_class_d_minus_certificate.mojo
mojo run -I . class_d_hitting_spine.mojo
```

The full-line driver separately checks `a=0,1` using the existing exact all-seed
graph machinery. The algebraic tail checker never substitutes a finite sample
for a universal inequality. A canonical failure blocks acceptance even when
the oracle succeeds. Human review remains pending and nonblocking; no PSC,
G1, PDS or whole-class claim status is promoted by this packet.

`source-digests.json` pins the source bytes used for the oracle runs and the
unexecuted canonical companions. `SHA256SUMS` pins every packet file.
