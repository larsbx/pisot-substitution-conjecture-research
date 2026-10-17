# Minus class-D boundary: complete symbolic template candidate

Status: independent exact-integer Python replay complete; canonical Mojo
execution NOT RUN LOCALLY. Human review pending and nonblocking. This packet
supports a complete scoped closure candidate, not a newly promoted theorem.

Domain: s=-1, b=0, p=3a+5, q=3a+6, r=2a+4, all integer a>=0.
The tail a>=4 is decided uniformly by quadratic coefficient signs at beta>14
and affine occurrence inequalities. Exact uncapped graphs cover a=0..3.
The symbolic graph has 145 vertices, 781 simple directed edges and maximum
half-depth 4. Depths 0,1,2,3,4 have populations 6,15,50,72,2 respectively.
Every listed vertex is reachable from the all-swap seeds. Every positive-depth
vertex has a child of depth one lower. Offset zero is not necessarily a
same-letter coincidence.

`oracle.json` contains the complete labels, seed indices, adjacency, minimum
depths and finite-prefix rows. Its two exact-field cross-checks at a=4,8
compare full labelled directed support; they are not the uniform argument.
The proof of the exhaustive candidate bound, actual run-index realization,
uniform signs and seed/child induction is in the family note section 4i.
The coordinate bound is mathematical; the separate 100-coordinate and
20,000-vertex resource caps refuse rather than truncate an answer.

Replay from repository root:

```sh
python3 oracles/python/class_d_boundary_template.py
python3 -m pytest tests/test_class_d_boundary_template.py
```

Canonical replay, still requiring a successful execution receipt:

```sh
cd kernel
mojo run -I . class_d_boundary_certificate.mojo
mojo run -I . tests/test_class_d_boundary_template.mojo
```

The standard kernel test runner discovers the new regression automatically.
Negative controls include a mixed coefficient sign, an affine sign that
changes later, a lowered threshold, an exhausted cap, and an edge deletion
that preserves every vertex. Existing theorem status and dependency ledgers
are unchanged. The conditional PDS/G1 assembly and remaining plus-boundary /
b>0 obligations are stated in section 4i and the existing proof ladder.

Baseline before this contribution: cb48214b08fb618959ae0c7c3728e69195e3ddee.
`source-digests.json` pins the new canonical code, oracle, regression sources,
mathematical note, and existing field/screen implementations used by the
replay. `SHA256SUMS` seals this packet. The two preceding class-D packets are
preserved byte-for-byte and keep their original source digests.
