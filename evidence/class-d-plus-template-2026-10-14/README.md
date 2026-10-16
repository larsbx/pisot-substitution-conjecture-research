# Plus class-D boundary: complete symbolic template candidate

Status: independent exact-integer Python replay complete; canonical Mojo
execution NOT RUN LOCALLY. Human review pending and nonblocking. No theorem
status or dependency is promoted by this packet.

Domain: s=+1, b=0, p=3a+3, q=3a+2, r=2a, every integer a>=0.
The tail a>=7 is certified by quadratic coefficient signs at beta>17 and
affine run-position inequalities. All nine segment pairs and a proved
finite third-coordinate bound exhaust the child graph. Exact uncapped
field graphs cover a=0..6, including the empty run at zero.

The complete symbolic graph has 718 vertices and 4,326 simple directed
edges. Minimum half-depths 0..6 have populations 6,27,102,243,196,136,8.
Every vertex is seed-reachable and has an offset-zero descendant within
six steps. Every finite-prefix member also has maximum half-depth six.
Full labelled directed support agrees with independent field graphs at
seven and eight; this cross-check is not the uniform argument.

`oracle.json` contains every vertex, seed index, adjacency row, depth and
finite-prefix row. The soundness argument, Perron length derivation,
root bound and conditional PDS/G1 assembly are in the existing family note
sections 4i/4j. Both branches share the canonical engine; its minus default
must still replay the original 145/781 packet unchanged.

Replay from repository root:

```sh
python3 oracles/python/class_d_boundary_template.py --plus
python3 -m pytest tests/test_class_d_plus_template.py tests/test_class_d_boundary_template.py
```

Canonical commands (execution receipt still pending):

```sh
cd kernel
mojo run -I . class_d_plus_boundary_certificate.mojo
mojo run -I . tests/test_class_d_plus_template.mojo
mojo run -I . tests/test_class_d_boundary_template.mojo
```

The standard kernel runner automatically discovers both regressions. They
reject the wrong branch, empty-run tail, unsupported lower threshold,
future affine sign change, exhausted state cap, and a deleted edge despite
identical vertices. Coordinate/state caps refuse rather than truncate.

Baseline: 38b87af7697c07641995e2ffe3be2b4cef275ded; reconciled main b9fbb32.
`sources.json.gz` is deterministic gzip-compressed JSON: a `sources` map
from paths to exact UTF-8 source contents, plus a `base_commit` locator.
`source-digests.json` pins each archived source; `SHA256SUMS` seals all packet
files. Verification works in shallow clones and permits later source edits
without changing historical evidence. All three earlier class-D packets
remain byte-for-byte unchanged. The two b>0 interiors and general PSC/G1
remain open.
