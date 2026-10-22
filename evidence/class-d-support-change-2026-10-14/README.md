# Equal-count support-change countercalibration, 2026-10-14

Actual local independent Python replay on exactly two class-D minus-branch
members: a=2,3 and b=0, with 20,000 vertices per graph. Both graphs complete
uncapped. Their 145 integral-offset-labelled vertices are the same; two
specified directed support edges are absent at a=2 and present at a=3.
No graph-count or vertex-set plateau is a constant-support certificate.

Replay from repository root:

```sh
python3 oracles/python/class_d_boundary_probe.py --support
python3 -m pytest tests/test_class_d_boundary_probe.py
# With the locked canonical toolchain:
cd kernel && mojo run -I . class_d_boundary_probe.mojo
```

The Python inverse uses rational Gauss elimination and reconstruction in the
three-dimensional tile-length basis; canonical Mojo uses the existing exact
length_matrix/offset_vector. Mojo execution is NOT_RUN_LOCALLY; those checks
still await CI. No canonical receipt or universal mathematical promotion is
credited. These members still hit by depth four as in the original packet.
No failure of boundary hitting, uniform depth or eventual stabilization is
claimed. RNG: none; family exhaustion: false.

Baseline: repository commit 05ca23e44c0235ad9db17f085af76b0cbca5c098.
The original evidence/class-d-boundary-2026-10-14 packet is unchanged. Its
source digests describe its original run; this packet pins the revised source
bytes and this new comparison. Reproduce original source bytes from the pinned
git history when auditing that earlier run.
