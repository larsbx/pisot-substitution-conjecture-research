# D0 exact packet receipts

Base: #385 at 3f9d816ab7835f4be6c159453481d0d1d1eabd4d, still open.
Its hosted workflows remain queued on fresh inspection. Predecessor and
exact-head gates remain required before integration; no merge. Independent
R5/D5/class-C sibling results are not imported into registry counts.

Existing D0 and reversal U7 have complete stars of 2n-1 indexed children,
a 24-label chamber-wide image equal to B5, and selected completion <=8 after
every actual first choice. Their uniform two-edge source exits and all image
tails <=7 are reused; no companion star or uniform exit is new. Same surviving
stars as B5 do not identify their differently typed source rectangles.

Locked Mojo: 56 members / 82,096 pairs / 2,016 accepted / 224 source-path
edges / 11,266 all-child walk edges. Independent exact replay: 117 /
297,648 / 5,850 / 468 / 34,884 plus 9,880 full-image uniform-tail edges.
Both attain all24 labels and max walk eight. All99 native source/candidate/
image/old-E7-image rows agree independently. Fifty-nine scoped Python tests
pass across D0 and eight preceding packets. A further 152 integrity, link,
proof-bank and governance tests pass. No full local suite is claimed.

Replay from root:

```sh
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/tests/test_class_a_boundary_d0_children.mojo
pixi run --manifest-path kernel/pixi.toml --locked mojo run -I kernel kernel/class_a_boundary_d0_children.mojo
python oracles/python/class_a_boundary_d0_children.py > /tmp/d0.json
cmp /tmp/d0.json evidence/class-a-boundary-d0-2026-10-28/probe.json
python -c "import runpy,pathlib; o=runpy.run_path('oracles/python/class_a_boundary_d0_children.py'); verify=o['verify_native_registry']; verify(pathlib.Path('evidence/class-a-boundary-d0-2026-10-28/driver.log').read_text())"
python -m pytest -q tests/test_class_a_boundary_d0_children.py tests/test_class_a_boundary_e7_children.py tests/test_class_a_boundary_e6_children.py tests/test_class_a_boundary_b5_children.py tests/test_class_a_boundary_y4_children.py tests/test_class_a_boundary_r4_children.py tests/test_class_a_boundary_b4_children.py tests/test_class_a_boundary_b3_children.py tests/test_class_a_boundary_r3_children.py
python -m pytest -o addopts='' -q tests/test_recorded_data_integrity.py tests/test_markdown_links.py tests/test_check_markdown_source.py tests/test_proof_bank.py tests/test_claim_governance.py
./tools/verify_all.sh provenance
TLA_TOOLS=/path/to/tla2tools.jar ./proof/tla/check.sh
./tools/check_lean.sh
sha256sum -c evidence/class-a-boundary-d0-2026-10-28/source-sha256.txt
sha256sum -c evidence/class-a-boundary-d0-2026-10-28/SHA256SUMS
```

Finite implementation replay is separate from the companion universal
nine-kind guard proof. Independent sign refinement refuses at budget 512;
canonical machine arithmetic refuses overflow. All18 existing TLA expected
outcomes pass. Local Lean fails before compilation, earning no pass.
Preserve 124 governed claims, 34 named Lean proofs and 325 source openings.
No general E7 all-child, closed carrier, global BH or PSC conclusion.
