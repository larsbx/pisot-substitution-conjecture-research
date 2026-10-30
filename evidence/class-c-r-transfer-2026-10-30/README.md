# R/T/U interfaces and translation control (2026-10-30)

Dependency: PR #406 at 5cdc00b3122ddd55d884ea143ab1a4a05d1e95fc.
Canonical compiler: Mojo 1.1.0.dev2026090805 (34562fa1), matching pixi.lock.
Independent oracle: standard-library Python integer/Fraction literal words.

`receipt.json` pins the finite d=7..64 replay: 174 interfaces, 870 children
counted per interface, 8,468 accepted occurrence pairs, 7,598 duplicates,
58 translated-star and strict-guard obstruction controls. The deterministic
export includes one rejected translated label at d=7. The hand proof in
`docs/class-c-r-transfer-2026-10-30.md` is quantified over all d>=7.

From kernel/:

    pixi run --locked mojo run -I . tests/test_class_c_r_transfer.mojo
    pixi run --locked mojo run -I . class_c_r_transfer.mojo dump > /tmp/class-c-r-transfer.txt

From repository root:

    python3 oracles/python/check_class_c_r_transfer.py --mojo-dump /tmp/class-c-r-transfer.txt --check-receipt evidence/class-c-r-transfer-2026-10-30/receipt.json

The workflow also reproduces both predecessor exports and checks their
unchanged committed receipts before uploading all artifacts. This packet
supplies no closed carrier or BH certificate. The rejected translation is
an invalid overlap, not a realized counterexample to BH/PDS/PSC. Local
replay is not hosted acceptance; independent human review remains pending.

The indexed continuation A_K=(x,c,[-1,3,-K]), 0<=K<=d, is proved in
`docs/class-c-indexed-transfer-2026-10-30.md`. `indexed-receipt.json` records
357 representative formal-parent interfaces over the same 58 gaps, 3,686
child records, 25,213 accepted pairs and 21,527 duplicates. Only A_0 and
A_4 have recorded uniform seed paths. K=d has twelve children, while all
interior indices have ten; both sides have 2d+1 occurrence pairs.

From kernel/:

    pixi run --locked mojo run -I . tests/test_class_c_indexed_transfer.mojo
    pixi run --locked mojo run -I . class_c_indexed_transfer.mojo dump > /tmp/class-c-indexed-transfer.txt

From repository root:

    python3 oracles/python/check_class_c_indexed_transfer.py --mojo-dump /tmp/class-c-indexed-transfer.txt --check-receipt evidence/class-c-r-transfer-2026-10-30/indexed-receipt.json
