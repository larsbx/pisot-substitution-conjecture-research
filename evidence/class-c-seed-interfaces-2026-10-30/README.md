# Nine-seed interface finite replay (2026-10-30)

Base source: d7bb85a9c96bf2ab526d3b41b5ce433a45256c4a (PR #404).
Local canonical toolchain: Mojo 1.1.0.dev2026090805 (34562fa1), the lock pin.
Independent oracle: standard-library Python 3, integer vectors and Fraction.

`receipt.json` records full-state agreement at 105 members / 945 seed
interfaces, 49,761 duplicate occurrence pairs collapsed, and all 2,131
parents of the fixed depth-four descendant experiment. `bounded-replay.txt`
records each frontier's counts. The complete deterministic export is
regenerated from source; its SHA-256 is in the receipt and CI uploads it.

Replay from kernel/:

    pixi run --locked mojo run -I . class_c_seed_interfaces.mojo dump > /tmp/class-c-seeds.txt

Then from repository root:

    python3 oracles/python/check_class_c_seed_interfaces.py --mojo-dump /tmp/class-c-seeds.txt --check-receipt evidence/class-c-seed-interfaces-2026-10-30/receipt.json

This packet is a bounded finite experiment. It is not a frozen graph,
forward-closed carrier, boundary-hitting certificate or PDS result.
The quantified first-generation proof is in
`docs/class-c-nine-seed-interfaces-2026-10-30.md`. Independent human review
remains pending. Hosted acceptance is recorded by the PR checks, not inferred
from these local receipts.
